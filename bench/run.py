#!/usr/bin/env python3
"""Compare Lithe against solc on equivalent contracts.

For each `bench/<name>.lithe` and `bench/<name>.sol`, report runtime bytecode size
for Lithe and three solc configurations. Then deploy all of them to a local anvil,
replay the same transactions against each, check that statuses, return data, logs,
and every storage slot agree, and report gas. Lithe lays out storage like Solidity,
so the raw slots must match exactly.

Needs `anvil` and `cast` (Foundry) and solc. `SOLC` overrides the solc binary.
Run from the repository root: `python3 bench/run.py [name ...]`.
"""

import binascii
import gzip
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "bench")
LITHE = os.path.join(ROOT, "target", "release", "lithe")
RPC = "http://127.0.0.1:8599"
# anvil's first two default accounts.
KEYS = {
    "A": "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80",
    "B": "0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d",
}
ADDR = {
    "A": "0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266",
    "B": "0x70997970C51812dC3A010C7d01b50e0d17dc79C8",
}
SOLC_BUILDS = {
    "solc ir r1": ["--optimize", "--optimize-runs", "1", "--via-ir"],
    "solc ir r200": ["--optimize", "--optimize-runs", "200", "--via-ir"],
    "solc r200": ["--optimize", "--optimize-runs", "200"],
}
LONG = "a string that is well past thirty one bytes long"


def word(n):
    return format(n, "064x")


def raw(sig, *words):
    """Hand-built calldata: a selector, then words as given, well-formed or not."""
    sel = subprocess.run(["cast", "sig", sig], capture_output=True, text=True).stdout.strip()
    return sel + "".join(words)

# (kind, sender, signature, args, value): kind is "send" or "call". Each targets the
# contract its scenario is named after. `SUITES` below deploy several contracts by role.
SCENARIOS = {
    "counter": [
        ("send", "A", "increment(uint256)", ["5"], None),
        ("send", "B", "increment(uint256)", ["0"], None),
        ("send", "B", "increment(uint256)", ["7"], None),
        ("send", "B", "reset()", [], None),
        ("call", "A", "get_count()", [], None),
        ("send", "A", "reset()", [], None),
        ("call", "A", "get_count()", [], None),
    ],
    "token": [
        ("send", "A", "mint(address,uint256)", [ADDR["A"], "1000"], None),
        ("send", "A", "mint(address,uint256)", [ADDR["B"], "50"], None),
        ("send", "A", "transfer(address,uint256)", [ADDR["B"], "100"], None),
        ("send", "B", "transfer(address,uint256)", [ADDR["A"], "999"], None),
        ("send", "B", "mint(address,uint256)", [ADDR["B"], "1"], None),
        ("send", "B", "transfer(address,uint256)", [ADDR["A"], "150"], None),
        # Calldata shorter than the arguments reverts; extra bytes after them are fine.
        ("send", "A", raw("transfer(address,uint256)", word(int(ADDR["B"], 16))), [], None),
        ("send", "A", raw("transfer(address,uint256)", word(int(ADDR["B"], 16)), word(1), word(9)), [], None),
        ("send", "A", raw("mint(address,uint256)", word(1 << 160), word(1)), [], None),
        ("call", "A", "balance_of(address)", [ADDR["A"]], None),
        ("call", "A", "total_supply()", [], None),
    ],
    "vault": [
        ("send", "A", "deposit()", [], "1ether"),
        ("send", "B", "deposit()", [], "0.5ether"),
        ("send", "A", "withdraw(uint256)", ["300000000000000000"], None),
        ("send", "B", "withdraw(uint256)", ["5000000000000000000"], None),
        ("send", "B", "set_paused(bool)", ["true"], None),
        ("send", "A", "set_paused(bool)", ["true"], None),
        ("send", "A", "deposit()", [], "1"),
        ("send", "A", "set_paused(bool)", ["false"], None),
        ("send", "A", "withdraw(uint256)", ["100"], "1"),
        ("call", "A", "deposit_of(address)", [ADDR["A"]], None),
    ],
    "math": [
        ("call", "A", "mul_div(uint256,uint256,uint256)", ["10", "20", "3"], None),
        ("call", "A", "mul_div(uint256,uint256,uint256)", ["1", "2", "0"], None),
        ("call", "A", "average(uint256,uint256)", ["7", "9"], None),
        ("call", "A", "distance(int256,int256)", ["-5", "3"], None),
        ("call", "A", "narrow(uint256)", ["255"], None),
        ("call", "A", "narrow(uint256)", ["256"], None),
        ("call", "A", "mix(uint32,uint32)", ["10", "20"], None),
        ("call", "A", "mix(uint32,uint32)", ["4000000000", "4000000000"], None),
        ("send", "A", "store(uint256,uint256)", ["12", "5"], None),
    ],
    "layout": [
        ("send", "A", "set_level(uint256,uint8)", ["0", "11"], None),
        ("send", "A", "set_level(uint256,uint8)", ["31", "22"], None),
        ("send", "A", "set_level(uint256,uint8)", ["32", "33"], None),
        ("send", "A", "set_level(uint256,uint8)", ["39", "255"], None),
        ("send", "A", "set_level(uint256,uint8)", ["40", "1"], None),
        ("call", "A", "level(uint256)", ["31"], None),
        ("call", "A", "level(uint256)", ["32"], None),
        ("send", "A", "set_flag(uint256,bool)", ["4", "true"], None),
        ("send", "A", "set_flag(uint256,bool)", ["0", "true"], None),
        ("call", "A", "flag(uint256)", ["4"], None),
        ("send", "A", "set_delta(uint256,int16)", ["1", "-300"], None),
        ("send", "A", "set_delta(uint256,int16)", ["2", "7"], None),
        ("call", "A", "delta(uint256)", ["1"], None),
        ("call", "A", "delta(uint256)", ["0"], None),
        ("send", "A", "place(uint16,uint16)", ["65535", "3"], None),
        ("call", "A", "spot()", [], None),
        ("send", "A", "set_pair(uint32,address)", ["4000000000", ADDR["B"]], None),
        ("call", "A", "pair()", [], None),
        ("send", "A", "bump(uint64)", ["18000000000000000000"], None),
        ("send", "A", "bump(uint64)", ["5"], None),
        ("call", "A", "small()", [], None),
    ],
    "records": [
        ("send", "A", "place(uint256,uint256,uint32,int16)", ["1", "1000", "4000000000", "-300"], None),
        ("send", "B", "place(uint256,uint256,uint32,int16)", ["2", str(2**255), "5", "32767"], None),
        ("call", "A", "order_of(uint256)", ["1"], None),
        ("send", "A", "bump(uint256,uint256)", ["1", "5"], None),
        ("send", "A", "bump(uint256,uint256)", ["9", "5"], None),
        ("send", "A", "bump(uint256,uint256)", ["2", str(2**255)], None),
        ("send", "A", "place(uint256,uint256,uint32,int16)", ["3", "1", "1", "-32768"], None),
        ("send", "A", "bump(uint256,uint256)", ["3", "1"], None),
        ("send", "A", "copy(uint256,uint256)", ["1", "4"], None),
        ("send", "A", "copy(uint256,uint256)", ["4", "4"], None),
        ("call", "A", "order_of(uint256)", ["4"], None),
        ("call", "A", "status_of(uint256)", ["1"], None),
        ("call", "A", "delta_of(uint256)", ["1"], None),
        ("send", "A", "pair_set(uint256,uint128,uint128)", ["7", str(2**128 - 1), "3"], None),
        ("send", "B", "pair_set(uint256,uint128,uint128)", ["7", "1", str(2**127)], None),
        ("send", "A", "pair_set(uint256,uint128,uint128)", ["8", "2", "9"], None),
        ("call", "A", "pair_of(address,uint256)", [ADDR["A"], "8"], None),
        ("call", "A", "pair_of(address,uint256)", [ADDR["B"], "8"], None),
    ],
    "lists": [
        ("send", "A", "save(uint256[])", ["[1,2,3]"], None),
        ("call", "A", "saved()", [], None),
        ("send", "A", "push(uint256)", ["4"], None),
        ("send", "A", "save(uint256[])", ["[9]"], None),
        ("call", "A", "saved()", [], None),
        ("send", "A", "save(uint256[])", ["[]"], None),
        ("send", "A", "set_owners(address[])", ["[" + ADDR["A"] + "," + ADDR["B"] + "]"], None),
        ("call", "A", "owners()", [], None),
        ("call", "A", "owner_at(uint256)", ["1"], None),
        ("call", "A", "owner_at(uint256)", ["2"], None),
        ("call", "A", "first(uint256[])", ["[7,8]"], None),
        ("call", "A", "first(uint256[])", ["[]"], None),
        ("call", "A", "echo(bytes4[])", ["[0xdeadbeef,0x01020304]"], None),
        ("call", "A", "pair(uint256,uint256)", ["5", "6"], None),
        ("send", "A", "announce(uint256[],string)", ["[1,2]", LONG], None),
        ("send", "A", "tag(bytes4[])", ["[0xdeadbeef,0x01020304]"], None),
        ("call", "A", "same(uint256[],uint256[])", ["[1,2]", "[1,2]"], None),
        ("call", "A", "same(uint256[],uint256[])", ["[1,2]", "[1,3]"], None),
        ("call", "A", "encoded(uint256[],bytes4)", ["[1,2]", "0xcafebabe"], None),
        # An offset past the data, a length past the data, and an address with high bits set.
        ("send", "A", raw("save(uint256[])", word(0x1000)), [], None),
        ("send", "A", raw("save(uint256[])", word(0x20), word(3), word(1)), [], None),
        ("send", "A", raw("set_owners(address[])", word(0x20), word(1), word(1 << 160)), [], None),
    ],
    "loops": [
        ("call", "A", "sum(uint256[])", ["[1,2,3,4,5]"], None),
        ("call", "A", "sum(uint256[])", ["[]"], None),
        ("send", "A", "airdrop(address[],uint256)", ["[" + ADDR["A"] + "," + ADDR["B"] + "," + ADDR["A"] + "]", "7"], None),
        ("call", "A", "balance_of(address)", [ADDR["A"]], None),
        ("send", "A", "join(address)", [ADDR["A"]], None),
        ("send", "A", "join(address)", [ADDR["B"]], None),
        ("send", "A", "join(address)", ["0x0000000000000000000000000000000000000003"], None),
        ("send", "A", "mark_all()", [], None),
        ("call", "A", "is_owner(address)", [ADDR["B"]], None),
        ("call", "A", "find(address)", [ADDR["B"]], None),
        ("call", "A", "find(address)", ["0x0000000000000000000000000000000000000009"], None),
        ("call", "A", "gcd(uint256,uint256)", ["1071", "462"], None),
        ("call", "A", "gcd(uint256,uint256)", ["7", "0"], None),
        ("call", "A", "hash_chain(bytes32,uint256)", ["0x" + "11" * 32, "20"], None),
        ("send", "A", "payout(address[])", ["[" + ADDR["B"] + ",0x0000000000000000000000000000000000000003]"], "1ether"),
        ("send", "A", "payout(address[])", ["[]"], "1"),
    ],
    "registry": [
        ("send", "A", "rename(string)", ["hello"], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "rename(string)", [LONG], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "set_blob(bytes)", ["0x" + "ab" * 70], None),
        ("call", "A", "blob()", [], None),
        ("call", "A", "digest()", [], None),
        ("send", "A", "set_tag(bytes4,uint8)", ["0xdeadbeef", "7"], None),
        ("call", "A", "tag()", [], None),
        ("call", "A", "level()", [], None),
        ("send", "B", "set_tag(bytes4,uint8)", ["0x01020304", "255"], None),
        ("call", "A", "tag()", [], None),
        # A string whose offset or length points past the end of calldata reverts.
        ("send", "A", raw("rename(string)", word(0x1000)), [], None),
        ("send", "A", raw("rename(string)", word(0x20), word(0x40), "68656c6c6f" + "00" * 27), [], None),
        ("send", "A", raw("rename(string)", word(0x20), word(5), "68656c6c6f" + "00" * 27), [], None),
        # Shrinking a stored value must clear the data slots it no longer uses.
        ("send", "A", "rename(string)", [LONG * 3], None),
        ("send", "A", "rename(string)", [LONG], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "rename(string)", ["hi"], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "set_blob(bytes)", ["0x" + "cd" * 40], None),
        ("send", "A", "set_blob(bytes)", ["0x" + "ef" * 5], None),
        ("call", "A", "blob()", [], None),
    ],
}


E18 = 10**18
MAX = str(2**256 - 1)
ZERO = "0x0000000000000000000000000000000000000000"


def erc20_steps(t):
    """OpenZeppelin's token behaviors, errors included, against role `t`."""
    return [
        ("call", "A", t, "name()", [], None),
        ("call", "A", t, "symbol()", [], None),
        ("call", "A", t, "decimals()", [], None),
        ("call", "A", t, "owner()", [], None),
        ("send", "A", t, "mint(address,uint256)", [ADDR["A"], str(1000 * E18)], None),
        ("send", "B", t, "mint(address,uint256)", [ADDR["B"], "5"], None),
        ("send", "A", t, "mint(address,uint256)", [ZERO, "1"], None),
        ("send", "A", t, "transfer(address,uint256)", [ADDR["B"], str(100 * E18)], None),
        ("call", "A", t, "transfer(address,uint256)", [ADDR["B"], "1"], None),
        ("send", "A", t, "transfer(address,uint256)", [ZERO, "1"], None),
        ("send", "B", t, "transfer(address,uint256)", [ADDR["A"], str(10**30)], None),
        ("send", "A", t, "approve(address,uint256)", [ADDR["B"], str(500 * E18)], None),
        ("send", "A", t, "approve(address,uint256)", [ZERO, "1"], None),
        ("call", "A", t, "allowance(address,address)", [ADDR["A"], ADDR["B"]], None),
        ("send", "B", t, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], str(200 * E18)], None),
        ("send", "B", t, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], str(400 * E18)], None),
        ("send", "B", t, "transferFrom(address,address,uint256)", [ADDR["A"], ZERO, "1"], None),
        ("send", "A", t, "approve(address,uint256)", [ADDR["B"], MAX], None),
        ("send", "B", t, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "1"], None),
        ("call", "A", t, "allowance(address,address)", [ADDR["A"], ADDR["B"]], None),
        ("send", "B", t, "burn(uint256)", [str(10 * E18)], None),
        ("send", "B", t, "burn(uint256)", [str(10**30)], None),
        ("send", "B", t, "burnFrom(address,uint256)", [ADDR["A"], str(5 * E18)], None),
        ("send", "A", t, "burnFrom(address,uint256)", [ADDR["B"], "1"], None),
        ("send", "B", t, "pause()", [], None),
        ("send", "A", t, "pause()", [], None),
        ("send", "A", t, "pause()", [], None),
        ("call", "A", t, "paused()", [], None),
        ("send", "A", t, "transfer(address,uint256)", [ADDR["B"], "1"], None),
        # Checked before the pause: the receiver.
        ("send", "A", t, "transfer(address,uint256)", [ZERO, "1"], None),
        ("send", "A", t, "mint(address,uint256)", [ADDR["A"], "1"], None),
        ("send", "A", t, "approve(address,uint256)", [ADDR["B"], "7"], None),
        ("send", "A", t, "unpause()", [], None),
        ("send", "A", t, "unpause()", [], None),
        ("send", "A", t, "transferOwnership(address)", [ZERO], None),
        ("send", "A", t, "transferOwnership(address)", [ADDR["B"]], None),
        ("send", "A", t, "mint(address,uint256)", [ADDR["A"], "1"], None),
        ("send", "B", t, "renounceOwnership()", [], None),
        ("call", "A", t, "owner()", [], None),
        ("call", "A", t, "totalSupply()", [], None),
        ("call", "A", t, "balanceOf(address)", [ADDR["A"]], None),
        ("call", "A", t, "balanceOf(address)", [ADDR["B"]], None),
        ("send", "A", t, raw("transfer(address,uint256)", word(int(ADDR["B"], 16))), [], None),
    ]


def erc721_steps():
    """OpenZeppelin's NFT behaviors, errors included, with a receiver contract."""
    n = "nft"
    safe = "safeTransferFrom(address,address,uint256)"
    safe_data = "safeTransferFrom(address,address,uint256,bytes)"
    return [
        ("call", "A", n, "name()", [], None),
        ("call", "A", n, "symbol()", [], None),
        ("call", "A", n, "owner()", [], None),
        ("call", "A", n, "supportsInterface(bytes4)", ["0x80ac58cd"], None),
        ("call", "A", n, "supportsInterface(bytes4)", ["0x5b5e139f"], None),
        ("call", "A", n, "supportsInterface(bytes4)", ["0x01ffc9a7"], None),
        ("call", "A", n, "supportsInterface(bytes4)", ["0xffffffff"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["A"], "1"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["B"], "2"], None),
        ("send", "B", n, "safeMint(address,uint256)", [ADDR["B"], "9"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ZERO, "3"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["B"], "1"], None),
        ("send", "A", n, "safeMint(address,uint256)", ["$receiver", "3"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["A"], "4"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["A"], "5"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["A"], "6"], None),
        ("call", "A", n, "balanceOf(address)", [ADDR["A"]], None),
        ("call", "A", n, "balanceOf(address)", [ZERO], None),
        ("call", "A", n, "ownerOf(uint256)", ["1"], None),
        ("call", "A", n, "ownerOf(uint256)", ["99"], None),
        ("call", "A", n, "tokenURI(uint256)", ["1"], None),
        ("call", "A", n, "tokenURI(uint256)", ["99"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "1"], None),
        ("call", "A", n, "getApproved(uint256)", ["1"], None),
        ("call", "A", n, "getApproved(uint256)", ["99"], None),
        ("send", "B", n, "approve(address,uint256)", [ADDR["B"], "4"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "99"], None),
        ("send", "B", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "1"], None),
        ("send", "B", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "1"], None),
        ("send", "B", n, "transferFrom(address,address,uint256)", [ADDR["B"], ZERO, "1"], None),
        ("send", "B", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "4"], None),
        ("send", "A", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "99"], None),
        ("send", "B", n, "setApprovalForAll(address,bool)", [ADDR["A"], "true"], None),
        ("send", "B", n, "setApprovalForAll(address,bool)", [ZERO, "true"], None),
        ("call", "A", n, "isApprovedForAll(address,address)", [ADDR["B"], ADDR["A"]], None),
        ("send", "A", n, "transferFrom(address,address,uint256)", [ADDR["B"], ADDR["A"], "2"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["A"], "1"], None),
        ("send", "A", n, safe, [ADDR["A"], ADDR["B"], "2"], None),
        ("send", "A", n, safe_data, [ADDR["A"], "$receiver", "4", "0x" + "ab" * 40], None),
        ("send", "A", n, safe_data, [ADDR["A"], "$receiver", "5", "0x1234"], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["1"], None),
        ("send", "A", n, safe, [ADDR["A"], "$receiver", "6"], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["2"], None),
        # The receiver's own reason passes through unchanged.
        ("call", "A", n, safe, [ADDR["A"], "$receiver", "6"], None),
        ("send", "A", n, safe, [ADDR["A"], "$receiver", "6"], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["0"], None),
        ("call", "A", n, safe, [ADDR["A"], "$nft", "6"], None),
        ("send", "A", n, safe, [ADDR["A"], "$nft", "6"], None),
        ("send", "A", n, "burn(uint256)", ["1"], None),
        ("send", "B", n, "burn(uint256)", ["1"], None),
        ("send", "B", n, "burn(uint256)", ["1"], None),
        ("call", "A", n, "getApproved(uint256)", ["1"], None),
        ("send", "B", n, "pause()", [], None),
        ("send", "A", n, "pause()", [], None),
        ("call", "A", n, "paused()", [], None),
        ("send", "A", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "6"], None),
        ("send", "A", n, "safeMint(address,uint256)", [ADDR["A"], "7"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "6"], None),
        ("send", "A", n, "unpause()", [], None),
        ("send", "B", n, "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], "6"], None),
        ("call", "A", n, "balanceOf(address)", [ADDR["A"]], None),
        ("call", "A", n, "balanceOf(address)", [ADDR["B"]], None),
        ("call", "A", n, "balanceOf(address)", ["$receiver"], None),
        ("send", "A", n, "transferOwnership(address)", [ADDR["B"]], None),
        ("send", "B", n, "renounceOwnership()", [], None),
        ("call", "A", n, "owner()", [], None),
    ]


SUITES = {
    "erc20": {"deploy": [("token", "erc20", "(address)", [ADDR["A"]])], "steps": erc20_steps("token")},
    "erc721": {
        "deploy": [("nft", "erc721", "(address)", [ADDR["A"]]), ("receiver", "receiver")],
        "steps": erc721_steps(),
    },
    # Lithe consumes call results in `defer ... then` continuations; Solidity inline.
    "swap": {
        "deploy": [("exchange", "exchange"), ("executor", "executor", "(address,uint256)", ["$exchange", "100"])],
        "steps": [
            ("call", "A", "exchange", "swap(uint256,uint256)", ["1000", "0"], None),
            ("send", "B", "exchange", "swap(uint256,uint256)", ["5000", "1"], None),
            ("send", "A", "executor", "execute(uint256,uint256,uint256)", ["1", "1000", "1990"], None),
            ("send", "A", "executor", "execute(uint256,uint256,uint256)", ["1", "1000", "0"], None),
            # The exchange's slippage check, then the executor's floor in the continuation.
            ("send", "A", "executor", "execute(uint256,uint256,uint256)", ["2", "1000", "5000"], None),
            ("send", "A", "executor", "execute(uint256,uint256,uint256)", ["3", "10", "0"], None),
            ("send", "B", "executor", "execute(uint256,uint256,uint256)", ["5", str(10**24), "0"], None),
            ("send", "A", "executor", "execute_and_deposit(uint256,uint256)", ["4", "500"], None),
            ("send", "A", "executor", "execute_and_deposit(uint256,uint256)", ["4", "500"], None),
            ("send", "A", "executor", "unwind(uint256)", ["4"], None),
            ("send", "A", "executor", "unwind(uint256)", ["4"], None),
            ("send", "A", "executor", "unwind(uint256)", ["9"], None),
            ("call", "A", "executor", "order_of(uint256)", ["1"], None),
            ("call", "A", "executor", "order_of(uint256)", ["2"], None),
            ("call", "A", "executor", "order_of(uint256)", ["4"], None),
            ("call", "A", "exchange", "shares_of(address)", ["$executor"], None),
        ],
    },
    "staking": {
        "deploy": [
            ("stake", "erc20", "(address)", [ADDR["A"]]),
            ("reward", "erc20", "(address)", [ADDR["A"]]),
            ("staking", "staking", "(address,address,address)", [ADDR["A"], "$reward", "$stake"]),
        ],
        "steps": [
            ("send", "A", "stake", "mint(address,uint256)", [ADDR["A"], str(1000 * E18)], None),
            ("send", "A", "stake", "mint(address,uint256)", [ADDR["B"], str(1000 * E18)], None),
            ("send", "A", "reward", "mint(address,uint256)", [ADDR["A"], str(2_000_000 * E18)], None),
            ("send", "A", "reward", "transfer(address,uint256)", ["$staking", str(700_000 * E18)], None),
            ("send", "B", "staking", "notifyRewardAmount(uint256)", [str(604_800 * E18)], None),
            ("send", "A", "staking", "notifyRewardAmount(uint256)", [str(10**30)], None),
            ("send", "A", "staking", "notifyRewardAmount(uint256)", [str(604_800 * E18)], None),
            ("send", "A", "stake", "approve(address,uint256)", ["$staking", MAX], None),
            ("send", "B", "stake", "approve(address,uint256)", ["$staking", MAX], None),
            ("send", "A", "staking", "stake(uint256)", ["0"], None),
            ("send", "A", "staking", "stake(uint256)", [str(100 * E18)], None),
            ("wait", 3600),
            ("send", "B", "staking", "stake(uint256)", [str(300 * E18)], None),
            ("wait", 7200),
            ("call", "A", "staking", "earned(address)", [ADDR["A"]], None),
            ("call", "A", "staking", "earned(address)", [ADDR["B"]], None),
            ("call", "A", "staking", "rewardPerToken()", [], None),
            ("send", "A", "staking", "getReward()", [], None),
            ("send", "A", "staking", "withdraw(uint256)", [str(50 * E18)], None),
            ("send", "A", "staking", "withdraw(uint256)", ["0"], None),
            ("send", "A", "staking", "withdraw(uint256)", [str(10**30)], None),
            ("wait", 86400),
            ("send", "B", "staking", "exit()", [], None),
            ("send", "B", "staking", "exit()", [], None),
            ("send", "A", "staking", "setRewardsDuration(uint256)", ["100"], None),
            ("wait", 604800),
            ("call", "A", "staking", "earned(address)", [ADDR["A"]], None),
            ("call", "A", "staking", "lastTimeRewardApplicable()", [], None),
            ("send", "A", "staking", "getReward()", [], None),
            ("send", "B", "staking", "setRewardsDuration(uint256)", ["86400"], None),
            ("send", "A", "staking", "setRewardsDuration(uint256)", ["86400"], None),
            ("send", "A", "staking", "notifyRewardAmount(uint256)", [str(1000 * E18)], None),
            ("call", "A", "staking", "getRewardForDuration()", [], None),
            ("call", "A", "staking", "rewardRate()", [], None),
            ("call", "A", "staking", "totalSupply()", [], None),
            ("call", "A", "stake", "balanceOf(address)", ["$staking"], None),
            ("call", "A", "reward", "balanceOf(address)", [ADDR["A"]], None),
            ("call", "A", "reward", "balanceOf(address)", [ADDR["B"]], None),
            ("call", "A", "staking", "rewardsToken()", [], None),
        ],
    },
}


def run(cmd, check=True):
    out = subprocess.run(cmd, capture_output=True, text=True)
    if check and out.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)}\n{out.stderr}")
    return out


def solc_binary():
    if os.environ.get("SOLC"):
        return os.environ["SOLC"]
    found = shutil.which("solc")
    if found:
        return found
    svm = os.path.expanduser("~/Library/Application Support/svm")
    if not os.path.isdir(svm):
        svm = os.path.expanduser("~/.svm")
    versions = sorted(
        (v for v in os.listdir(svm) if v[0].isdigit()),
        key=lambda v: [int(x) for x in v.split(".")],
    )
    return os.path.join(svm, versions[-1], f"solc-{versions[-1]}")


REMAPPINGS = [
    "@openzeppelin/contracts-upgradeable/=" + os.path.join(BENCH, "vendor", "openzeppelin-contracts-upgradeable", "contracts") + "/",
    "@openzeppelin/contracts/=" + os.path.join(BENCH, "vendor", "openzeppelin-contracts", "contracts") + "/",
]


def solc(path, flags):
    """Creation code and runtime size of the contract `path` defines, imports resolved."""
    out = run([SOLC, *flags, "--no-cbor-metadata", *REMAPPINGS, "--allow-paths", BENCH,
               "--combined-json", "bin,bin-runtime", path]).stdout
    contracts = json.loads(out)["contracts"]
    mine = [v for k, v in contracts.items() if k.split(":")[0].endswith(os.path.basename(path))]
    main = max(mine, key=lambda v: len(v["bin-runtime"]))
    return "0x" + main["bin"], len(main["bin-runtime"]) // 2


def lithe_builds():
    """Each pair's creation code and runtime size, from the Foundry-style artifacts. The
    Solidity contracts answer ERC-165 only where they implement it, so Lithe's generated
    `supportsInterface` is off; a contract that writes its own, as `erc721` does, keeps it."""
    out = tempfile.mkdtemp()
    subprocess.run([LITHE, "compile", "--erc165", "off", BENCH], cwd=out, check=True, capture_output=True)
    builds = {}
    for entry in os.listdir(os.path.join(out, "out")):
        folder = os.path.join(out, "out", entry)
        (artifact,) = os.listdir(folder)
        with open(os.path.join(folder, artifact)) as f:
            art = json.load(f)
        runtime = art["deployedBytecode"]["object"]
        builds[entry[: -len(".lithe")]] = (art["bytecode"]["object"], (len(runtime) - 2) // 2)
    shutil.rmtree(out)
    return builds


class Chain:
    """One anvil per build. Every chain replays the same transactions from the same
    accounts, so contracts land at the same addresses, and blocks get the same times."""

    def __init__(self, port):
        self.rpc = f"http://127.0.0.1:{port}"
        self.proc = subprocess.Popen(["anvil", "--port", str(port), "--silent"],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(100):
            if run(["cast", "block-number", "--rpc-url", self.rpc], check=False).returncode == 0:
                return
            time.sleep(0.1)
        raise RuntimeError("anvil did not start")

    def stop(self):
        self.proc.send_signal(signal.SIGTERM)
        self.proc.wait()

    def at(self, stamp):
        run(["cast", "rpc", "--rpc-url", self.rpc, "evm_setNextBlockTimestamp", str(stamp)])

    def send(self, to, sender, sig, args, value):
        cmd = ["cast", "send", "--rpc-url", self.rpc, "--private-key", KEYS[sender], "--json",
               "--gas-limit", "5000000"]
        if value:
            cmd += ["--value", value]
        if to is None:
            cmd += ["--create", sig]
        else:
            cmd += [to, sig, *args]
        receipt = json.loads(run(cmd).stdout)
        # Logs grouped by emitter: Lithe runs deferred calls after its own events, so the
        # order between contracts may differ, but each contract's own order may not.
        logs = {}
        for log in receipt.get("logs", []):
            logs.setdefault(log["address"].lower(), []).append((log["topics"], log["data"]))
        return {
            "status": int(receipt["status"], 16),
            "gas": int(receipt["gasUsed"], 16),
            "address": receipt.get("contractAddress"),
            "logs": logs,
        }

    def call(self, to, sender, sig, args):
        base = ["--rpc-url", self.rpc, "--from", ADDR[sender], to, sig, *args]
        out = run(["cast", "call", *base], check=False)
        if out.returncode != 0:
            # Keep only the revert data; the rest of the message names the contract.
            text = out.stderr.strip()
            data = text[text.find("0x"):].split()[0] if "0x" in text else "revert"
            return {"result": "revert " + data.strip('",)'), "gas": None}
        gas = run(["cast", "estimate", *base], check=False)
        return {"result": out.stdout.strip(), "gas": int(gas.stdout) if gas.returncode == 0 else None}

    def storage(self, addresses):
        """Every nonzero storage slot of each address, from anvil's state dump."""
        raw = json.loads(run(["cast", "rpc", "--rpc-url", self.rpc, "anvil_dumpState"]).stdout)
        data = binascii.unhexlify(raw[2:])
        try:
            data = gzip.decompress(data)
        except OSError:
            pass
        accounts = {k.lower(): v for k, v in json.loads(data)["accounts"].items()}
        out = {}
        for address in addresses:
            slots = accounts.get(address.lower(), {}).get("storage", {})
            out[address] = {int(k, 16): int(v, 16) for k, v in slots.items() if int(v, 16)}
        return out


# Blocks start here and advance by `STEP` seconds per transaction unless a step waits.
GENESIS = 2_000_000_000
STEP = 12


def suites():
    """Each benchmark: which pair builds each role, then the steps. Single-pair scenarios
    deploy one contract under their own name and target it."""
    out = {}
    for name, steps in SCENARIOS.items():
        out[name] = {"deploy": [(name, name)], "steps": [(k, s, name, sig, a, v) for k, s, sig, a, v in steps]}
    out.update(SUITES)
    return out


def main():
    pairs = sorted(n[:-6] for n in os.listdir(BENCH) if n.endswith(".lithe"))
    wanted = sys.argv[1:] or sorted(suites())
    order = ["lithe", *SOLC_BUILDS]
    code = {}
    builds = lithe_builds()
    print("Runtime bytecode (bytes)\n")
    header = ["contract", "lithe", *SOLC_BUILDS, "lithe vs best solc"]
    rows = []
    for name in pairs:
        code[name] = {"lithe": builds[name]}
        for label, flags in SOLC_BUILDS.items():
            code[name][label] = solc(os.path.join(BENCH, name + ".sol"), flags)
        sizes = [code[name][b][1] for b in order]
        best = min(sizes[1:])
        rows.append([name, *map(str, sizes), f"{(sizes[0] - best) * 100 / best:+.1f}%"])
    totals = [sum(int(r[i]) for r in rows) for i in range(1, 1 + len(order))]
    best = min(totals[1:])
    rows.append(["total", *map(str, totals), f"{(totals[0] - best) * 100 / best:+.1f}%"])
    table(header, rows)

    mismatches = 0
    print("\nGas per transaction (lower is better); views are estimates\n")
    for name in wanted:
        suite = suites()[name]
        chains = {b: Chain(8600 + i) for i, b in enumerate(order)}
        try:
            mismatches += replay(name, suite, code, order, chains)
        finally:
            for chain in chains.values():
                chain.stop()
    if mismatches:
        print(f"{mismatches} behavior mismatches")
        sys.exit(1)
    print("All builds behaved identically and left identical storage.")


def replay(name, suite, code, order, chains):
    mismatches = 0
    stamp = GENESIS
    roles = {}
    gas_rows = []
    fill = lambda a: roles[a[1:]] if a.startswith("$") else a
    # A role is `(role, pair)`, or `(role, pair, types, args)` for constructor arguments.
    for role, pair, *ctor in suite["deploy"]:
        encoded = ""
        if ctor:
            types, values = ctor
            encoded = run(["cast", "abi-encode", f"f{types}", *map(fill, values)]).stdout.strip()[2:]
        addrs = set()
        cells = []
        for build in order:
            chains[build].at(stamp)
            receipt = chains[build].send(None, "A", code[pair][build][0] + encoded, [], None)
            assert receipt["status"] == 1, f"{name} {role} {build} failed to deploy"
            addrs.add(receipt["address"].lower())
            cells.append(str(receipt["gas"]))
        assert len(addrs) == 1, f"{name}: {role} landed at different addresses"
        roles[role] = addrs.pop()
        gas_rows.append([f"deploy {role}", *cells])
        stamp += STEP
    for step in suite["steps"]:
        if step[0] == "wait":
            stamp += step[1]
            continue
        kind, sender, role, sig, args, value = step
        args = [fill(a) for a in args]
        results = {}
        for build in order:
            chain = chains[build]
            if kind == "send":
                chain.at(stamp)
                results[build] = chain.send(roles[role], sender, sig, args, value)
            else:
                results[build] = chain.call(roles[role], sender, sig, args)
        if kind == "send":
            stamp += STEP
        key = (lambda r: (r["status"], r["logs"])) if kind == "send" else (lambda r: r["result"])
        if not all(key(results[b]) == key(results["lithe"]) for b in order):
            mismatches += 1
            print(f"  MISMATCH {name} {role}.{sig} {args}:")
            for b in order:
                print(f"    {b}: {key(results[b])}")
        shown = [("$" + r if a in roles.values() and (r := next(k for k, v in roles.items() if v == a)) else a[:10])
                 for a in args]
        label = f"{sig.split('(')[0]}({', '.join(shown)})"
        if len(suite["deploy"]) > 1:
            label = f"{role}.{label}"
        if sig.startswith("0x"):
            label = f"raw {sig[:10]}.. {len(sig) // 2 - 1} bytes"
        if kind == "send" and results["lithe"]["status"] == 0:
            label += " reverts"
        elif kind == "call" and results["lithe"]["result"].startswith("revert"):
            label += " reverts"
        cells = [str(results[b]["gas"]) if results[b]["gas"] is not None else "-" for b in order]
        gas_rows.append([label, *cells])
    addresses = list(roles.values())
    slots = {b: chains[b].storage(addresses) for b in order}
    for b in order[1:]:
        for role, address in roles.items():
            want, have = slots["lithe"][address], slots[b][address]
            if want != have:
                mismatches += 1
                print(f"  STORAGE MISMATCH {name} {role}: lithe vs {b}")
                for k in sorted(set(want) | set(have)):
                    if want.get(k, 0) != have.get(k, 0):
                        print(f"    slot {k:#x}: lithe {want.get(k, 0):#x} {b} {have.get(k, 0):#x}")
    print(f"{name}")
    table(["tx", *order, "lithe vs best solc"], [[*row, vs_best(row[1:])] for row in gas_rows])
    print()
    return mismatches


def vs_best(cells):
    """Lithe's cell against the lowest solc cell, as a percentage; `-` without numbers."""
    if not all(c.isdigit() for c in cells):
        return "-"
    lithe, best = int(cells[0]), min(int(c) for c in cells[1:])
    return f"{(lithe - best) * 100 / best:+.1f}%"


def table(header, rows):
    widths = [max(len(str(r[i])) for r in [header, *rows]) for i in range(len(header))]
    line = lambda r: "| " + " | ".join(str(c).ljust(w) for c, w in zip(r, widths)) + " |"
    print(line(header))
    print("|" + "|".join("-" * (w + 2) for w in widths) + "|")
    for r in rows:
        print(line(r))


SOLC = solc_binary()

if __name__ == "__main__":
    main()
