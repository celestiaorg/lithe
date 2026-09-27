#!/usr/bin/env python3
"""Compare Lithe against solc on equivalent contracts.

For each `bench/<name>.lithe` and `bench/<name>.sol`, report runtime bytecode size
for Lithe and three solc configurations. Then deploy all of them to a local anvil,
replay the same transactions against each, check that statuses, return data, logs,
and every storage slot agree, and report gas. Lithe lays out storage like Solidity,
so the raw slots must match exactly, except for Solady's tokens, whose hashed slots
no Solidity layout has. Each pair must also expose the same functions, and answer
`supportsInterface` the same for every id either side's code pushes, so no side is
measured with entrypoints the other lacks.

Needs `anvil` and `cast` (Foundry) and solc. `SOLC` overrides the solc binary.
Run from the repository root: `python3 bench/run.py [name ...]`.
"""

import base64
import binascii
import gzip
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "bench")
# Through cargo so the bench always measures the compiler in this tree.
LITHE = ["cargo", "run", "--release", "--quiet", "--manifest-path", os.path.join(ROOT, "Cargo.toml"), "--"]
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

def enc(types, *args):
    """ABI-encoded values, as `abi.encode` lays them out, from Foundry's encoder."""
    return subprocess.run(["cast", "abi-encode", f"f({types})", *args], capture_output=True, text=True).stdout.strip()


ORDER = "(uint256,string,uint256[])"
ORDERS = "[(1,first,[10,20]),(2," + LONG + ",[]),(3,\"\",[7])]"
GRID = "[[1,2],[],[3,4,5]]"

# (kind, sender, signature, args, value): kind is "send" or "call". Each targets the
# contract its scenario is named after. `SUITES` below deploy several contracts by role.
SCENARIOS = {
    # ABI encoding and decoding on their own: flat values, several at once, and nested
    # ones. Every answer is compared with solc's byte for byte, malformed data included.
    "codec": [
        ("call", "A", "enc_flat(address,uint256,string)", [ADDR["B"], "7", LONG], None),
        ("call", "A", "dec_flat(bytes)", [enc("address,uint256,string", ADDR["B"], "7", LONG)], None),
        ("call", "A", "dec_flat(bytes)", ["0x" + word(1)], None),
        ("call", "A", "enc_orders(" + ORDER + "[])", [ORDERS], None),
        ("call", "A", "enc_orders(" + ORDER + "[])", ["[]"], None),
        ("call", "A", "dec_orders(bytes)", [enc(ORDER + "[]", ORDERS)], None),
        ("call", "A", "dec_orders(bytes)", ["0x" + word(0x20) + word(1) + word(0x1000)], None),
        ("call", "A", "dec_orders(bytes)", ["0x" + word(0x20) + word(1 << 64)], None),
        ("call", "A", "enc_grid(uint256[][])", [GRID], None),
        ("call", "A", "dec_grid(bytes)", [enc("uint256[][]", GRID)], None),
        ("call", "A", "packed(address,uint96,string)", [ADDR["A"], "5", LONG], None),
        ("call", "A", "calldata_for(" + ORDER + "[])", [ORDERS], None),
        ("send", "A", "keep(bytes)", [enc(ORDER + "[]", ORDERS)], None),
        ("call", "A", "seen()", [], None),
        ("call", "A", "digest()", [], None),
    ],
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
    # Reverting calls compare the ABI-encoded error payloads byte for byte; sends give gas.
    "traits": [
        ("send", "A", "mint(uint256)", ["3"], None),
        ("send", "A", "tag(uint256,string)", ["1", "Background"], None),
        ("send", "A", "tag(uint256,string)", ["1", ""], None),
        ("call", "A", "tag(uint256,string)", ["1", ""], None),
        ("send", "A", "tag(uint256,string)", ["9", "Background"], None),
        ("call", "A", "tag(uint256,string)", ["9", "Background"], None),
        ("call", "A", "tag(uint256,string)", ["9", LONG], None),
        ("call", "A", "background(uint256)", ["2"], None),
        ("call", "A", "background(uint256)", ["3"], None),
        ("call", "A", "check(uint256[])", ["[0,1,2]"], None),
        ("call", "A", "check(uint256[])", ["[0,5,1]"], None),
        ("call", "A", "check(uint256[])", ["[]"], None),
    ],
    "shapes": [
        ("send", "A", "add(uint256)", ["0"], None),
        ("call", "A", "add(uint256)", ["0"], None),
        ("send", "B", "add(uint256)", ["3"], None),
        ("call", "B", "add(uint256)", ["3"], None),
        ("send", "A", "add(uint256)", ["5"], None),
        ("send", "A", "buy(uint256,string)", ["2", "Widget"], None),
        ("send", "A", "buy(uint256,string)", ["9", "Widget"], None),
        ("call", "A", "buy(uint256,string)", ["9", "Widget"], None),
        ("call", "A", "buy(uint256,string)", ["9", LONG], None),
        ("call", "A", "buy(uint256,string)", ["1", ""], None),
        ("call", "A", "buy(uint256,string)", ["1", "x" * 41], None),
        ("call", "A", "buy_all(uint256[],string)", ["[]", "nothing to buy"], None),
        ("call", "A", "buy_all(uint256[],string)", ["[1,2,3,4,5]", LONG], None),
        ("send", "A", "buy_all(uint256[],string)", ["[1,9]", "n"], None),
        ("call", "A", "buy_all(uint256[],string)", ["[1,9]", "n"], None),
        ("call", "A", "buy_all(uint256[],string)", ["[0,1]", LONG], None),
        ("send", "A", "buy_all(uint256[],string)", ["[1,2]", "ok"], None),
        ("call", "A", "load(bytes)", ["0x"], None),
        ("send", "A", "load(bytes)", ["0xdeadbeef"], None),
        ("call", "B", "load(bytes)", ["0xdeadbeef"], None),
        ("call", "A", "load(bytes)", ["0x" + "ab" * 65], None),
        ("call", "A", "compare(string,string)", ["abc", "abc"], None),
        ("call", "A", "compare(string,string)", ["abc", "abd"], None),
        ("call", "A", "compare(string,string)", [LONG, "x"], None),
        ("call", "A", "compare(string,string)", ["", ""], None),
    ],
    # Every reason is a literal of at most 31 bytes, one of them exactly 31.
    "reasons": [
        ("send", "A", "deposit(uint256)", ["100"], None),
        ("send", "A", "deposit(uint256)", ["0"], None),
        ("call", "A", "deposit(uint256)", ["0"], None),
        ("call", "A", "deposit(uint256)", ["5000"], None),
        ("send", "A", "withdraw(uint256)", ["500"], None),
        ("call", "A", "withdraw(uint256)", ["500"], None),
        ("send", "A", "withdraw(uint256)", ["50"], None),
        ("call", "A", "transfer(address,uint256)", ["0x0000000000000000000000000000000000000000", "1"], None),
        ("call", "A", "transfer(address,uint256)", [ADDR["A"], "1"], None),
        ("send", "A", "transfer(address,uint256)", [ADDR["B"], "10"], None),
        ("send", "B", "set_limit(uint256)", ["5"], None),
        ("call", "B", "set_limit(uint256)", ["5"], None),
        ("call", "A", "set_limit(uint256)", ["0"], None),
        ("call", "A", "set_limit(uint256)", ["2000000"], None),
        ("send", "A", "set_limit(uint256)", ["2000"], None),
        ("call", "A", "pause(bool)", ["false"], None),
        ("send", "A", "pause(bool)", ["true"], None),
        ("send", "A", "deposit(uint256)", ["1"], None),
        ("call", "A", "deposit(uint256)", ["1"], None),
        ("call", "A", "balance_of(address)", ["0x0000000000000000000000000000000000000000"], None),
        ("call", "A", "balance_of(address)", [ADDR["A"]], None),
    ],
    # Names cross one word: empty, 31 bytes, 32 bytes, and several words.
    "strings": [
        ("send", "A", "rename(string)", ["Short"], None),
        ("send", "A", "rename(string)", ["Short"], None),
        ("call", "A", "rename(string)", ["Short"], None),
        ("send", "A", "rename(string)", [LONG], None),
        ("call", "A", "rename(string)", [LONG], None),
        ("send", "B", "rename(string)", ["Other"], None),
        ("call", "B", "rename(string)", ["Other"], None),
        ("call", "A", "rename(string)", ["n" * 101], None),
        ("send", "A", "describe(string)", ["a description that is well past one word in length"], None),
        ("call", "B", "describe(string)", ["x"], None),
        ("call", "A", "describe(string)", ["d" * 201], None),
        ("call", "A", "description()", [], None),
        ("call", "A", "name()", [], None),
        ("call", "A", "title(string)", ["Dr."], None),
        ("call", "A", "title(string)", [LONG], None),
        ("call", "A", "require_name(string)", ["nope"], None),
        ("call", "A", "require_name(string)", [LONG], None),
        ("send", "A", "rename(string)", ["a" * 31], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "describe(string)", ["short"], None),
        ("call", "A", "description()", [], None),
        ("send", "A", "rename(string)", ["b" * 32], None),
        ("call", "A", "name()", [], None),
        ("send", "A", "rename(string)", [""], None),
        ("call", "A", "name()", [], None),
        ("call", "B", "describe(string)", ["x"], None),
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
        ("send", "A", "head_set(uint128)", ["7"], None),
        ("send", "B", "head_set(uint128)", [str(2**128 - 1)], None),
        ("send", "B", "head_set(uint128)", ["9"], None),
        ("send", "A", "head_swap()", [], None),
        ("call", "A", "head_pair()", [], None),
        ("call", "A", "pair_of(address,uint256)", [ADDR["B"], "0"], None),
        ("call", "A", "pair_of(address,uint256)", [ADDR["A"], "0"], None),
        ("call", "A", "odd_of(uint128)", ["7"], None),
        ("call", "A", "odd_of(uint128)", ["8"], None),
        ("send", "A", "promote(uint256)", ["1"], None),
        ("call", "A", "top_order()", [], None),
        ("send", "B", "reset_top(uint256,int16)", ["77", "-5"], None),
        ("call", "A", "top_order()", [], None),
        ("send", "A", "reset_top(uint256,int16)", ["3", "32767"], None),
        ("send", "A", "promote(uint256)", ["9"], None),
        ("call", "A", "top_order()", [], None),
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
    "texts": [
        ("send", "A", "save(bytes[])", ["[0x0102,0x" + "cd" * 40 + ",0x]"], None),
        ("call", "A", "saved()", [], None),
        ("call", "A", "saved_at(uint256)", ["1"], None),
        ("call", "A", "saved_at(uint256)", ["3"], None),
        ("send", "A", "push(bytes)", ["0x" + "ef" * 33], None),
        ("send", "A", "set_at(uint256,bytes)", ["1", "0x09"], None),
        ("call", "A", "joined()", [], None),
        # Shorter lists and values leave no data behind in the slots they no longer use.
        ("send", "A", "save(bytes[])", ["[0x" + "ab" * 31 + "]"], None),
        ("call", "A", "saved()", [], None),
        ("send", "A", "save(bytes[])", ["[]"], None),
        ("send", "A", "set_names(string[])", ["[" + LONG + ",hi,]"], None),
        ("call", "A", "names()", [], None),
        ("send", "A", "set_names(string[])", ["[x]"], None),
        ("send", "A", "label(uint256,string)", ["7", LONG], None),
        ("call", "A", "label_of(uint256)", ["7"], None),
        ("send", "A", "label(uint256,string)", ["7", "short"], None),
        ("call", "A", "label_of(uint256)", ["7"], None),
        ("call", "A", "label_of(uint256)", ["8"], None),
        ("call", "A", "first(bytes[])", ["[0x0102,0x030405]"], None),
        ("call", "A", "concat_all(bytes[])", ["[0x0102,0x030405,0x" + "cd" * 40 + "]"], None),
        ("call", "A", "echo(string[])", ["[" + LONG + ",ab,]"], None),
        ("call", "A", "pair(bytes,bytes)", ["0x0102", "0x" + "cd" * 40], None),
        # An empty value is its length alone, not the word that follows it.
        ("call", "A", "left(bytes,bytes)", ["0x", "0x010203"], None),
        ("call", "A", "same(bytes[],bytes[])", ["[0x0102,0x]", "[0x0102,0x]"], None),
        ("call", "A", "same(bytes[],bytes[])", ["[0x0102,0x]", "[0x0102,0x00]"], None),
        ("call", "A", "encoded(uint256,string[])", ["7", "[" + LONG + ",hi]"], None),
        ("call", "A", "decoded(bytes)", ["0x" + word(0x20) + word(2) + word(0x40) + word(0x80) + word(2) + "0102" + "00" * 30 + word(0)], None),
        # An element's offset past the data, and its length past the data.
        ("send", "A", raw("save(bytes[])", word(0x20), word(1), word(0x1000)), [], None),
        ("send", "A", raw("save(bytes[])", word(0x20), word(1), word(0x20), word(64)), [], None),
        ("call", "A", "decoded(bytes)", ["0x" + word(0x20) + word(1) + word(0x1000)], None),
        # Abi.decode reads a word or a string from calldata or memory, and rejects data
        # too short for its head, dirty bits, and offsets or lengths past the data.
        ("call", "A", "small_of(bytes)", ["0x" + word(7)], None),
        ("call", "A", "small_of(bytes)", ["0x" + word(256)], None),
        ("call", "A", "small_of(bytes)", ["0x07"], None),
        ("call", "A", "text_of(bytes)", ["0x" + word(0x20) + word(2) + "6869" + "00" * 30], None),
        ("call", "A", "text_of(bytes)", ["0x" + word(0x20) + word(40) + "ab" * 40 + "00" * 24], None),
        ("call", "A", "text_of(bytes)", ["0x" + word(0x20) + word(1000)], None),
        ("call", "A", "text_of(bytes)", ["0x" + word(0x1000)], None),
        ("call", "A", "addr_mem(bytes)", ["0x" + word(0xabc)], None),
        ("call", "A", "addr_mem(bytes)", ["0x" + word(1 << 160)], None),
        ("call", "A", "addr_mem(bytes)", ["0x"], None),
        ("call", "A", "text_mem(bytes)", ["0x" + word(0x20) + word(40) + "ab" * 40 + "00" * 24], None),
        ("call", "A", "text_mem(bytes)", ["0x" + word(0x40) + word(0) + word(3) + "616263" + "00" * 29], None),
        ("call", "A", "text_mem(bytes)", ["0x" + word(0x20) + word(33) + "ab" * 32], None),
        ("call", "A", "names_mem(bytes)", ["0x" + word(0x20) + word(2) + word(0x40) + word(0x80) + word(2) + "6869" + "00" * 30 + word(0)], None),
        ("call", "A", "names_mem(bytes)", ["0x" + word(0x20) + word(2) + word(0x40)], None),
        # A decoded short string compares, measures, and stores like any other.
        ("call", "A", "same_text(string,bytes)", ["hi", "0x" + word(0x20) + word(2) + "6869" + "00" * 30], None),
        ("call", "A", "same_text(string,bytes)", [LONG, "0x" + word(0x20) + word(len(LONG)) + LONG.encode().hex() + "00" * (-len(LONG) % 32)], None),
        ("call", "A", "same_text(string,bytes)", ["ho", "0x" + word(0x20) + word(2) + "6869" + "00" * 30], None),
        ("call", "A", "empty_text(bytes)", ["0x" + word(0x20) + word(0)], None),
        ("send", "A", "keep_text(uint256,bytes)", ["9", "0x" + word(0x20) + word(40) + "ab" * 40 + "00" * 24], None),
        ("send", "A", "keep_text(uint256,bytes)", ["9", "0x" + word(0x20) + word(2) + "6869" + "00" * 30], None),
        ("call", "A", "label_of(uint256)", ["9"], None),
        ("call", "A", "note()", [], None),
        ("call", "A", "selector_only()", [], None),
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
    "names": [
        ("send", "A", "set_name(uint256,string)", ["1", "hello"], None),
        ("call", "A", "name(uint256)", ["1"], None),
        ("send", "A", "set_name(uint256,string)", ["1", LONG], None),
        ("call", "A", "name(uint256)", ["1"], None),
        # Shrinking a stored value must clear the data slots it no longer uses.
        ("send", "A", "set_name(uint256,string)", ["1", LONG * 3], None),
        ("send", "A", "set_name(uint256,string)", ["1", LONG], None),
        ("call", "A", "name(uint256)", ["1"], None),
        ("send", "A", "set_name(uint256,string)", ["1", "hi"], None),
        ("call", "A", "name(uint256)", ["1"], None),
        ("call", "A", "name(uint256)", ["2"], None),
        ("send", "A", "set_blob(bytes32,bytes)", ["0x" + "11" * 32, "0x" + "ab" * 70], None),
        ("call", "A", "blob(bytes32)", ["0x" + "11" * 32], None),
        ("send", "A", "set_blob(bytes32,bytes)", ["0x" + "11" * 32, "0x" + "cd" * 32], None),
        ("send", "A", "set_blob(bytes32,bytes)", ["0x" + "11" * 32, "0x" + "ef" * 5], None),
        ("call", "A", "blob(bytes32)", ["0x" + "11" * 32], None),
        ("send", "A", "set_label(uint256,string)", ["3", LONG], None),
        ("send", "B", "set_label(uint256,string)", ["3", "bee"], None),
        ("call", "A", "label(address,uint256)", [ADDR["A"], "3"], None),
        ("call", "A", "label(address,uint256)", [ADDR["B"], "3"], None),
        ("send", "A", "add_note(string)", ["short"], None),
        ("send", "A", "add_note(string)", [LONG], None),
        ("send", "A", "add_note(string)", [LONG * 2], None),
        ("call", "A", "note(uint256)", ["1"], None),
        ("call", "A", "note_copy(uint256)", ["2"], None),
        ("call", "A", "notes_length()", [], None),
        ("send", "A", "set_note(uint256,string)", ["2", "x"], None),
        ("send", "A", "set_note(uint256,string)", ["0", LONG * 3], None),
        ("call", "A", "note(uint256)", ["0"], None),
        ("call", "A", "note(uint256)", ["2"], None),
        # An index past the end panics, for writes and reads alike.
        ("send", "A", "set_note(uint256,string)", ["5", "y"], None),
        ("call", "A", "note(uint256)", ["9"], None),
        # A whole list replaces a longer one, clearing the elements and data it no longer uses.
        ("send", "A", "set_notes(string,string)", ["b", LONG], None),
        ("call", "A", "note_copy(uint256)", ["1"], None),
        ("call", "A", "notes_length()", [], None),
    ],
    "base64": [
        ("call", "A", "encode(bytes)", ["0x"], None),
        ("call", "A", "encode(bytes)", ["0x66"], None),
        ("call", "A", "encode(bytes)", ["0x" + "ab" * 20], None),
        ("call", "A", "encode(bytes)", ["0x" + "ab" * 32], None),
        ("call", "A", "encode(bytes)", ["0x" + "5a" * 100], None),
        ("call", "A", "encode(bytes)", ["0x" + "c3" * 1000], None),
        ("call", "A", "encode_with(bytes,bool,bool)", ["0x" + "fb" * 50, "true", "true"], None),
        ("call", "A", "encode_with(bytes,bool,bool)", ["0x" + "fb" * 50, "false", "true"], None),
        ("call", "A", "decode(string)", ["Zm9vYmFy"], None),
        ("call", "A", "decode(string)", ["Zm9vYg=="], None),
        ("call", "A", "decode(string)", ["Pz8_-,A"], None),
        ("call", "A", "decode(string)", [base64.b64encode(bytes(range(256)) * 4).decode()], None),
    ],
    # Overloads picked by argument count and type, some writing the map they are given.
    "overloads": [
        ("send", "A", "deposit(uint256)", ["10000"], None),
        ("send", "B", "deposit(uint256,uint256)", ["10000", "100"], None),
        ("send", "A", "deposit(uint256,uint256)", ["10000", "10001"], None),
        ("send", "A", "stake(uint256)", ["500"], None),
        ("send", "A", "transfer(address,uint256)", [ADDR["B"], "70"], None),
        ("send", "B", "transfer(address,uint256)", [ADDR["A"], "99999"], None),
        ("send", "A", "transfer_staked(address,uint256)", [ADDR["B"], "200"], None),
        ("send", "B", "transfer_staked(address,uint256)", [ADDR["A"], "201"], None),
        ("call", "A", "balance_of(address)", [ADDR["A"]], None),
        ("call", "A", "balance_of(address)", [ADDR["B"]], None),
        ("call", "A", "staked_of(address)", [ADDR["B"]], None),
        ("call", "A", "total()", [], None),
    ],
    # A module passes its own namespaced storage to a generic module, once per key type.
    "tally": [
        ("send", "A", "vote(bytes32,uint256)", ["0x" + "01" * 32, "3"], None),
        ("send", "B", "vote(bytes32,uint256)", ["0x" + "01" * 32, "5"], None),
        ("send", "A", "vote(bytes32,uint256)", ["0x" + "02" * 32, "7"], None),
        ("send", "B", "vote(bytes32,uint256)", ["0x" + "02" * 32, "0"], None),
        ("send", "B", "vote(bytes32,uint256)", ["0x" + "03" * 32, str(2**256 - 1)], None),
        ("call", "A", "votes_of(address)", [ADDR["A"]], None),
        ("call", "A", "votes_of(address)", [ADDR["B"]], None),
        ("call", "A", "votes_for(bytes32)", ["0x" + "01" * 32], None),
        ("call", "A", "votes_for(bytes32)", ["0x" + "03" * 32], None),
        ("call", "A", "total_votes()", [], None),
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
        # Two dynamic arguments in one call: empty, short, at 31 and 32 bytes, and long.
        ("send", "A", "set_both(string,bytes)", ["", "0x0102"], None),
        ("call", "A", "name()", [], None),
        ("call", "A", "blob()", [], None),
        ("send", "A", "set_both(string,bytes)", ["hi", "0x"], None),
        ("send", "A", "set_both(string,bytes)", ["x" * 31, "0x" + "ab" * 32], None),
        ("send", "A", "set_both(string,bytes)", [LONG, "0x" + "cd" * 31], None),
        ("call", "A", "name()", [], None),
        ("call", "A", "blob()", [], None),
        # The padding after short data need not be zero.
        ("send", "A", raw("set_both(string,bytes)", word(0x40), word(0x80),
                          word(2), "6869" + "ff" * 30, word(1), "ab" + "ff" * 31), [], None),
        ("call", "A", "name()", [], None),
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


def erc1155_steps():
    """OpenZeppelin's multi-token behaviors, errors included, with a receiver in each of its
    modes and a contract that has no hook."""
    m = "mt"
    a, b = ADDR["A"], ADDR["B"]
    mint = "mint(address,uint256,uint256,bytes)"
    mint_batch = "mintBatch(address,uint256[],uint256[],bytes)"
    safe = "safeTransferFrom(address,address,uint256,uint256,bytes)"
    safe_batch = "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)"
    burn = "burn(address,uint256,uint256)"
    burn_batch = "burnBatch(address,uint256[],uint256[])"
    batch_of = "balanceOfBatch(address[],uint256[])"
    long = "0x" + "ab" * 100
    mode = lambda n: ("send", "A", "r1155", "set_mode(uint256)", [str(n)], None)
    return [
        ("call", "A", m, "uri(uint256)", ["1"], None),
        ("call", "A", m, "owner()", [], None),
        *[("call", "A", m, "supportsInterface(bytes4)", [i], None)
          for i in ["0xd9b67a26", "0x0e89341c", "0x01ffc9a7", "0x80ac58cd", "0xffffffff"]],
        ("send", "A", m, mint, [a, "1", "100", "0x"], None),
        ("send", "A", m, mint, [b, "2", "50", "0x1234"], None),
        ("send", "B", m, mint, [b, "2", "1", "0x"], None),
        ("send", "A", m, mint, [ZERO, "1", "1", "0x"], None),
        ("send", "A", m, mint, ["$r1155", "3", "10", long], None),
        ("send", "A", m, mint, ["$plain", "3", "1", "0x"], None),
        ("send", "A", m, mint_batch, [a, "[1,2,3]", "[10,20,30]", "0x"], None),
        # Repeated ids, and a long payload to the batch hook.
        ("send", "A", m, mint_batch, ["$r1155", "[4,5,4]", "[1,2,3]", long], None),
        # One id logs `TransferSingle` but still asks the batch hook.
        ("send", "A", m, mint_batch, ["$r1155", "[7]", "[1]", "0x"], None),
        ("send", "A", m, mint_batch, [a, "[]", "[]", "0x"], None),
        ("send", "A", m, mint_batch, [a, "[1,2]", "[1]", "0x"], None),
        ("send", "A", m, mint_batch, [ZERO, "[1]", "[1]", "0x"], None),
        ("send", "A", m, mint_batch, ["$plain", "[1,2]", "[1,1]", "0x"], None),
        mode(1),
        ("send", "A", m, mint, ["$r1155", "3", "1", "0x"], None),
        ("send", "A", m, mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"], None),
        mode(2),
        # The receiver's own reason passes through unchanged.
        ("call", "A", m, mint, ["$r1155", "3", "1", "0x"], None),
        ("call", "A", m, mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"], None),
        ("send", "A", m, mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"], None),
        mode(3),
        ("call", "A", m, mint, ["$r1155", "3", "1", "0x"], None),
        ("send", "A", m, mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"], None),
        mode(0),
        ("call", "A", m, "balanceOf(address,uint256)", [a, "1"], None),
        ("call", "A", m, "balanceOf(address,uint256)", ["$r1155", "4"], None),
        ("call", "A", m, batch_of, [f"[{a},{b},{a},{a}]", "[1,2,3,99]"], None),
        ("call", "A", m, batch_of, [f"[{a},{b}]", "[1]"], None),
        ("call", "A", m, batch_of, ["[]", "[]"], None),
        ("send", "A", m, safe, [a, b, "1", "5", "0x"], None),
        ("send", "B", m, safe, [a, b, "1", "5", "0x"], None),
        ("send", "A", m, safe, [a, b, "1", "1000", "0x"], None),
        ("send", "A", m, safe, [a, ZERO, "1", "1", "0x"], None),
        ("send", "A", m, safe, [ZERO, b, "1", "1", "0x"], None),
        ("send", "A", m, safe, [a, "$r1155", "1", "5", long], None),
        ("send", "A", m, safe, [a, "$plain", "1", "5", "0x"], None),
        ("send", "A", m, "setApprovalForAll(address,bool)", [b, "true"], None),
        ("send", "A", m, "setApprovalForAll(address,bool)", [ZERO, "true"], None),
        ("call", "A", m, "isApprovedForAll(address,address)", [a, b], None),
        ("send", "B", m, safe, [a, b, "1", "5", "0x"], None),
        ("send", "A", m, safe_batch, [a, b, "[1,2,3]", "[1,2,3]", "0x"], None),
        ("send", "A", m, safe_batch, [a, b, "[1,1,2]", "[1,2,3]", "0x1234"], None),
        ("send", "A", m, safe_batch, [a, b, "[1,2]", "[1]", "0x"], None),
        # The second id's balance runs out.
        ("send", "A", m, safe_batch, [a, b, "[1,2]", "[1,1000]", "0x"], None),
        # Repeated ids draw on one balance.
        ("send", "A", m, safe_batch, [a, b, "[3,3]", "[20,20]", "0x"], None),
        ("send", "A", m, safe_batch, [a, ZERO, "[1]", "[1]", "0x"], None),
        ("send", "B", m, safe_batch, [b, a, "[2]", "[1]", "0x"], None),
        ("send", "A", m, safe_batch, [b, a, "[2]", "[1]", "0x"], None),
        ("send", "A", m, safe_batch, [a, "$r1155", "[1,3,1]", "[1,1,1]", long], None),
        ("send", "A", m, safe_batch, [a, "$plain", "[1,3]", "[1,1]", "0x"], None),
        ("send", "A", m, burn, [a, "1", "1"], None),
        ("send", "B", m, burn, [a, "1", "1"], None),
        ("send", "A", m, "setApprovalForAll(address,bool)", [b, "false"], None),
        ("send", "B", m, burn, [a, "1", "1"], None),
        ("send", "A", m, burn, [a, "1", "1000"], None),
        ("send", "A", m, burn, [ZERO, "1", "1"], None),
        ("send", "A", m, burn_batch, [a, "[1,2,3]", "[1,1,1]"], None),
        ("send", "A", m, burn_batch, [a, "[1,1]", "[1,1]"], None),
        ("send", "A", m, burn_batch, [a, "[1,2]", "[1]"], None),
        ("send", "A", m, burn_batch, [a, "[1,2]", "[1,1000]"], None),
        ("send", "B", m, burn_batch, [a, "[1]", "[1]"], None),
        ("call", "A", m, "totalSupply(uint256)", ["1"], None),
        ("call", "A", m, "totalSupply(uint256)", ["4"], None),
        ("call", "A", m, "totalSupply()", [], None),
        ("call", "A", m, "exists(uint256)", ["1"], None),
        ("call", "A", m, "exists(uint256)", ["99"], None),
        # The total of every id overflows.
        ("send", "A", m, mint, [a, "9", MAX, "0x"], None),
        ("send", "B", m, "setURI(string)", ["ipfs://x/{id}"], None),
        ("send", "A", m, "setURI(string)", ["ipfs://x/{id}"], None),
        ("call", "A", m, "uri(uint256)", ["1"], None),
        ("send", "A", m, "setURI(string)", [LONG + "/{id}.json"], None),
        ("call", "A", m, "uri(uint256)", ["7"], None),
        ("send", "B", m, "pause()", [], None),
        ("send", "A", m, "pause()", [], None),
        ("send", "A", m, "pause()", [], None),
        ("call", "A", m, "paused()", [], None),
        ("send", "A", m, safe, [a, b, "1", "1", "0x"], None),
        ("send", "A", m, safe_batch, [a, b, "[1]", "[1]", "0x"], None),
        # Checked before the pause: the receiver.
        ("send", "A", m, safe, [a, ZERO, "1", "1", "0x"], None),
        ("send", "A", m, mint, [a, "1", "1", "0x"], None),
        ("send", "A", m, mint_batch, [a, "[1]", "[1]", "0x"], None),
        ("send", "A", m, burn, [a, "1", "1"], None),
        ("send", "A", m, burn_batch, [a, "[1]", "[1]"], None),
        ("send", "A", m, "setApprovalForAll(address,bool)", [b, "true"], None),
        ("send", "A", m, "unpause()", [], None),
        ("send", "A", m, "unpause()", [], None),
        ("send", "B", m, safe, [a, b, "1", "1", "0x"], None),
        ("send", "A", m, "transferOwnership(address)", [ZERO], None),
        ("send", "A", m, "transferOwnership(address)", [b], None),
        ("send", "A", m, mint, [a, "1", "1", "0x"], None),
        ("send", "B", m, mint_batch, [a, "[1,8]", "[1,1]", "0x"], None),
        ("send", "B", m, "renounceOwnership()", [], None),
        ("call", "A", m, "owner()", [], None),
        ("call", "A", m, batch_of, [f"[{a},{b},{a},{b}]", "[1,1,8,8]"], None),
        ("call", "A", m, "balanceOf(address,uint256)", ["$r1155", "1"], None),
        ("call", "A", m, "totalSupply()", [], None),
        ("send", "A", m, raw(batch_of, word(0x40), word(0x60), word(1)), [], None),
    ]


def erc721_full_steps():
    """The full wizard NFT: enumeration through transfers and burns, per-token and base
    URIs, royalties, pausing, and ownership, errors included, with a receiver contract."""
    n = "nft"
    mint = "safeMint(address,string)"
    xfer = "transferFrom(address,address,uint256)"
    safe = "safeTransferFrom(address,address,uint256)"
    safe_data = "safeTransferFrom(address,address,uint256,bytes)"
    royalty = "royaltyInfo(uint256,uint256)"
    set_default = "setDefaultRoyalty(address,uint96)"
    set_token = "setTokenRoyalty(uint256,address,uint96)"
    by_index = "tokenByIndex(uint256)"
    of_owner = "tokenOfOwnerByIndex(address,uint256)"

    def enumerate_all(count):
        """Every enumeration, one past each end: the swap-and-pop order shows here."""
        return [
            ("call", "A", n, "totalSupply()", [], None),
            *[("call", "A", n, by_index, [str(i)], None) for i in range(count + 1)],
            *[("call", "A", n, of_owner, [who, str(i)], None)
              for who in [ADDR["A"], ADDR["B"], "$receiver"] for i in range(4)],
        ]

    return [
        ("call", "A", n, "name()", [], None),
        ("call", "A", n, "symbol()", [], None),
        ("call", "A", n, "owner()", [], None),
        *[("call", "A", n, "supportsInterface(bytes4)", [i], None)
          for i in ["0x80ac58cd", "0x5b5e139f", "0x780e9d63", "0x49064906", "0x2a55205a",
                    "0x01ffc9a7", "0xffffffff", "0x00000000"]],
        ("call", "A", n, "totalSupply()", [], None),
        ("call", "A", n, by_index, ["0"], None),
        ("call", "A", n, royalty, ["0", str(E18)], None),
        # Ids 0 to 5: a per-token URI, none, a long one to the receiver, then more.
        ("call", "A", n, mint, [ADDR["A"], "a.json"], None),
        ("send", "A", n, mint, [ADDR["A"], "a.json"], None),
        ("send", "A", n, mint, [ADDR["B"], ""], None),
        ("send", "B", n, mint, [ADDR["B"], "b.json"], None),
        ("send", "A", n, mint, [ZERO, "z.json"], None),
        ("send", "A", n, mint, ["$receiver", LONG], None),
        ("send", "A", n, mint, [ADDR["A"], "d.json"], None),
        ("send", "A", n, mint, [ADDR["A"], "e.json"], None),
        ("send", "A", n, mint, [ADDR["B"], "f.json"], None),
        ("call", "A", n, mint, [ADDR["B"], "g.json"], None),
        *enumerate_all(6),
        ("call", "A", n, of_owner, [ZERO, "0"], None),
        ("call", "A", n, "balanceOf(address)", [ADDR["A"]], None),
        ("call", "A", n, "balanceOf(address)", [ZERO], None),
        ("call", "A", n, "ownerOf(uint256)", ["2"], None),
        ("call", "A", n, "ownerOf(uint256)", ["99"], None),
        *[("call", "A", n, "tokenURI(uint256)", [str(i)], None) for i in [0, 1, 2, 5, 99]],
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "0"], None),
        ("call", "A", n, "getApproved(uint256)", ["0"], None),
        ("call", "A", n, "getApproved(uint256)", ["99"], None),
        ("send", "B", n, "approve(address,uint256)", [ADDR["B"], "3"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "99"], None),
        # Moves the owner's first token: its last token takes the empty place.
        ("send", "B", n, xfer, [ADDR["A"], ADDR["B"], "0"], None),
        ("send", "B", n, xfer, [ADDR["A"], ADDR["B"], "0"], None),
        ("send", "B", n, xfer, [ADDR["B"], ZERO, "0"], None),
        ("send", "B", n, xfer, [ADDR["A"], ADDR["B"], "3"], None),
        ("send", "A", n, xfer, [ADDR["A"], ADDR["B"], "99"], None),
        ("send", "B", n, "setApprovalForAll(address,bool)", [ADDR["A"], "true"], None),
        ("send", "B", n, "setApprovalForAll(address,bool)", [ZERO, "true"], None),
        ("call", "A", n, "isApprovedForAll(address,address)", [ADDR["B"], ADDR["A"]], None),
        ("send", "A", n, xfer, [ADDR["B"], ADDR["A"], "1"], None),
        ("send", "A", n, xfer, [ADDR["A"], ADDR["A"], "1"], None),
        *enumerate_all(6),
        ("send", "A", n, safe, [ADDR["A"], ADDR["B"], "3"], None),
        ("send", "A", n, safe_data, [ADDR["A"], "$receiver", "4", "0x" + "ab" * 40], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["1"], None),
        ("send", "A", n, safe, [ADDR["A"], "$receiver", "1"], None),
        ("send", "A", n, mint, ["$receiver", "r.json"], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["2"], None),
        # The receiver's own reason passes through unchanged.
        ("call", "A", n, safe, [ADDR["A"], "$receiver", "1"], None),
        ("send", "A", n, safe, [ADDR["A"], "$receiver", "1"], None),
        ("send", "A", "receiver", "set_mode(uint256)", ["0"], None),
        ("call", "A", n, safe, [ADDR["A"], "$nft", "1"], None),
        ("send", "A", n, safe, [ADDR["A"], "$nft", "1"], None),
        ("send", "A", n, safe, [ADDR["B"], ADDR["A"], "1"], None),
        *enumerate_all(6),
        # Burning takes the last token of both enumerations into the burned one's place.
        ("send", "A", n, "burn(uint256)", ["5"], None),
        ("send", "B", n, "burn(uint256)", ["0"], None),
        ("send", "B", n, "burn(uint256)", ["0"], None),
        ("call", "A", n, "tokenURI(uint256)", ["0"], None),
        ("call", "A", n, "getApproved(uint256)", ["0"], None),
        *enumerate_all(5),
        # Royalties: the default, a token's own, both validated, then reset and deleted.
        ("call", "A", n, royalty, ["1", str(E18)], None),
        ("send", "A", n, set_token, ["1", ADDR["B"], "1000"], None),
        ("call", "A", n, royalty, ["1", str(E18)], None),
        ("call", "A", n, royalty, ["2", str(E18)], None),
        ("call", "A", n, royalty, ["1", MAX], None),
        ("send", "A", n, set_token, ["1", ADDR["B"], "10001"], None),
        ("send", "A", n, set_token, ["1", ZERO, "100"], None),
        ("send", "A", n, set_token, ["2", "$receiver", "10000"], None),
        ("call", "A", n, royalty, ["2", "12345"], None),
        ("send", "B", n, set_token, ["1", ADDR["B"], "1"], None),
        ("send", "A", n, set_default, [ADDR["B"], "10001"], None),
        ("send", "A", n, set_default, [ZERO, "1"], None),
        ("send", "A", n, set_default, [ADDR["B"], "250"], None),
        ("send", "B", n, set_default, [ADDR["B"], "250"], None),
        ("call", "A", n, royalty, ["4", "999"], None),
        ("send", "A", n, "resetTokenRoyalty(uint256)", ["1"], None),
        ("send", "B", n, "resetTokenRoyalty(uint256)", ["1"], None),
        ("call", "A", n, royalty, ["1", str(E18)], None),
        ("send", "A", n, "deleteDefaultRoyalty()", [], None),
        ("send", "B", n, "deleteDefaultRoyalty()", [], None),
        ("call", "A", n, royalty, ["1", str(E18)], None),
        ("call", "A", n, royalty, ["2", str(E18)], None),
        # Pausing stops every ownership change, but not approvals.
        ("send", "B", n, "pause()", [], None),
        ("send", "A", n, "pause()", [], None),
        ("send", "A", n, "pause()", [], None),
        ("call", "A", n, "paused()", [], None),
        ("send", "A", n, xfer, [ADDR["A"], ADDR["B"], "1"], None),
        # Checked before the pause: the receiver.
        ("send", "A", n, xfer, [ADDR["A"], ZERO, "1"], None),
        ("send", "A", n, mint, [ADDR["A"], "p.json"], None),
        ("send", "A", n, "burn(uint256)", ["1"], None),
        ("send", "A", n, "approve(address,uint256)", [ADDR["B"], "1"], None),
        ("send", "A", n, "unpause()", [], None),
        ("send", "A", n, "unpause()", [], None),
        ("send", "B", n, xfer, [ADDR["A"], ADDR["B"], "1"], None),
        ("send", "A", n, mint, [ADDR["A"], "after.json"], None),
        ("call", "A", n, "tokenURI(uint256)", ["6"], None),
        ("send", "A", n, "transferOwnership(address)", [ZERO], None),
        ("send", "A", n, "transferOwnership(address)", [ADDR["B"]], None),
        ("send", "A", n, mint, [ADDR["A"], "old.json"], None),
        ("send", "B", n, mint, [ADDR["A"], ""], None),
        ("call", "A", n, "tokenURI(uint256)", ["7"], None),
        ("send", "B", n, "renounceOwnership()", [], None),
        ("call", "A", n, "owner()", [], None),
        ("send", "B", n, set_default, [ADDR["B"], "1"], None),
        *enumerate_all(7),
        ("call", "A", n, "balanceOf(address)", [ADDR["A"]], None),
        ("call", "A", n, "balanceOf(address)", [ADDR["B"]], None),
        ("call", "A", n, "balanceOf(address)", ["$receiver"], None),
        ("send", "A", n, raw(set_default, word(int(ADDR["A"], 16)), word(2**96)), [], None),
    ]


def uniswap_v2_steps():
    """Uniswap v2-core on two bench tokens: pairs, liquidity, swaps both ways, burns, skim
    and sync, the protocol fee, the LP token with a permit, and each `require`'s reason.
    Pairs are CREATE2-deployed from each build's own code, so later steps reach them, and
    the pair's tokens in order, through `bind`."""
    a, b = ADDR["A"], ADDR["B"]
    create = "createPair(address,address)"
    swap = "swap(uint256,uint256,address,bytes)"
    permit = "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)"
    pay = lambda who, token, amount: ("send", who, token, "transfer(address,uint256)", ["$pair", str(amount)], None)
    both = lambda kind, who, role, sig, args: [(k, who, role, sig, args, None) for k in ("call", "send")] if kind == "both" else [(kind, who, role, sig, args, None)]
    view = lambda role, sig, *args: ("call", "A", role, sig, list(args), None)

    def out(amount_in, reserve_in, reserve_out):
        """UniswapV2Library.getAmountOut: the most a swap can take out for `amount_in`."""
        with_fee = amount_in * 997
        return with_fee * reserve_out // (reserve_in * 1000 + with_fee)

    def signed(owner, spender, value, nonce, deadline, signer=None):
        """`permit`'s arguments, signed by `signer` over each build's own domain."""
        def args(roles):
            typehash = keccak(b"Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
            fields = word(int(ADDR[owner], 16)) + word(int(ADDR[spender], 16)) + word(value) + word(nonce) + word(deadline)
            digest = keccak(b"\x19\x01" + bytes.fromhex(roles["domain"][2:]) + keccak(typehash + bytes.fromhex(fields)))
            sig = run(["cast", "wallet", "sign", "--no-hash", "--private-key", KEYS[signer or owner],
                       "0x" + digest.hex()]).stdout.strip()[2:]
            return [ADDR[owner], ADDR[spender], str(value), str(deadline), str(int(sig[128:], 16)),
                    "0x" + sig[:64], "0x" + sig[64:128]]
        return args

    r0, r1 = 1000 * E18, 4000 * E18
    in0 = 10 * E18
    out1 = out(in0, r0, r1)
    later = str(2**40)
    return [
        *[("send", "A", t, "mint(address,uint256)", [who, str(10_000 * E18)], None)
          for t in ("tka", "tkb") for who in (a, b)],
        view("factory", "feeTo()"),
        view("factory", "feeToSetter()"),
        view("factory", "allPairsLength()"),
        *both("both", "A", "factory", create, ["$tka", "$tka"]),
        *both("both", "A", "factory", create, ["$tka", ZERO]),
        *both("call", "A", "factory", create, [ZERO, "$tkb"]),
        # `createPair` returns where the pair lands, before it is there.
        ("bind", "pair", "factory", create, ["$tka", "$tkb"]),
        ("send", "B", "factory", create, ["$tka", "$tkb"], None),
        *both("both", "A", "factory", create, ["$tkb", "$tka"]),
        view("factory", "getPair(address,address)", "$tka", "$tkb"),
        view("factory", "getPair(address,address)", "$tkb", "$tka"),
        view("factory", "allPairs(uint256)", "0"),
        # Past the end, Solidity's getter reverts with no data, and Lithe's index panics.
        ("send", "A", "factory", "allPairs(uint256)", ["1"], None),
        view("factory", "allPairsLength()"),
        ("bind", "domain", "pair", "DOMAIN_SEPARATOR()", []),
        ("bind", "t0", "pair", "token0()", []),
        ("bind", "t1", "pair", "token1()", []),
        *[view("pair", v) for v in ["name()", "symbol()", "decimals()", "factory()", "MINIMUM_LIQUIDITY()",
                                    "PERMIT_TYPEHASH()", "DOMAIN_SEPARATOR()", "getReserves()", "totalSupply()"]],
        *both("both", "B", "pair", "initialize(address,address)", ["$t0", "$t1"]),
        # The first mint's square root falls short of the locked minimum: a panic.
        *both("call", "A", "pair", "mint(address)", [a]),
        pay("A", "t0", r0),
        pay("A", "t1", r1),
        ("send", "A", "pair", "mint(address)", [a], None),
        view("pair", "getReserves()"),
        view("pair", "totalSupply()"),
        view("pair", "balanceOf(address)", a),
        view("pair", "balanceOf(address)", ZERO),
        *both("both", "A", "pair", "mint(address)", [a]),
        ("wait", 3600),
        *both("call", "B", "pair", swap, ["0", "0", b, "0x"]),
        *both("call", "B", "pair", swap, ["0", str(r1), b, "0x"]),
        *both("call", "B", "pair", swap, ["0", "1", "$t0", "0x"]),
        *both("call", "B", "pair", swap, ["0", "1", "$t1", "0x"]),
        *both("call", "B", "pair", swap, ["1", "0", b, "0x"]),
        # A callback to an account without code.
        *both("call", "B", "pair", swap, ["0", "1", b, "0x01"]),
        pay("B", "t0", in0),
        *both("both", "B", "pair", swap, ["0", str(out1 + 1), b, "0x"]),
        ("send", "B", "pair", swap, ["0", str(out1), b, "0x"], None),
        view("pair", "getReserves()"),
        view("pair", "price0CumulativeLast()"),
        ("wait", 600),
        pay("A", "t1", 100 * E18),
        ("send", "A", "pair", swap, [str(20 * E18), "0", a, "0x"], None),
        ("wait", 60),
        # Both tokens out at once.
        pay("B", "t0", 40 * E18),
        ("send", "B", "pair", swap, [str(E18), str(100 * E18), b, "0x"], None),
        view("pair", "getReserves()"),
        view("pair", "price0CumulativeLast()"),
        view("pair", "price1CumulativeLast()"),
        # The LP token.
        ("send", "A", "pair", "approve(address,uint256)", [b, str(100 * E18)], None),
        ("send", "B", "pair", "transferFrom(address,address,uint256)", [a, b, str(30 * E18)], None),
        view("pair", "allowance(address,address)", a, b),
        *both("both", "B", "pair", "transferFrom(address,address,uint256)", [a, b, str(100 * E18)]),
        ("send", "A", "pair", "approve(address,uint256)", [b, MAX], None),
        ("send", "B", "pair", "transferFrom(address,address,uint256)", [a, b, str(E18)], None),
        view("pair", "allowance(address,address)", a, b),
        ("send", "A", "pair", "transfer(address,uint256)", [b, str(E18)], None),
        view("pair", "nonces(address)", a),
        ("send", "B", "pair", permit, signed("A", "B", 5 * E18, 0, 2**40), None),
        view("pair", "nonces(address)", a),
        view("pair", "allowance(address,address)", a, b),
        # The same signature again, one long past its deadline, and one by someone else.
        *both("call", "B", "pair", permit, signed("A", "B", 5 * E18, 0, 2**40)),
        *both("call", "B", "pair", permit, signed("A", "B", 5 * E18, 1, 1)),
        *both("both", "B", "pair", permit, signed("A", "B", 5 * E18, 1, 2**40, "B")),
        # Liquidity out.
        ("send", "A", "pair", "transfer(address,uint256)", ["$pair", str(100 * E18)], None),
        ("send", "A", "pair", "burn(address)", [a], None),
        *both("both", "A", "pair", "burn(address)", [a]),
        view("pair", "getReserves()"),
        # Skim a donation, then sync to one.
        pay("A", "t0", 5 * E18),
        ("send", "B", "pair", "skim(address)", [b], None),
        pay("A", "t1", 3 * E18),
        ("send", "B", "pair", "sync()", [], None),
        view("pair", "getReserves()"),
        # The protocol fee: on, grown by a swap, minted with the next liquidity, then off.
        *both("both", "B", "factory", "setFeeTo(address)", [b]),
        ("send", "A", "factory", "setFeeTo(address)", [b], None),
        view("factory", "feeTo()"),
        pay("A", "t0", 100 * E18),
        pay("A", "t1", 400 * E18),
        ("send", "A", "pair", "mint(address)", [a], None),
        view("pair", "kLast()"),
        ("wait", 120),
        pay("B", "t1", 200 * E18),
        ("send", "B", "pair", swap, [str(40 * E18), "0", b, "0x"], None),
        pay("A", "t0", 10 * E18),
        pay("A", "t1", 40 * E18),
        ("send", "A", "pair", "mint(address)", [a], None),
        view("pair", "balanceOf(address)", b),
        view("pair", "kLast()"),
        ("send", "A", "factory", "setFeeTo(address)", [ZERO], None),
        pay("A", "t0", 10 * E18),
        pay("A", "t1", 40 * E18),
        ("send", "A", "pair", "mint(address)", [a], None),
        view("pair", "kLast()"),
        *both("both", "B", "factory", "setFeeToSetter(address)", [b]),
        ("send", "A", "factory", "setFeeToSetter(address)", [b], None),
        *both("both", "A", "factory", "setFeeTo(address)", [a]),
        ("send", "B", "factory", "setFeeTo(address)", [a], None),
        view("factory", "feeToSetter()"),
        # A token that refuses a transfer: `TRANSFER_FAILED`, whatever its own reason.
        ("send", "A", "tka", "pause()", [], None),
        ("send", "A", "pair", "transfer(address,uint256)", ["$pair", str(10 * E18)], None),
        *both("both", "A", "pair", "burn(address)", [a]),
        *both("both", "A", "pair", "skim(address)", [a]),
        ("send", "A", "tka", "unpause()", [], None),
        ("send", "A", "pair", "burn(address)", [a], None),
        # A second pair, whose other token is any address.
        ("bind", "pair2", "factory", create, ["$tkb", "$factory"]),
        ("send", "A", "factory", create, ["$tkb", "$factory"], None),
        ("bind", "domain2", "pair2", "DOMAIN_SEPARATOR()", []),
        view("factory", "allPairs(uint256)", "1"),
        view("factory", "allPairsLength()"),
        view("factory", "getPair(address,address)", "$factory", "$tkb"),
        view("pair2", "getReserves()"),
        view("pair", "getReserves()"),
        view("pair", "price0CumulativeLast()"),
        view("pair", "price1CumulativeLast()"),
        view("pair", "totalSupply()"),
        view("t0", "balanceOf(address)", "$pair"),
        view("t1", "balanceOf(address)", "$pair"),
    ]


# A's first deployment: the token of a suite that deploys it first.
FIRST = "0x5FbDB2315678afecb367f032d93F642f64180aa3"


def sign_typed(name, token, struct_hash):
    """Account A's EIP-712 signature over a struct for a token's version-1 domain: `v`, `r`, `s`."""
    domain = cast("keccak", cast(
        "abi-encode", "f(bytes32,bytes32,bytes32,uint256,address)",
        cast("keccak", "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
        cast("keccak", name), cast("keccak", "1"), "31337", token))
    digest = cast("keccak", "0x1901" + domain[2:] + struct_hash[2:])
    sig = cast("wallet", "sign", "--no-hash", "--private-key", KEYS["A"], digest)
    return [str(int(sig[130:132], 16)), "0x" + sig[2:66], "0x" + sig[66:130]]


def permit_args(name, token, spender, value, nonce, deadline):
    """`permit` arguments for A's signed approval of `spender`."""
    struct = cast("keccak", cast(
        "abi-encode", "f(bytes32,address,address,uint256,uint256,uint256)",
        cast("keccak", "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"),
        ADDR["A"], spender, str(value), str(nonce), str(deadline)))
    return [ADDR["A"], spender, str(value), str(deadline), *sign_typed(name, token, struct)]


def erc20_full_steps():
    """The wizard token with every add-on: roles, the cap, votes and their history, flash
    loans through a borrower contract, and permits and delegations signed by account A."""
    t, f = "token", "borrower"
    token = FIRST
    minter, pauser = cast("keccak", "MINTER_ROLE"), cast("keccak", "PAUSER_ROLE")
    loan = "flashLoan(address,address,uint256,bytes)"
    xfer = "transfer(address,uint256)"
    steps = []
    # The block each send lands in: the two deployments take blocks 1 and 2.
    block = [2]

    def send(sender, sig, args, role=t):
        steps.append(("send", sender, role, sig, args, None))
        block[0] += 1

    def call(sig, args=(), role=t):
        steps.append(("call", "A", role, sig, list(args), None))

    signed = lambda struct_hash: sign_typed("Bench Governance Token", token, struct_hash)
    permit = lambda value, nonce, deadline: permit_args("Bench Governance Token", token, ADDR["B"], value, nonce, deadline)

    def delegation(delegatee, nonce, expiry):
        struct = cast("keccak", cast(
            "abi-encode", "f(bytes32,address,uint256,uint256)",
            cast("keccak", "Delegation(address delegatee,uint256 nonce,uint256 expiry)"),
            delegatee, str(nonce), str(expiry)))
        return [delegatee, str(nonce), str(expiry), *signed(struct)]

    for view in ["name()", "symbol()", "decimals()", "totalSupply()", "cap()", "paused()",
                 "DEFAULT_ADMIN_ROLE()", "MINTER_ROLE()", "PAUSER_ROLE()", "clock()",
                 "CLOCK_MODE()", "DOMAIN_SEPARATOR()", "eip712Domain()"]:
        call(view)
    for i in ["0x7965db0b", "0x01ffc9a7", "0x36372b07", "0xffffffff"]:
        call("supportsInterface(bytes4)", [i])
    call("hasRole(bytes32,address)", [minter, ADDR["A"]])
    call("hasRole(bytes32,address)", [minter, ADDR["B"]])
    call("getRoleAdmin(bytes32)", [minter])
    call("maxFlashLoan(address)", ["$token"])
    call("maxFlashLoan(address)", [ADDR["B"]])
    call("flashFee(address,uint256)", ["$token", str(E18)])
    call("flashFee(address,uint256)", [ADDR["B"], "1"])

    # Minting: the role, the receiver, and the cap.
    send("A", "mint(address,uint256)", [ADDR["A"], str(1000 * E18)])
    send("B", "mint(address,uint256)", [ADDR["B"], "5"])
    send("A", "mint(address,uint256)", [ZERO, "1"])
    send("A", "mint(address,uint256)", [ADDR["B"], str(10**24)])
    # Votes count only once delegated, and follow every balance change after.
    call("getVotes(address)", [ADDR["A"]])
    send("A", "delegate(address)", [ADDR["A"]])
    delegated = block[0]
    send("A", xfer, [ADDR["B"], str(100 * E18)])
    send("B", "delegate(address)", [ADDR["B"]])
    send("B", xfer, [ADDR["A"], str(10 * E18)])
    send("A", xfer, [ZERO, "1"])
    send("B", xfer, [ADDR["A"], str(10**30)])
    for _ in range(6):
        send("A", xfer, [ADDR["B"], str(E18)])
    many = block[0]
    send("A", "mint(address,uint256)", [ADDR["B"], str(50 * E18)])
    minted = block[0]
    send("B", "burn(uint256)", [str(5 * E18)])
    send("B", "burn(uint256)", [str(10**30)])
    send("A", "approve(address,uint256)", [ADDR["B"], str(20 * E18)])
    send("B", "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], str(5 * E18)])
    send("B", "transferFrom(address,address,uint256)", [ADDR["A"], ADDR["B"], str(100 * E18)])
    send("B", "burnFrom(address,uint256)", [ADDR["A"], str(5 * E18)])
    send("A", "burnFrom(address,uint256)", [ADDR["B"], "1"])
    send("A", "delegate(address)", [ADDR["B"]])
    send("A", "delegate(address)", [ZERO])
    send("A", "delegate(address)", [ADDR["A"]])
    for who in [ADDR["A"], ADDR["B"]]:
        call("getVotes(address)", [who])
        call("delegates(address)", [who])
        call("numCheckpoints(address)", [who])
        for pos in ["0", "1", "7", "99"]:
            call("checkpoints(address,uint32)", [who, pos])
        # Before, at, and between checkpoints, and a lookup that is not yet past.
        for at in [1, delegated - 1, delegated, delegated + 3, many - 2, many, minted, block[0] - 1, block[0] + 5]:
            call("getPastVotes(address,uint256)", [who, str(at)])
    for at in [1, delegated, minted, block[0] - 1, block[0] + 5]:
        call("getPastTotalSupply(uint256)", [str(at)])

    # Pausing, and roles granted, revoked, and renounced.
    send("B", "pause()", [])
    send("B", "grantRole(bytes32,address)", [pauser, ADDR["B"]])
    send("A", "grantRole(bytes32,address)", [pauser, ADDR["B"]])
    send("A", "grantRole(bytes32,address)", [pauser, ADDR["B"]])
    send("B", "pause()", [])
    send("B", "pause()", [])
    call("paused()")
    send("A", xfer, [ADDR["B"], "1"])
    send("A", "mint(address,uint256)", [ADDR["A"], "1"])
    send("A", loan, ["$borrower", "$token", str(E18), "0x"])
    send("A", "approve(address,uint256)", [ADDR["B"], "7"])
    send("B", "delegate(address)", [ADDR["A"]])
    send("A", "unpause()", [])
    send("B", "unpause()", [])
    send("B", "unpause()", [])
    send("A", "revokeRole(bytes32,address)", [pauser, ADDR["B"]])
    send("B", "renounceRole(bytes32,address)", [minter, ADDR["A"]])
    send("B", "pause()", [])

    # Flash loans: repaid, too large, of another token, over the cap, and borrowers that
    # answer wrong, don't approve, refuse, or aren't contracts at all.
    send("A", loan, ["$borrower", "$token", str(1000 * E18), "0x" + "ab" * 40])
    call("totalSupply()")
    call("balanceOf(address)", ["$borrower"])
    call("allowance(address,address)", ["$borrower", "$token"])
    send("A", loan, ["$borrower", "$token", MAX, "0x"])
    send("A", loan, ["$borrower", ADDR["B"], "0", "0x"])
    send("A", loan, ["$borrower", ADDR["B"], "1", "0x"])
    send("A", loan, ["$borrower", "$token", str(10**24), "0x"])
    send("A", loan, [ZERO, "$token", "1", "0x"])
    send("A", loan, [ADDR["B"], "$token", "1", "0x"])
    for mode in ["1", "2", "3"]:
        send("A", "set_mode(uint256)", [mode], role=f)
        call(loan, ["$borrower", "$token", "7", "0x"])
        send("A", loan, ["$borrower", "$token", "7", "0x"])
    send("A", "set_mode(uint256)", ["0"], role=f)
    send("B", loan, ["$borrower", "$token", "7", "0x1234"])

    # Signed approvals and delegations: used, replayed, and expired.
    send("B", "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", permit(123, 0, 3_000_000_000))
    call("allowance(address,address)", [ADDR["A"], ADDR["B"]])
    call("nonces(address)", [ADDR["A"]])
    send("B", "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", permit(123, 0, 3_000_000_000))
    send("B", "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)", permit(5, 1, 1))
    send("B", "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", delegation(ADDR["B"], 1, 3_000_000_000))
    call("delegates(address)", [ADDR["A"]])
    send("B", "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", delegation(ADDR["B"], 1, 3_000_000_000))
    send("B", "delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)", delegation(ADDR["B"], 2, 1))
    call("nonces(address)", [ADDR["A"]])

    send("A", "renounceRole(bytes32,address)", [minter, ADDR["A"]])
    send("A", "mint(address,uint256)", [ADDR["A"], "1"])
    for view in ["totalSupply()", "getVotes(address)", "balanceOf(address)"]:
        for who in [ADDR["A"], ADDR["B"]]:
            call(view, [] if view == "totalSupply()" else [who])
    send("A", raw(xfer, word(int(ADDR["B"], 16))), [])
    return steps


PERMIT2 = "0x000000000022D473030F116dDEE9F6B43aC78BA3"


def solady_erc20_steps():
    """Solady's token: no zero-address checks, a total supply that must not overflow, the
    fixed Permit2 allowance, and permits signed by account A."""
    t, a, b = "token", ADDR["A"], ADDR["B"]
    xfer, xfer_from = "transfer(address,uint256)", "transferFrom(address,address,uint256)"
    sig = "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)"
    permit = lambda spender, value, nonce, deadline: permit_args("Solady Token", FIRST, spender, value, nonce, deadline)
    send = lambda sender, f, args: ("send", sender, t, f, args, None)
    call = lambda f, args=(): ("call", "A", t, f, list(args), None)
    signed = permit(b, 123, 0, 3_000_000_000)
    return [
        *[call(v) for v in ["name()", "symbol()", "decimals()", "totalSupply()", "DOMAIN_SEPARATOR()"]],
        send("A", "mint(address,uint256)", [a, str(1000 * E18)]),
        send("B", "mint(address,uint256)", [b, "5"]),
        send("A", "mint(address,uint256)", [ZERO, "1"]),
        send("A", "mint(address,uint256)", [a, MAX]),
        send("A", xfer, [b, str(100 * E18)]),
        call(xfer, [b, "1"]),
        send("A", xfer, [ZERO, "1"]),
        send("A", xfer, [a, "7"]),
        send("A", xfer, [b, "0"]),
        send("B", xfer, [a, str(10**30)]),
        send("A", "approve(address,uint256)", [b, str(500 * E18)]),
        send("A", "approve(address,uint256)", [ZERO, "1"]),
        call("allowance(address,address)", [a, b]),
        send("B", xfer_from, [a, b, str(200 * E18)]),
        send("B", xfer_from, [a, b, str(400 * E18)]),
        send("B", xfer_from, [a, ZERO, "1"]),
        send("A", "approve(address,uint256)", [b, MAX]),
        send("B", xfer_from, [a, b, "1"]),
        call("allowance(address,address)", [a, b]),
        send("B", xfer_from, [a, b, str(10**30)]),
        # Permit2 may always spend, and its allowance can't be lowered.
        call("allowance(address,address)", [a, PERMIT2]),
        send("A", "approve(address,uint256)", [PERMIT2, "5"]),
        send("A", "approve(address,uint256)", [PERMIT2, MAX]),
        send("B", "burn(uint256)", [str(10 * E18)]),
        send("B", "burn(uint256)", [str(10**30)]),
        # Signed approvals: used, replayed, expired, for Permit2, and by the wrong owner.
        send("B", sig, signed),
        call("allowance(address,address)", [a, b]),
        call("nonces(address)", [a]),
        send("B", sig, signed),
        send("B", sig, permit(b, 5, 1, 1)),
        send("B", sig, permit(PERMIT2, 5, 1, 3_000_000_000)),
        send("B", sig, [b, *permit(b, 5, 1, 3_000_000_000)[1:]]),
        send("B", sig, [ZERO, b, "5", "3000000000", "27", "0x" + "11" * 32, "0x" + "22" * 32]),
        send("B", sig, permit(b, 9, 1, 3_000_000_000)),
        call("nonces(address)", [a]),
        call("totalSupply()"),
        *[call("balanceOf(address)", [who]) for who in [a, b, ZERO]],
        send("A", raw(xfer, word(int(b, 16))), []),
    ]


def solady_erc721_steps():
    """Solady's NFT: its errors and order of checks, operators, burns by approved accounts,
    and safe transfers to a receiver in each of its modes, and to a contract without the hook."""
    n, a, b = "nft", ADDR["A"], ADDR["B"]
    xfer = "transferFrom(address,address,uint256)"
    safe = "safeTransferFrom(address,address,uint256)"
    safe_data = "safeTransferFrom(address,address,uint256,bytes)"
    mint, safe_mint = "mint(address,uint256)", "safeMint(address,uint256,bytes)"
    send = lambda sender, f, args, value=None: ("send", sender, n, f, args, value)
    call = lambda f, args=(): ("call", "A", n, f, list(args), None)
    mode = lambda m: ("send", "A", "receiver", "set_mode(uint256)", [str(m)], None)
    return [
        call("name()"),
        call("symbol()"),
        *[call("supportsInterface(bytes4)", [i]) for i in ["0x80ac58cd", "0x5b5e139f", "0x01ffc9a7", "0xffffffff"]],
        send("A", mint, [a, "1"]),
        send("B", mint, [b, "2"]),
        send("A", mint, [ZERO, "3"]),
        send("A", mint, [b, "1"]),
        send("A", safe_mint, ["$receiver", "3", "0x" + "ab" * 40]),
        send("A", safe_mint, [a, "4", "0x"]),
        send("A", safe_mint, [a, "5", "0x1234"]),
        send("A", mint, [a, "6"]),
        send("A", safe_mint, ["$nft", "7", "0x"]),
        call("balanceOf(address)", [a]),
        call("balanceOf(address)", [ZERO]),
        call("ownerOf(uint256)", ["1"]),
        call("ownerOf(uint256)", ["99"]),
        call("tokenURI(uint256)", ["1"]),
        call("tokenURI(uint256)", ["4"]),
        call("tokenURI(uint256)", ["99"]),
        send("A", "approve(address,uint256)", [b, "1"]),
        call("getApproved(uint256)", ["1"]),
        call("getApproved(uint256)", ["99"]),
        send("B", "approve(address,uint256)", [b, "4"]),
        send("A", "approve(address,uint256)", [b, "99"]),
        send("B", xfer, [a, b, "1"]),
        send("B", xfer, [a, b, "1"]),
        send("B", xfer, [b, ZERO, "1"]),
        send("B", xfer, [a, b, "4"]),
        send("A", xfer, [a, b, "99"]),
        send("B", "setApprovalForAll(address,bool)", [a, "true"]),
        send("B", "setApprovalForAll(address,bool)", [ZERO, "true"]),
        call("isApprovedForAll(address,address)", [b, a]),
        # An operator moves and approves the owner's tokens, and may pay.
        send("A", xfer, [b, a, "2"], "1"),
        send("A", "approve(address,uint256)", [a, "1"]),
        send("A", safe, [a, b, "2"]),
        send("A", safe_data, [a, "$receiver", "4", "0x" + "ab" * 40]),
        send("A", safe_data, [a, "$receiver", "5", "0x1234"]),
        mode(1),
        send("A", safe, [a, "$receiver", "6"]),
        mode(2),
        # The receiver's own reason passes through unchanged.
        call(safe, [a, "$receiver", "6"]),
        send("A", safe, [a, "$receiver", "6"]),
        mode(0),
        call(safe, [a, "$nft", "6"]),
        send("A", safe, [a, "$nft", "6"]),
        send("A", "burn(uint256)", ["1"]),
        send("B", "burn(uint256)", ["1"]),
        send("B", "burn(uint256)", ["6"]),
        send("A", "burn(uint256)", ["6"]),
        call("getApproved(uint256)", ["1"]),
        send("A", mint, [a, "1"]),
        *[call("balanceOf(address)", [who]) for who in [a, b, "$receiver"]],
    ]


def solady_erc1155_steps():
    """Solady's multi-token: its errors and order of checks, batches that always log
    `TransferBatch`, burns by operators, and a receiver in each of its modes and a contract
    that has no hook. Solady walks a batch from its end, so a batch that fails does so at
    both ends, and neither side's order costs it the other's writes."""
    m, a, b = "mt", ADDR["A"], ADDR["B"]
    mint = "mint(address,uint256,uint256,bytes)"
    mint_batch = "mintBatch(address,uint256[],uint256[],bytes)"
    safe = "safeTransferFrom(address,address,uint256,uint256,bytes)"
    safe_batch = "safeBatchTransferFrom(address,address,uint256[],uint256[],bytes)"
    burn = "burn(address,uint256,uint256)"
    burn_batch = "burnBatch(address,uint256[],uint256[])"
    batch_of = "balanceOfBatch(address[],uint256[])"
    long = "0x" + "ab" * 100
    send = lambda sender, f, args: ("send", sender, m, f, args, None)
    call = lambda f, args: ("call", "A", m, f, args, None)
    mode = lambda n: ("send", "A", "r1155", "set_mode(uint256)", [str(n)], None)
    return [
        call("uri(uint256)", ["1"]),
        *[call("supportsInterface(bytes4)", [i])
          for i in ["0xd9b67a26", "0x0e89341c", "0x01ffc9a7", "0x80ac58cd", "0xffffffff"]],
        send("A", mint, [a, "1", "100", "0x"]),
        send("B", mint, [b, "2", "50", "0x1234"]),
        send("A", mint, [ZERO, "1", "1", "0x"]),
        send("A", mint, ["$r1155", "3", "10", long]),
        send("A", mint, ["$plain", "3", "1", "0x"]),
        send("A", mint, [a, "9", MAX, "0x"]),
        send("A", mint, [a, "9", "1", "0x"]),
        send("A", mint_batch, [a, "[1,2,3]", "[10,20,30]", "0x"]),
        # Repeated ids, and a long payload to the batch hook.
        send("A", mint_batch, ["$r1155", "[4,5,4]", "[1,2,3]", long]),
        send("A", mint_batch, ["$r1155", "[7]", "[1]", "0x"]),
        send("A", mint_batch, [a, "[]", "[]", "0x"]),
        send("A", mint_batch, [a, "[1,2]", "[1]", "0x"]),
        send("A", mint_batch, [ZERO, "[1]", "[1]", "0x"]),
        send("A", mint_batch, [a, "[9,8,9]", "[1,1,1]", "0x"]),
        send("A", mint_batch, ["$plain", "[1,2]", "[1,1]", "0x"]),
        mode(1),
        send("A", mint, ["$r1155", "3", "1", "0x"]),
        send("A", mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"]),
        mode(2),
        # The receiver's own reason passes through unchanged.
        call(mint, ["$r1155", "3", "1", "0x"]),
        call(mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"]),
        send("A", mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"]),
        mode(3),
        call(mint, ["$r1155", "3", "1", "0x"]),
        send("A", mint_batch, ["$r1155", "[3,4]", "[1,1]", "0x"]),
        mode(0),
        call("balanceOf(address,uint256)", [a, "1"]),
        call("balanceOf(address,uint256)", ["$r1155", "4"]),
        call(batch_of, [f"[{a},{b},{a},{a}]", "[1,2,3,99]"]),
        call(batch_of, [f"[{a},{b}]", "[1]"]),
        call(batch_of, ["[]", "[]"]),
        send("A", safe, [a, b, "1", "5", "0x"]),
        send("B", safe, [a, b, "1", "5", "0x"]),
        send("A", safe, [a, b, "1", "1000", "0x"]),
        send("A", safe, [a, ZERO, "1", "1", "0x"]),
        send("A", safe, [ZERO, b, "1", "1", "0x"]),
        send("A", safe, [a, a, "1", "1", "0x"]),
        send("A", safe, [a, "$r1155", "1", "5", long]),
        send("A", safe, [a, "$plain", "1", "5", "0x"]),
        send("A", "setApprovalForAll(address,bool)", [b, "true"]),
        send("A", "setApprovalForAll(address,bool)", [ZERO, "true"]),
        call("isApprovedForAll(address,address)", [a, b]),
        send("B", safe, [a, b, "1", "5", "0x"]),
        send("A", safe_batch, [a, b, "[1,2,3]", "[1,2,3]", "0x"]),
        send("A", safe_batch, [a, b, "[1,1,2]", "[1,2,3]", "0x1234"]),
        send("A", safe_batch, [a, b, "[1,2]", "[1]", "0x"]),
        send("A", safe_batch, [a, b, "[1,2]", "[1000,1000]", "0x"]),
        # Repeated ids draw on one balance.
        send("A", safe_batch, [a, b, "[3,3]", "[20,20]", "0x"]),
        send("A", safe_batch, [a, ZERO, "[1]", "[1]", "0x"]),
        send("B", safe_batch, [b, a, "[2]", "[1]", "0x"]),
        send("A", safe_batch, [b, a, "[2]", "[1]", "0x"]),
        send("A", safe_batch, [a, "$r1155", "[1,3,1]", "[1,1,1]", long]),
        send("A", safe_batch, [a, "$plain", "[1,3]", "[1,1]", "0x"]),
        send("A", burn, [a, "1", "1"]),
        send("B", burn, [a, "1", "1"]),
        send("A", "setApprovalForAll(address,bool)", [b, "false"]),
        send("B", burn, [a, "1", "1"]),
        send("A", burn, [a, "1", "1000"]),
        send("A", burn, [ZERO, "1", "0"]),
        send("A", burn_batch, [a, "[1,2,3]", "[1,1,1]"]),
        send("A", burn_batch, [a, "[1,1]", "[1,1]"]),
        send("A", burn_batch, [a, "[1,2]", "[1]"]),
        send("A", burn_batch, [a, "[1,2]", "[1000,1000]"]),
        send("B", burn_batch, [a, "[1]", "[1]"]),
        call(batch_of, [f"[{a},{b},{a},{b},{a}]", "[1,1,2,2,9]"]),
        call("balanceOf(address,uint256)", ["$r1155", "1"]),
        send("A", raw(batch_of, word(0x40), word(0x60), word(1)), []),
    ]


def cast(*args):
    return subprocess.run(["cast", *args], capture_output=True, text=True, check=True).stdout.strip()


def blobs(*items):
    """The ABI encoding of a `bytes[]` value, as `abi.encode` lays it out."""
    head, tail = word(len(items)), ""
    for item in items:
        head += word(32 * len(items) + len(tail) // 2)
        tail += word(len(item) // 2) + item + "00" * (-(len(item) // 2) % 32)
    return "0x" + word(0x20) + head + tail


SUITES = {
    # Lists of strings through query and `defer`, and a payload decoded by a contract
    # another contract calls: no calldata floor price hides that call's gas.
    "relay": {
        "deploy": [("texts", "texts"), ("relay", "relay")],
        "steps": [
            ("send", "A", "relay", "ask(address,string[])", ["$texts", "[" + LONG + ",hi,]"], None),
            ("call", "A", "relay", "names()", [], None),
            ("send", "A", "relay", "send(address,string[])", ["$texts", "[x," + LONG + "]"], None),
            ("call", "A", "relay", "kept()", [], None),
            ("send", "A", "relay", "unpack(address,bytes)", ["$texts", blobs("ab" * 2048, "cd" * 2048)], None),
            ("send", "A", "relay", "unpack(address,bytes)", ["$texts", blobs("ab" * 16384, "cd" * 16384)], None),
            ("call", "A", "relay", "count()", [], None),
            ("send", "A", "relay", "unpack(address,bytes)", ["$texts", "0x" + word(0x20) + word(1) + word(0x1000)], None),
        ],
    },
    # One contract reaching another only through raw calls: calldata built with
    # `Abi.encode_call`, the raw answer decoded, and a refusal's payload read from raw
    # revert data. No calldata floor price hides the inner call's gas.
    "dial": {
        "deploy": [("book", "book"), ("dialer", "dialer")],
        "steps": [
            ("send", "A", "dialer", "place(address," + ORDER + "[])", ["$book", "[(1,first,[10,20]),(2," + LONG + ",[5])]"], None),
            ("call", "A", "dialer", "ids()", [], None),
            ("call", "A", "dialer", "note(address,uint256)", ["$book", "2"], None),
            ("call", "A", "dialer", "note(address,uint256)", ["$book", "9"], None),
            ("send", "A", "dialer", "place(address," + ORDER + "[])", ["$book", "[(4,x,[1]),(3,y,[])]"], None),
            ("call", "A", "dialer", "refused()", [], None),
            ("call", "A", "dialer", "ids()", [], None),
            # An account with no code answers nothing, which does not decode as a list.
            ("call", "A", "dialer", "place(address," + ORDER + "[])", [ADDR["B"], "[(5,z,[1])]"], None),
        ],
    },
    "registry": {
        "deploy": [("registry", "registry", "(string)", ["registry"])],
        "steps": [(k, s, "registry", sig, a, v) for k, s, sig, a, v in SCENARIOS["registry"]],
    },
    # Constructor arguments decoded together, then a function's lone argument.
    "profile": {
        "deploy": [
            ("profile", "profile", "(string,bytes)", ["", "0x0102"]),
            ("short", "profile", "(string,bytes)", ["alice", "0x"]),
            ("long", "profile", "(string,bytes)", [LONG, "0x" + "ab" * 40]),
        ],
        "steps": [
            *[("call", "A", role, view, [], None)
              for role in ["profile", "short", "long"] for view in ["name()", "avatar()"]],
            ("send", "A", "profile", "set_bio(string)", [""], None),
            ("send", "A", "profile", "set_bio(string)", ["hi"], None),
            ("send", "A", "profile", "set_bio(string)", ["x" * 31], None),
            ("send", "A", "profile", "set_bio(string)", ["x" * 32], None),
            ("send", "A", "profile", "set_bio(string)", [LONG], None),
            ("call", "A", "profile", "bio()", [], None),
            ("send", "A", "profile", raw("set_bio(string)", word(0x20), word(2), "6869" + "ff" * 30), [], None),
            ("call", "A", "profile", "bio()", [], None),
        ],
    },
    "erc20": {"deploy": [("token", "erc20", "(address)", [ADDR["A"]])], "steps": erc20_steps("token")},
    "erc721": {
        "deploy": [("nft", "erc721", "(address)", [ADDR["A"]]), ("receiver", "receiver")],
        "steps": erc721_steps(),
    },
    "erc1155": {
        "deploy": [
            ("mt", "erc1155", "(address)", [ADDR["A"]]),
            ("r1155", "receiver1155"),
            ("plain", "receiver"),
        ],
        "steps": erc1155_steps(),
    },
    "erc721_full": {
        "deploy": [("nft", "erc721_full", "(address)", [ADDR["A"]]), ("receiver", "receiver")],
        "steps": erc721_full_steps(),
    },
    "erc20_full": {
        "deploy": [
            ("token", "erc20_full", "(address,address,address)", [ADDR["A"], ADDR["A"], ADDR["A"]]),
            ("borrower", "flash_borrower"),
        ],
        "steps": erc20_full_steps(),
    },
    # Solady lays out storage by hashes no Lithe map produces, so its token's slots are
    # left out of the storage comparison: `own_layout` names such roles.
    "solady_erc20": {
        "deploy": [("token", "solady_erc20")],
        "steps": solady_erc20_steps(),
        "own_layout": ["token"],
    },
    "solady_erc721": {
        "deploy": [("nft", "solady_erc721"), ("receiver", "receiver")],
        "steps": solady_erc721_steps(),
        "own_layout": ["nft"],
    },
    "solady_erc1155": {
        "deploy": [("mt", "solady_erc1155"), ("r1155", "receiver1155"), ("plain", "receiver")],
        "steps": solady_erc1155_steps(),
        "own_layout": ["mt"],
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
    # The factory creates each pair from its own build's code, so the pairs' addresses
    # differ between builds, and every comparison names them by role.
    "uniswap_v2": {
        "deploy": [
            ("tka", "erc20", "(address)", [ADDR["A"]]),
            ("tkb", "erc20", "(address)", [ADDR["A"]]),
            ("factory", "uniswap_v2_factory", "(address)", [ADDR["A"]]),
        ],
        "steps": uniswap_v2_steps(),
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
    "solady/=" + os.path.join(BENCH, "vendor", "solady", "src") + "/",
]


def solc(path, flags):
    """Creation code, runtime size, and function signatures of the contract `path` defines,
    imports resolved."""
    out = run([SOLC, *flags, "--no-cbor-metadata", *REMAPPINGS, "--allow-paths", BENCH,
               "--combined-json", "abi,bin,bin-runtime", path]).stdout
    contracts = json.loads(out)["contracts"]
    mine = [v for k, v in contracts.items() if k.split(":")[0].endswith(os.path.basename(path))]
    main = max(mine, key=lambda v: len(v["bin-runtime"]))
    return "0x" + main["bin"], len(main["bin-runtime"]) // 2, signatures(main["abi"])


def signatures(abi):
    """Each function's canonical signature, as its selector hashes it."""
    def ty(p):
        if not p["type"].startswith("tuple"):
            return p["type"]
        return "(" + ",".join(ty(c) for c in p["components"]) + ")" + p["type"][len("tuple"):]
    return {f"{e['name']}({','.join(ty(p) for p in e['inputs'])})" for e in abi if e["type"] == "function"}


def push4s(code):
    """Every 4-byte constant the code pushes: where a `supportsInterface` finds its ids."""
    code, i, out = bytes.fromhex(code[2:]), 0, set()
    while i < len(code):
        op = code[i]
        if op == 0x63:
            out.add("0x" + code[i + 1:i + 5].hex())
        i += 1 + (op - 0x5f if 0x60 <= op <= 0x7f else 0)
    return out


def lithe_builds():
    """Each pair's creation code, runtime size, and function signatures, from the
    Foundry-style artifacts."""
    out = tempfile.mkdtemp()
    result = subprocess.run([*LITHE, "compile", BENCH], cwd=out, capture_output=True, text=True)
    if result.returncode:
        sys.exit(result.stderr)
    builds = {}
    for entry in os.listdir(os.path.join(out, "out")):
        folder = os.path.join(out, "out", entry)
        (artifact,) = os.listdir(folder)
        with open(os.path.join(folder, artifact)) as f:
            art = json.load(f)
        runtime = art["deployedBytecode"]["object"]
        builds[entry[: -len(".lithe")]] = (art["bytecode"]["object"], (len(runtime) - 2) // 2, signatures(art["abi"]))
    shutil.rmtree(out)
    return builds


class Chain:
    """One anvil per build. Every chain replays the same transactions from the same
    accounts, so contracts land at the same addresses, and blocks get the same times."""

    def __init__(self):
        # Port 0 lets the OS pick a free port, so runs in other checkouts never share a chain.
        self.log = tempfile.TemporaryFile("w+")
        self.proc = subprocess.Popen(["anvil", "--port", "0"], stdout=self.log,
                                     stderr=subprocess.DEVNULL)
        for _ in range(100):
            self.log.seek(0)
            listening = re.search(r"Listening on (\S+)", self.log.read())
            if listening:
                self.rpc = f"http://{listening[1]}"
                return
            time.sleep(0.1)
        self.stop()
        raise RuntimeError("anvil did not start")

    def stop(self):
        self.proc.send_signal(signal.SIGTERM)
        self.proc.wait()
        self.log.close()

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
            # Keep only the revert data; the rest of the message names the contract. A custom
            # error's message starts with its selector, so take the whole `data:` field.
            text = out.stderr.strip()
            full = re.search(r'data: "(0x[0-9a-fA-F]*)"', text)
            data = full[1] if full else text[text.find("0x"):].split()[0] if "0x" in text else "revert"
            return {"result": "revert " + data.strip('",)'), "gas": None}
        gas = run(["cast", "estimate", *base], check=False)
        return {"result": out.stdout.strip(), "gas": int(gas.stdout) if gas.returncode == 0 else None}

    def answer(self, to, id):
        """`supportsInterface(id)`, without the gas estimate a step records."""
        out = run(["cast", "call", "--rpc-url", self.rpc, to, "supportsInterface(bytes4)(bool)", id], check=False)
        return out.stdout.strip() if out.returncode == 0 else "revert"

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

    # A pair is only a fair comparison when both sides have the same entrypoints.
    mismatches = 0
    for name in pairs:
        for label in SOLC_BUILDS:
            lithe, sol = code[name]["lithe"][2], code[name][label][2]
            if lithe != sol:
                mismatches += 1
                print(f"  INTERFACE MISMATCH {name}: lithe vs {label}")
                for sig in sorted(lithe - sol):
                    print(f"    only lithe: {sig}")
                for sig in sorted(sol - lithe):
                    print(f"    only {label}: {sig}")
    print("\nGas per transaction (lower is better); views are estimates\n")
    for name in wanted:
        suite = suites()[name]
        chains = {b: Chain() for b in order}
        try:
            mismatches += replay(name, suite, code, order, chains)
        finally:
            for chain in chains.values():
                chain.stop()
    if mismatches:
        print(f"{mismatches} behavior mismatches")
        sys.exit(1)
    print("All builds behaved identically and left identical storage.")


def keccak(data):
    try:
        return hashlib.new("keccak-256", data).digest()
    except ValueError:
        return bytes.fromhex(run(["cast", "keccak", "0x" + data.hex()]).stdout.strip()[2:])


def canon(x, bound):
    """`x` with each bound role's value, wherever its hex appears, replaced by the role's
    name: a contract that `CREATE2` deployed lands at a different address in each build."""
    if isinstance(x, dict):
        return {canon(k, bound): canon(v, bound) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [canon(v, bound) for v in x]
    if isinstance(x, str):
        x = x.lower()
        for role, value in bound.items():
            x = x.replace(value[2:].lower(), f"<{role}>")
    return x


def canon_slots(slots, bound, bases):
    """Storage with bound values canonical, and each map entry keyed by a bound address,
    under one of `bases`, named for the role and the map's slot."""
    keyed = {}
    for role, value in bound.items():
        if len(value) == 42:
            for base in bases:
                key = keccak(bytes.fromhex(word(int(value, 16)) + word(base)))
                keyed[int.from_bytes(key, "big")] = f"<{role}>@{base:#x}"
    return {keyed.get(k, f"{k:#x}"): canon(f"{v:#066x}", bound) for k, v in slots.items()}


def replay(name, suite, code, order, chains):
    mismatches = 0
    stamp = GENESIS
    # Each build's roles. Deployed ones agree; a `bind` step reads one from each build.
    roles = {b: {} for b in order}
    bound = {b: {} for b in order}
    gas_rows = []
    fill = lambda a, b: roles[b][a[1:]] if a.startswith("$") else a
    # A role is `(role, pair)`, or `(role, pair, types, args)` for constructor arguments.
    for role, pair, *ctor in suite["deploy"]:
        encoded = ""
        if ctor:
            types, values = ctor
            encoded = run(["cast", "abi-encode", f"f{types}", *(fill(v, "lithe") for v in values)]).stdout.strip()[2:]
        cells = []
        for build in order:
            chains[build].at(stamp)
            receipt = chains[build].send(None, "A", code[pair][build][0] + encoded, [], None)
            assert receipt["status"] == 1, f"{name} {role} {build} failed to deploy"
            roles[build][role] = receipt["address"].lower()
            cells.append(str(receipt["gas"]))
        assert len({roles[b][role] for b in order}) == 1, f"{name}: {role} landed at different addresses"
        gas_rows.append([f"deploy {role}", *cells])
        stamp += STEP
        # Every id either side's code could answer ERC-165 for gets the same answer.
        if "supportsInterface(bytes4)" in code[pair]["lithe"][2]:
            for id in sorted(set().union(*(push4s(code[pair][b][0]) for b in order)) | {"0xffffffff"}):
                answers = {b: chains[b].answer(roles[b][role], id) for b in order}
                if len(set(answers.values())) > 1:
                    mismatches += 1
                    print(f"  MISMATCH {name} {role}.supportsInterface({id}): {answers}")
    for step in suite["steps"]:
        if step[0] == "wait":
            stamp += step[1]
            continue
        # `("bind", role, target, sig, args)`: the role is what the call returns, an
        # address or a word, in each build.
        if step[0] == "bind":
            _, role, target, sig, args = step
            for build in order:
                result = chains[build].call(roles[build][target], "A", sig, [fill(a, build) for a in args])["result"]
                value = "0x" + result[-40:] if int(result, 16) >> 160 == 0 else result
                roles[build][role] = bound[build][role] = value.lower()
            continue
        kind, sender, role, sig, args, value = step
        results = {}
        filled = {}
        for build in order:
            chain = chains[build]
            # Arguments may be a function of the build's roles, as a signature over its domain is.
            filled[build] = args(roles[build]) if callable(args) else [fill(a, build) for a in args]
            if kind == "send":
                chain.at(stamp)
                results[build] = chain.send(roles[build][role], sender, sig, filled[build], value)
            else:
                results[build] = chain.call(roles[build][role], sender, sig, filled[build])
        args = filled["lithe"]
        if kind == "send":
            stamp += STEP
        key = (lambda r: (r["status"], r["logs"])) if kind == "send" else (lambda r: r["result"])
        seen = {b: canon(key(results[b]), bound[b]) for b in order}
        if not all(seen[b] == seen["lithe"] for b in order):
            mismatches += 1
            print(f"  MISMATCH {name} {role}.{sig} {args}:")
            for b in order:
                print(f"    {b}: {seen[b]}")
        names = {v: r for r, v in roles["lithe"].items()}
        shown = ["$" + names[a] if a in names else a[:10] for a in args]
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
    contracts = [r for r, v in roles["lithe"].items() if len(v) == 42 and r not in suite.get("own_layout", [])]
    slots = {b: chains[b].storage([roles[b][r] for r in contracts]) for b in order}
    # Maps keyed by a bound address: their slots, and the words just past a slot in use.
    bases = set(range(64)) | {k - d for b in order for s in slots[b].values() for k in s for d in range(8) if k >= d}
    for b in order[1:]:
        for role in contracts:
            want = canon_slots(slots["lithe"][roles["lithe"][role]], bound["lithe"], bases)
            have = canon_slots(slots[b][roles[b][role]], bound[b], bases)
            if want != have:
                mismatches += 1
                print(f"  STORAGE MISMATCH {name} {role}: lithe vs {b}")
                for k in sorted(set(want) | set(have)):
                    if want.get(k, 0) != have.get(k, 0):
                        print(f"    slot {k}: lithe {want.get(k, 0)} {b} {have.get(k, 0)}")
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
