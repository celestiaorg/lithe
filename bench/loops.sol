// SPDX-License-Identifier: MIT
// Benchmark: loops over calldata, storage, and ranges, with effects inside them.
// Mirrors loops.lithe.
pragma solidity ^0.8.24;

contract Loops {
    error Nobody();

    event Sent(address indexed to, uint256 amount);

    mapping(address => uint256) balances;
    address[] owners;
    mapping(address => bool) is_owner_;

    function sum(uint256[] calldata xs) external pure returns (uint256 acc) {
        for (uint256 i = 0; i < xs.length; i++) {
            acc += xs[i];
        }
    }

    function airdrop(address[] calldata tos, uint256 amount) external {
        for (uint256 i = 0; i < tos.length; i++) {
            balances[tos[i]] += amount;
            emit Sent(tos[i], amount);
        }
    }

    function join(address who) external {
        owners.push(who);
    }

    function markAll() external {
        for (uint256 i = 0; i < owners.length; i++) {
            is_owner_[owners[i]] = true;
        }
    }

    function find(address target) external view returns (uint256 hit) {
        for (uint256 i = 0; i < owners.length; i++) {
            if (owners[i] == target) {
                hit = i + 1;
                break;
            }
        }
    }

    function gcd(uint256 a, uint256 b) external pure returns (uint256) {
        uint256 x = a;
        uint256 y = b;
        while (y != 0) {
            (x, y) = (y, x % y);
        }
        return x;
    }

    function hashChain(bytes32 seed, uint256 n) external pure returns (bytes32 h) {
        h = seed;
        for (uint256 i = 0; i < n; i++) {
            h = keccak256(abi.encode(h));
        }
    }

    function payout(address[] calldata tos) external payable {
        if (tos.length == 0) revert Nobody();
        uint256 each = msg.value / tos.length;
        for (uint256 i = 0; i < tos.length; i++) {
            (bool ok, ) = tos[i].call{value: each}("");
            require(ok);
        }
    }

    function balanceOf(address who) external view returns (uint256) {
        return balances[who];
    }

    function isOwner(address who) external view returns (bool) {
        return is_owner_[who];
    }
}
