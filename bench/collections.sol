// SPDX-License-Identifier: MIT
// Benchmark: a queue and an enumerable map laid out as std's, the keys in OpenZeppelin's
// enumerable set. Popping deletes the element; removing leaves the value, as std's does.
// Mirrors collections.lithe.
pragma solidity ^0.8.24;

import {EnumerableSet} from "@openzeppelin/contracts/utils/structs/EnumerableSet.sol";

contract Collections {
    using EnumerableSet for EnumerableSet.AddressSet;

    error QueueEmpty();
    error EnumerableMapNonexistentKey(bytes32 key);

    struct Queue {
        mapping(uint256 => address) items;
        uint256 head;
        uint256 tail;
    }

    struct Map {
        EnumerableSet.AddressSet keys;
        mapping(address => uint256) values;
    }

    Queue pending;
    Map balances;

    function enqueue(address who) external {
        pending.items[pending.tail] = who;
        pending.tail += 1;
    }

    function dequeue() external returns (address value) {
        if (pending.tail <= pending.head) revert QueueEmpty();
        value = pending.items[pending.head];
        delete pending.items[pending.head];
        pending.head += 1;
    }

    function queued() external view returns (uint256) {
        return pending.tail - pending.head;
    }

    function set(address key, uint256 value) external {
        balances.values[key] = value;
        balances.keys.add(key);
    }

    function remove(address key) external {
        balances.keys.remove(key);
    }

    function get(address key) external view returns (uint256) {
        if (!balances.keys.contains(key)) revert EnumerableMapNonexistentKey(bytes32(uint256(uint160(key))));
        return balances.values[key];
    }

    function length() external view returns (uint256) {
        return balances.keys.length();
    }

    function at(uint256 index) external view returns (address, uint256) {
        address key = balances.keys.at(index);
        return (key, balances.values[key]);
    }
}
