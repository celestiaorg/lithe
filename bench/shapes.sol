// SPDX-License-Identifier: MIT
// Benchmark: errors of several shapes, strings and lists among words, each raised from
// more than one place. Mirrors shapes.lithe.
pragma solidity ^0.8.24;

contract Shapes {
    error Unauthorized(address caller, string role);
    error OutOfRange(uint256 value, uint256 min, uint256 max);
    error UnknownItem(uint256 id, string name);
    error BadItems(uint256[]);
    error BadBatch(string reason, uint256[] ids);
    error BadData(bytes);
    error Mismatch(string expected, string actual);

    address immutable owner;
    uint256 items;
    uint256 sold;

    constructor() {
        owner = msg.sender;
    }

    function add(uint256 count) external {
        if (msg.sender != owner) revert Unauthorized(msg.sender, "owner");
        if (count == 0 || count > 10) revert OutOfRange(count, 1, 10);
        items += count;
    }

    function buy(uint256 id, string calldata name) external {
        if (id >= items) revert UnknownItem(id, name);
        if (bytes(name).length > 40) revert OutOfRange(bytes(name).length, 0, 40);
        if (bytes(name).length == 0) revert Mismatch("a name", name);
        sold += 1;
    }

    function buy_all(uint256[] calldata ids, string calldata note) external {
        if (ids.length == 0) revert BadBatch(note, ids);
        if (ids.length > 4) revert BadBatch("batch too large", ids);
        for (uint256 i = 0; i < ids.length; i++) {
            if (ids[i] >= items) revert BadItems(ids);
        }
        if (ids[0] == 0) revert UnknownItem(0, note);
        sold += ids.length;
    }

    function load(bytes calldata data) external {
        if (msg.sender != owner) revert Unauthorized(msg.sender, "loader");
        if (data.length == 0) revert BadData(data);
        if (data.length > 64) {
            uint256[] memory bad = new uint256[](2);
            bad[0] = data.length;
            bad[1] = 64;
            revert BadItems(bad);
        }
        sold += data.length;
    }

    function compare(string calldata expected, string calldata actual) external pure returns (uint256) {
        if (keccak256(bytes(expected)) != keccak256(bytes(actual))) revert Mismatch(expected, actual);
        if (bytes(expected).length == 0) revert BadData(hex"ff");
        return bytes(expected).length;
    }
}
