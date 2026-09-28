// SPDX-License-Identifier: MIT
// Benchmark: anonymous events, which log no signature topic. Mirrors logs.lithe.
pragma solidity ^0.8.24;

contract Logs {
    event Moved(address indexed from, address indexed to, uint256 indexed id, uint256 indexed kind) anonymous;
    event Noted(uint256 indexed id, string note) anonymous;
    event Ticked(uint256 count) anonymous;

    mapping(uint256 => address) owners;
    uint256 notes;

    function move(address to, uint256 id) external {
        address from = owners[id];
        owners[id] = to;
        emit Moved(from, to, id, 1);
    }

    function note(uint256 id, string calldata text) external {
        notes += 1;
        emit Noted(id, text);
    }

    function tick() external {
        uint256 count = notes + 1;
        notes = count;
        emit Ticked(count);
    }
}
