// SPDX-License-Identifier: MIT
// Benchmark: owner-gated counter with an event. Mirrors counter.lithe.
pragma solidity ^0.8.24;

contract Counter {
    error Not_owner();

    event Count_changed(uint256 old_count, uint256 new_count);

    uint256 count;
    address owner;

    constructor() {
        owner = msg.sender;
    }

    function increment(uint256 n) external {
        if (n > 0) {
            uint256 old = count;
            count = old + n;
            emit Count_changed(old, count);
        }
    }

    function reset() external {
        if (msg.sender != owner) revert Not_owner();
        uint256 old = count;
        count = 0;
        emit Count_changed(old, 0);
    }

    function get_count() external view returns (uint256) {
        return count;
    }
}
