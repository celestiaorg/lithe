// SPDX-License-Identifier: MIT
// Benchmark: owner-gated counter with an event. Mirrors counter.lithe.
pragma solidity ^0.8.24;

contract Counter {
    error NotOwner();

    event CountChanged(uint256 oldCount, uint256 newCount);

    uint256 count;
    address immutable owner;

    constructor() {
        owner = msg.sender;
    }

    function increment(uint256 n) external {
        if (n > 0) {
            uint256 old = count;
            count = old + n;
            emit CountChanged(old, count);
        }
    }

    function reset() external {
        if (msg.sender != owner) revert NotOwner();
        uint256 old = count;
        count = 0;
        emit CountChanged(old, 0);
    }

    function getCount() external view returns (uint256) {
        return count;
    }
}
