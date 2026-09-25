// SPDX-License-Identifier: MIT
// Benchmark: many short literal reasons, as `require(cond, "reason")` carries them.
// Mirrors reasons.lithe.
pragma solidity ^0.8.24;

contract Reasons {
    error Failed(string);
    error Denied(address who, string reason);

    address owner;
    bool paused;
    uint256 limit;
    mapping(address => uint256) balances;

    constructor() {
        owner = msg.sender;
        limit = 1000;
    }

    function deposit(uint256 amount) external {
        if (paused) revert Failed("paused");
        if (amount == 0) revert Failed("zero amount");
        if (amount > limit) revert Failed("over the limit");
        balances[msg.sender] += amount;
    }

    function withdraw(uint256 amount) external {
        if (paused) revert Failed("paused");
        if (amount == 0) revert Failed("zero amount");
        uint256 have = balances[msg.sender];
        if (have < amount) revert Failed("insufficient balance to proceed");
        balances[msg.sender] = have - amount;
    }

    function transfer(address to, uint256 amount) external {
        if (paused) revert Failed("paused");
        if (to == address(0)) revert Failed("zero address");
        if (to == msg.sender) revert Denied(to, "self transfer");
        uint256 have = balances[msg.sender];
        if (have < amount) revert Failed("insufficient balance to proceed");
        balances[msg.sender] = have - amount;
        balances[to] += amount;
    }

    function set_limit(uint256 newLimit) external {
        if (msg.sender != owner) revert Denied(msg.sender, "not the owner");
        if (newLimit == 0) revert Failed("zero limit");
        if (newLimit > 1_000_000) revert Failed("limit too high");
        limit = newLimit;
    }

    function pause(bool on) external {
        if (msg.sender != owner) revert Denied(msg.sender, "not the owner");
        if (paused == on) revert Failed("already set");
        paused = on;
    }

    function balance_of(address who) external view returns (uint256) {
        if (who == address(0)) revert Failed("zero address");
        return balances[who];
    }
}
