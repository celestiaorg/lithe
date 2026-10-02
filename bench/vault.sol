// SPDX-License-Identifier: MIT
// Benchmark: an ETH vault with pausing and withdrawals. Mirrors vault.lithe.
pragma solidity ^0.8.24;

contract Vault {
    error NotOwner();
    error Paused();
    error Insufficient(uint256 available, uint256 required);

    event Deposited(address indexed who, uint256 amount);
    event Withdrawn(address indexed who, uint256 amount);

    address immutable owner;
    bool paused;
    mapping(address => uint256) deposits;

    constructor() {
        owner = msg.sender;
    }

    function deposit() external payable {
        if (paused) revert Paused();
        deposits[msg.sender] += msg.value;
        emit Deposited(msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external {
        if (paused) revert Paused();
        uint256 have = deposits[msg.sender];
        if (have < amount) revert Insufficient(have, amount);
        deposits[msg.sender] = have - amount;
        emit Withdrawn(msg.sender, amount);
        (bool ok,) = msg.sender.call{value: amount}("");
        if (!ok) revert();
    }

    function setPaused(bool flag) external {
        if (msg.sender != owner) revert NotOwner();
        paused = flag;
    }

    function depositOf(address who) external view returns (uint256) {
        return deposits[who];
    }
}
