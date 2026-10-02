// SPDX-License-Identifier: MIT
// Benchmark: a minimal token with owner minting. Mirrors token.lithe.
pragma solidity ^0.8.24;

contract Token {
    error NotOwner();
    error InsufficientBalance(uint256 available, uint256 required);

    event Transfer(address indexed from, address indexed to, uint256 amount);

    address immutable owner;
    uint256 total;
    mapping(address => uint256) balances;

    constructor() {
        owner = msg.sender;
    }

    function mint(address to, uint256 amount) external {
        if (msg.sender != owner) revert NotOwner();
        balances[to] += amount;
        total += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 amount) external {
        address from = msg.sender;
        uint256 have = balances[from];
        if (have < amount) revert InsufficientBalance(have, amount);
        balances[from] = have - amount;
        balances[to] += amount;
        emit Transfer(from, to, amount);
    }

    function balanceOf(address who) external view returns (uint256) {
        return balances[who];
    }

    function totalSupply() external view returns (uint256) {
        return total;
    }
}
