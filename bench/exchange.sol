// SPDX-License-Identifier: MIT
// Benchmark: a fixed-price exchange whose state-changing calls return values.
// Mirrors exchange.lithe.
pragma solidity ^0.8.24;

contract Exchange {
    struct SwapResult {
        uint256 amount_out;
        uint256 fee;
    }

    error Slippage(uint256 amount_out, uint256 min_out);

    event Swapped(address indexed trader, uint256 amount_in, uint256 amount_out);

    uint256 volume;
    uint256 fees;
    uint256 total_shares;
    mapping(address => uint256) shares;

    function swap(uint256 amount_in, uint256 min_out) external returns (SwapResult memory) {
        uint256 fee = amount_in * 3 / 1000;
        uint256 amount_out = (amount_in - fee) * 2;
        if (amount_out < min_out) revert Slippage(amount_out, min_out);
        volume += amount_in;
        fees += fee;
        emit Swapped(msg.sender, amount_in, amount_out);
        return SwapResult(amount_out, fee);
    }

    function deposit(uint256 amount) external returns (uint256 minted) {
        minted = amount * 10;
        total_shares += minted;
        shares[msg.sender] += minted;
    }

    function split(uint256 amount) external returns (uint256, uint256) {
        total_shares -= amount;
        return (amount / 3, amount - amount / 3);
    }

    function shares_of(address who) external view returns (uint256) {
        return shares[who];
    }
}
