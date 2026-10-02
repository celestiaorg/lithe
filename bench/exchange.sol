// SPDX-License-Identifier: MIT
// Benchmark: a fixed-price exchange whose state-changing calls return values.
// Mirrors exchange.lithe.
pragma solidity ^0.8.24;

contract Exchange {
    struct SwapResult {
        uint256 amountOut;
        uint256 fee;
    }

    error Slippage(uint256 amountOut, uint256 minOut);

    event Swapped(address indexed trader, uint256 amountIn, uint256 amountOut);

    uint256 volume;
    uint256 fees;
    uint256 totalShares;
    mapping(address => uint256) shares;

    function swap(uint256 amountIn, uint256 minOut) external returns (SwapResult memory) {
        uint256 fee = amountIn * 3 / 1000;
        uint256 amountOut = (amountIn - fee) * 2;
        if (amountOut < minOut) revert Slippage(amountOut, minOut);
        volume += amountIn;
        fees += fee;
        emit Swapped(msg.sender, amountIn, amountOut);
        return SwapResult(amountOut, fee);
    }

    function deposit(uint256 amount) external returns (uint256 minted) {
        minted = amount * 10;
        totalShares += minted;
        shares[msg.sender] += minted;
    }

    function split(uint256 amount) external returns (uint256, uint256) {
        totalShares -= amount;
        return (amount / 3, amount - amount / 3);
    }

    function sharesOf(address who) external view returns (uint256) {
        return shares[who];
    }
}
