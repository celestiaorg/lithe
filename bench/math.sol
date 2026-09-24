// SPDX-License-Identifier: MIT
// Benchmark: checked arithmetic in pure views. Mirrors math.lithe.
pragma solidity ^0.8.24;

contract Math {
    uint256 last;

    function mul_div(uint256 a, uint256 b, uint256 c) external pure returns (uint256) {
        return a * b / c;
    }

    function average(uint256 a, uint256 b) external pure returns (uint256) {
        return (a + b) / 2;
    }

    function distance(int256 a, int256 b) external pure returns (int256) {
        return a * b - a / b;
    }

    function narrow(uint256 x) external pure returns (uint8) {
        // Lithe narrows with a checked conversion: out of range is Panic(0x11).
        if (x > type(uint8).max) {
            assembly {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x11)
                revert(0, 0x24)
            }
        }
        return uint8(x);
    }

    function mix(uint32 x, uint32 y) external pure returns (uint32) {
        return (x + y) * 3 - x % 7;
    }

    function store(uint256 a, uint256 b) external {
        last = a * b + a / b - b % a;
    }
}
