// SPDX-License-Identifier: MIT
// Benchmark: powers, OpenZeppelin's roots, logarithms, and signed helpers, and hex
// formatting, on runtime arguments. Mirrors numerics.lithe.
pragma solidity ^0.8.24;

import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {SignedMath} from "@openzeppelin/contracts/utils/math/SignedMath.sol";
import {Strings} from "@openzeppelin/contracts/utils/Strings.sol";

contract Numerics {
    // OpenZeppelin has no signed clamp; this is the error Lithe's Math.clamp raises.
    error MathInvalidSignedRange(int256 low, int256 high);

    uint256 scale;

    function pow(uint256 base, uint256 exponent) external pure returns (uint256) {
        return base ** exponent;
    }

    function units(uint8 decimals) external pure returns (uint256) {
        return 10 ** decimals;
    }

    function pow_signed(int256 base, uint256 exponent) external pure returns (int256) {
        return base ** exponent;
    }

    function pow2(uint256 exponent) external pure returns (uint256) {
        return 2 ** exponent;
    }

    function sqrt(uint256 a) external pure returns (uint256) {
        return Math.sqrt(a);
    }

    function log2(uint256 a) external pure returns (uint256) {
        return Math.log2(a);
    }

    function log10(uint256 a) external pure returns (uint256) {
        return Math.log10(a);
    }

    function abs(int256 x) external pure returns (uint256) {
        return SignedMath.abs(x);
    }

    function min(int256 a, int256 b) external pure returns (int256) {
        return SignedMath.min(a, b);
    }

    function max(int256 a, int256 b) external pure returns (int256) {
        return SignedMath.max(a, b);
    }

    function average(int256 a, int256 b) external pure returns (int256) {
        return SignedMath.average(a, b);
    }

    function clamp(int256 x, int256 low, int256 high) external pure returns (int256) {
        if (low > high) revert MathInvalidSignedRange(low, high);
        return SignedMath.min(SignedMath.max(x, low), high);
    }

    function hex_nat(uint256 n) external pure returns (string memory) {
        return Strings.toHexString(n);
    }

    function hex_fixed(uint256 n, uint256 length) external pure returns (string memory) {
        return Strings.toHexString(n, length);
    }

    function hex_address(address a) external pure returns (string memory) {
        return Strings.toHexString(a);
    }

    function checksum(address a) external pure returns (string memory) {
        return Strings.toChecksumHexString(a);
    }

    function set_scale(uint8 decimals) external {
        scale = 10 ** decimals;
    }
}
