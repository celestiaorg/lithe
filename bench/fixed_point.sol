// SPDX-License-Identifier: MIT
// Benchmark: Solady's FixedPointMathLib on runtime arguments. Mirrors fixed_point.lithe.
// Lithe's unsigned `_up` products and quotients keep 512 bits, so they are Solady's
// `fullMulDivUp` here, not `mulWadUp`, which reverts once `a * b` passes 256 bits.
pragma solidity ^0.8.24;

import {FixedPointMathLib as F} from "solady/utils/FixedPointMathLib.sol";

contract FixedPointBench {
    uint256 last;

    function wadMulUp(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDivUp(a, b, 1e18);
    }

    function wadDivUp(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDivUp(a, 1e18, b);
    }

    function divWad(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDiv(a, 1e18, b);
    }

    function sMulWad(int256 a, int256 b) external pure returns (int256) {
        return F.sMulWad(a, b);
    }

    function sDivWad(int256 a, int256 b) external pure returns (int256) {
        return F.sDivWad(a, b);
    }

    function expWad(int256 x) external pure returns (int256) {
        return F.expWad(x);
    }

    function lnWad(int256 x) external pure returns (int256) {
        return F.lnWad(x);
    }

    function powWad(int256 x, int256 y) external pure returns (int256) {
        return F.powWad(x, y);
    }

    function sqrtWad(uint256 x) external pure returns (uint256) {
        return F.sqrtWad(x);
    }

    function cbrtWad(uint256 x) external pure returns (uint256) {
        return F.cbrtWad(x);
    }

    function rpow(uint256 x, uint256 n, uint256 base) external pure returns (uint256) {
        return F.rpow(x, n, base);
    }

    function cbrt(uint256 x) external pure returns (uint256) {
        return F.cbrt(x);
    }

    function dist(uint256 a, uint256 b) external pure returns (uint256) {
        return F.dist(a, b);
    }

    function distInt(int256 a, int256 b) external pure returns (uint256) {
        return F.dist(a, b);
    }

    function gcd(uint256 a, uint256 b) external pure returns (uint256) {
        return F.gcd(a, b);
    }

    function saturatingAdd(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingAdd(a, b);
    }

    function saturatingSub(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingSub(a, b);
    }

    function saturatingMul(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingMul(a, b);
    }

    function lerp(uint256 a, uint256 b, uint256 t, uint256 t0, uint256 t1) external pure returns (uint256) {
        return F.lerp(a, b, t, t0, t1);
    }

    function lerpInt(int256 a, int256 b, int256 t, int256 t0, int256 t1) external pure returns (int256) {
        return F.lerp(a, b, t, t0, t1);
    }

    function setLast(int256 x) external {
        last = uint256(F.expWad(x));
    }
}
