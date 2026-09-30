// SPDX-License-Identifier: MIT
// Benchmark: Solady's FixedPointMathLib on runtime arguments. Mirrors fixed_point.lithe.
// Lithe's unsigned `_up` products and quotients keep 512 bits, so they are Solady's
// `fullMulDivUp` here, not `mulWadUp`, which reverts once `a * b` passes 256 bits.
pragma solidity ^0.8.24;

import {FixedPointMathLib as F} from "solady/utils/FixedPointMathLib.sol";

contract FixedPointBench {
    uint256 last;

    function wad_mul_up(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDivUp(a, b, 1e18);
    }

    function wad_div_up(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDivUp(a, 1e18, b);
    }

    function div_wad(uint256 a, uint256 b) external pure returns (uint256) {
        return F.fullMulDiv(a, 1e18, b);
    }

    function s_mul_wad(int256 a, int256 b) external pure returns (int256) {
        return F.sMulWad(a, b);
    }

    function s_div_wad(int256 a, int256 b) external pure returns (int256) {
        return F.sDivWad(a, b);
    }

    function exp_wad(int256 x) external pure returns (int256) {
        return F.expWad(x);
    }

    function ln_wad(int256 x) external pure returns (int256) {
        return F.lnWad(x);
    }

    function pow_wad(int256 x, int256 y) external pure returns (int256) {
        return F.powWad(x, y);
    }

    function sqrt_wad(uint256 x) external pure returns (uint256) {
        return F.sqrtWad(x);
    }

    function cbrt_wad(uint256 x) external pure returns (uint256) {
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

    function dist_int(int256 a, int256 b) external pure returns (uint256) {
        return F.dist(a, b);
    }

    function gcd(uint256 a, uint256 b) external pure returns (uint256) {
        return F.gcd(a, b);
    }

    function saturating_add(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingAdd(a, b);
    }

    function saturating_sub(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingSub(a, b);
    }

    function saturating_mul(uint256 a, uint256 b) external pure returns (uint256) {
        return F.saturatingMul(a, b);
    }

    function lerp(uint256 a, uint256 b, uint256 t, uint256 t0, uint256 t1) external pure returns (uint256) {
        return F.lerp(a, b, t, t0, t1);
    }

    function lerp_int(int256 a, int256 b, int256 t, int256 t0, int256 t1) external pure returns (int256) {
        return F.lerp(a, b, t, t0, t1);
    }

    function set_last(int256 x) external {
        last = uint256(F.expWad(x));
    }
}
