// SPDX-License-Identifier: MIT
// Benchmark: packed fixed lists, records, and tuples. Mirrors layout.lithe slot for slot.
pragma solidity ^0.8.24;

contract Layout {
    struct Pos {
        uint16 x;
        uint16 y;
        bool live;
    }

    // Lithe's `(uint32, address)` tuple lays out like this struct.
    struct Pair {
        uint32 a;
        address who;
    }

    uint8 _small;
    uint8[40] levels;
    bool[5] flags;
    int16[3] deltas;
    Pos _spot;
    Pair _pair;
    uint64 tail;
    uint256 total;

    function setLevel(uint256 i, uint8 v) external {
        levels[i] = v;
    }

    function setFlag(uint256 i, bool f) external {
        flags[i] = f;
    }

    function setDelta(uint256 i, int16 d) external {
        deltas[i] = d;
    }

    function place(uint16 x, uint16 y) external {
        _spot.x = x;
        _spot.y = y;
        _spot.live = true;
    }

    function setPair(uint32 a, address who) external {
        _pair = Pair(a, who);
    }

    function bump(uint64 t) external {
        tail = t;
        _small = _small + 1;
        total = total + 1;
    }

    function level(uint256 i) external view returns (uint8) {
        return levels[i];
    }

    function flag(uint256 i) external view returns (bool) {
        return flags[i];
    }

    function delta(uint256 i) external view returns (int16) {
        return deltas[i];
    }

    function spot() external view returns (uint16, uint16, bool) {
        return (_spot.x, _spot.y, _spot.live);
    }

    function pair() external view returns (uint32, address) {
        return (_pair.a, _pair.who);
    }

    function small() external view returns (uint8) {
        return _small;
    }
}
