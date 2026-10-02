// SPDX-License-Identifier: MIT
// Benchmark: string and bytes storage. Mirrors registry.lithe.
pragma solidity ^0.8.24;

contract Registry {
    event Renamed(string indexed label);
    event Tagged(address indexed who, bytes4 tag, uint8 level);

    string _name;
    bytes _blob;
    uint256 updates;
    bytes4 _tag;
    uint8 _level;

    constructor(string memory n) {
        _name = n;
    }

    function rename(string calldata n) external {
        _name = n;
        updates += 1;
        emit Renamed(n);
    }

    function setBlob(bytes calldata b) external {
        _blob = b;
    }

    function setBoth(string calldata n, bytes calldata b) external {
        _name = n;
        _blob = b;
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function blob() external view returns (bytes memory) {
        return _blob;
    }

    function digest() external view returns (bytes32) {
        return keccak256(_blob);
    }

    function setTag(bytes4 t, uint8 level_) external {
        _tag = t;
        _level = level_;
        emit Tagged(msg.sender, t, level_);
    }

    function tag() external view returns (bytes4) {
        return _tag;
    }

    function level() external view returns (uint8) {
        return _level;
    }
}
