// SPDX-License-Identifier: MIT
// Benchmark: string and bytes arguments to a constructor, and a lone one to a
// function. Mirrors profile.lithe.
pragma solidity ^0.8.24;

contract Profile {
    string _name;
    bytes _avatar;
    string _bio;

    constructor(string memory name_, bytes memory avatar_) {
        _name = name_;
        _avatar = avatar_;
    }

    function set_bio(string calldata bio_) external {
        _bio = bio_;
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function avatar() external view returns (bytes memory) {
        return _avatar;
    }

    function bio() external view returns (string memory) {
        return _bio;
    }
}
