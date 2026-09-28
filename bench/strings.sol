// SPDX-License-Identifier: MIT
// Benchmark: strings short and long, from calldata and storage: stored, returned, joined,
// compared, logged, and carried by errors. Mirrors strings.lithe.
pragma solidity ^0.8.24;

contract Names {
    error NameTaken(string name, address owner);
    error TooLong(string name, uint256 limit);
    error NotOwner(address caller, string name);

    event Renamed(address indexed who, string old_name, string new_name);

    address immutable owner;
    string _name;
    string _description;

    constructor() {
        owner = msg.sender;
    }

    function rename(string calldata newName) external {
        if (msg.sender != owner) revert NotOwner(msg.sender, _name);
        if (keccak256(bytes(newName)) == keccak256(bytes(_name))) revert NameTaken(newName, owner);
        if (bytes(newName).length > 100) revert TooLong(newName, 100);
        emit Renamed(msg.sender, _name, newName);
        _name = newName;
    }

    function describe(string calldata text) external {
        if (msg.sender != owner) revert NotOwner(msg.sender, _name);
        if (bytes(text).length > 200) revert TooLong(text, 200);
        _description = string.concat(_name, ": ", text);
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function description() external view returns (string memory) {
        return _description;
    }

    function title(string calldata prefix) external view returns (string memory) {
        return string.concat(prefix, " ", _name);
    }

    function require_name(string calldata candidate) external view returns (bool) {
        if (keccak256(bytes(candidate)) != keccak256(bytes(_name))) revert NotOwner(msg.sender, _name);
        return true;
    }
}
