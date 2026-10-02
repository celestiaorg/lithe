// SPDX-License-Identifier: MIT
// Benchmark: strings and bytes as map values and list elements. Mirrors names.lithe.
pragma solidity ^0.8.24;

contract Names {
    mapping(uint256 => string) names;
    mapping(bytes32 => bytes) blobs;
    mapping(address => mapping(uint256 => string)) labels;
    string[] _notes;

    function setName(uint256 id, string calldata n) external {
        names[id] = n;
    }

    function name(uint256 id) external view returns (string memory) {
        return names[id];
    }

    function setBlob(bytes32 key, bytes calldata b) external {
        blobs[key] = b;
    }

    function blob(bytes32 key) external view returns (bytes memory) {
        return blobs[key];
    }

    function setLabel(uint256 id, string calldata l) external {
        labels[msg.sender][id] = l;
    }

    function label(address who, uint256 id) external view returns (string memory) {
        return labels[who][id];
    }

    function addNote(string calldata n) external {
        _notes.push(n);
    }

    function setNote(uint256 i, string calldata n) external {
        _notes[i] = n;
    }

    function note(uint256 i) external view returns (string memory) {
        return _notes[i];
    }

    function setNotes(string calldata a, string calldata b) external {
        string[] memory ns = new string[](2);
        ns[0] = a;
        ns[1] = b;
        _notes = ns;
    }

    function noteCopy(uint256 i) external view returns (string memory) {
        string[] memory ns = _notes;
        return ns[i];
    }

    function notesLength() external view returns (uint256 total) {
        for (uint256 i = 0; i < _notes.length; i++) {
            total += bytes(_notes[i]).length;
        }
    }
}
