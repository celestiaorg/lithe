// SPDX-License-Identifier: MIT
// Benchmark: lists of strings and bytes through the ABI, storage, events, and encoding,
// and strings in maps. Mirrors texts.lithe.
pragma solidity ^0.8.24;

contract Texts {
    bytes[] saved_;
    string[] names_;
    mapping(uint256 => string) labels_;
    string note_;

    event Named(address indexed who, string[] names);

    function save(bytes[] memory xs) external {
        saved_ = xs;
    }

    function push(bytes calldata x) external {
        saved_.push(x);
    }

    function setAt(uint256 i, bytes calldata x) external {
        saved_[i] = x;
    }

    function saved() external view returns (bytes[] memory) {
        return saved_;
    }

    function savedAt(uint256 i) external view returns (bytes memory) {
        return saved_[i];
    }

    function joined() external view returns (bytes memory out) {
        for (uint256 i = 0; i < saved_.length; i++) {
            out = bytes.concat(out, saved_[i]);
        }
    }

    function setNames(string[] memory xs) external {
        names_ = xs;
        emit Named(msg.sender, xs);
    }

    function names() external view returns (string[] memory) {
        return names_;
    }

    function label(uint256 k, string calldata v) external {
        labels_[k] = v;
    }

    function labelOf(uint256 k) external view returns (string memory) {
        return labels_[k];
    }

    function first(bytes[] calldata xs) external pure returns (bytes memory) {
        return xs[0];
    }

    function concatAll(bytes[] calldata xs) external pure returns (bytes memory out) {
        for (uint256 i = 0; i < xs.length; i++) {
            out = bytes.concat(out, xs[i]);
        }
    }

    function echo(string[] calldata xs) external pure returns (string[] memory) {
        return xs;
    }

    function pair(bytes calldata a, bytes calldata b) external pure returns (bytes[] memory out) {
        out = new bytes[](2);
        out[0] = a;
        out[1] = b;
    }

    function left(bytes calldata a, bytes calldata) external pure returns (bytes memory) {
        return a;
    }

    function same(bytes[] calldata a, bytes[] calldata b) external pure returns (bool) {
        return keccak256(abi.encode(a)) == keccak256(abi.encode(b));
    }

    function encoded(uint256 k, string[] calldata xs) external pure returns (bytes memory) {
        return abi.encode(k, xs);
    }

    function decoded(bytes calldata data) external pure returns (bytes[] memory) {
        return abi.decode(data, (bytes[]));
    }

    function smallOf(bytes calldata data) external pure returns (uint8) {
        return abi.decode(data, (uint8));
    }

    function textOf(bytes calldata data) external pure returns (string memory) {
        return abi.decode(data, (string));
    }

    function addrMem(bytes memory data) external pure returns (address) {
        return abi.decode(data, (address));
    }

    function textMem(bytes memory data) external pure returns (string memory) {
        return abi.decode(data, (string));
    }

    function namesMem(bytes memory data) external pure returns (string[] memory) {
        return abi.decode(data, (string[]));
    }

    function sameText(string calldata a, bytes calldata data) external pure returns (bool) {
        return keccak256(bytes(abi.decode(data, (string)))) == keccak256(bytes(a));
    }

    function emptyText(bytes calldata data) external pure returns (bool) {
        return bytes(abi.decode(data, (string))).length == 0;
    }

    function keepText(uint256 k, bytes calldata data) external {
        labels_[k] = abi.decode(data, (string));
        note_ = abi.decode(data, (string));
    }

    function note() external view returns (string memory) {
        return note_;
    }

    function selectorOnly() external pure returns (bytes memory) {
        return abi.encodeWithSelector(0x12345678);
    }
}
