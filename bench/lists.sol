// SPDX-License-Identifier: MIT
// Benchmark: dynamic arrays through the ABI, storage, events, and encoding. Mirrors
// lists.lithe.
pragma solidity ^0.8.24;

contract Lists {
    uint256[] saved_;
    address[] owners_;

    event Batch(address indexed who, uint256[] ids, string note);
    event Tagged(bytes4[] indexed tags, uint256 count);

    function save(uint256[] calldata xs) external {
        saved_ = xs;
    }

    function push(uint256 x) external {
        saved_.push(x);
    }

    function setOwners(address[] calldata owners) external {
        owners_ = owners;
    }

    function saved() external view returns (uint256[] memory) {
        return saved_;
    }

    function owners() external view returns (address[] memory) {
        return owners_;
    }

    function ownerAt(uint256 i) external view returns (address) {
        return owners_[i];
    }

    function first(uint256[] calldata xs) external pure returns (uint256) {
        return xs[0];
    }

    function echo(bytes4[] calldata xs) external pure returns (bytes4[] memory) {
        return xs;
    }

    function pair(uint256 a, uint256 b) external pure returns (uint256[] memory out) {
        out = new uint256[](2);
        out[0] = a;
        out[1] = b;
    }

    function announce(uint256[] calldata ids, string calldata note) external {
        emit Batch(msg.sender, ids, note);
    }

    function tag(bytes4[] calldata tags) external {
        emit Tagged(tags, tags.length);
    }

    function same(uint256[] calldata a, uint256[] calldata b) external pure returns (bool) {
        return keccak256(abi.encode(a)) == keccak256(abi.encode(b));
    }

    function encoded(uint256[] calldata xs, bytes4 tag) external pure returns (bytes memory) {
        return abi.encode(tag, xs);
    }
}
