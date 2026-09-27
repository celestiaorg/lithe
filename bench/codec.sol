// SPDX-License-Identifier: MIT
// Benchmark: abi.encode, abi.decode, and abi.encodePacked on their own, over flat values,
// several values at once, and nested ones. Mirrors codec.lithe.
pragma solidity ^0.8.24;

interface IBook {
    struct Order {
        uint256 id;
        string note;
        uint256[] legs;
    }

    function place(Order[] calldata os) external returns (uint256[] memory);
}

contract Codec {
    uint256 seen_;
    bytes32 digest_;

    function enc_flat(address who, uint256 amount, string calldata memo) external pure returns (bytes memory) {
        return abi.encode(who, amount, memo);
    }

    function dec_flat(bytes calldata data) external pure returns (address who, uint256 amount, string memory memo) {
        (who, amount, memo) = abi.decode(data, (address, uint256, string));
    }

    function enc_orders(IBook.Order[] calldata os) external pure returns (bytes memory) {
        return abi.encode(os);
    }

    function dec_orders(bytes calldata data) external pure returns (IBook.Order[] memory) {
        return abi.decode(data, (IBook.Order[]));
    }

    function enc_grid(uint256[][] calldata g) external pure returns (bytes memory) {
        return abi.encode(g);
    }

    function dec_grid(bytes calldata data) external pure returns (uint256[][] memory) {
        return abi.decode(data, (uint256[][]));
    }

    function packed(address who, uint96 amount, string calldata memo) external pure returns (bytes memory) {
        return abi.encodePacked(who, amount, memo);
    }

    function calldata_for(IBook.Order[] calldata os) external pure returns (bytes memory) {
        return abi.encodeCall(IBook.place, (os));
    }

    function keep(bytes calldata data) external {
        IBook.Order[] memory os = abi.decode(data, (IBook.Order[]));
        seen_ = os.length;
        digest_ = keccak256(abi.encode(os));
    }

    function seen() external view returns (uint256) {
        return seen_;
    }

    function digest() external view returns (bytes32) {
        return digest_;
    }
}
