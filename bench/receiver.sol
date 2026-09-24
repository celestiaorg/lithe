// SPDX-License-Identifier: MIT
// Benchmark: an ERC-721 receiver that records each delivery. Mirrors receiver.lithe.
// In mode 1 it answers with the wrong selector; in mode 2 it refuses with a reason.
pragma solidity ^0.8.24;

contract Receiver {
    error Refused(uint256 tokenId);

    address last_operator;
    address last_from;
    uint256 last_token;
    bytes last_data;
    uint256 calls;
    uint256 mode;

    function set_mode(uint256 m) external {
        mode = m;
    }

    function onERC721Received(address operator, address from, uint256 tokenId, bytes calldata data)
        external
        returns (bytes4)
    {
        if (mode == 2) revert Refused(tokenId);
        last_operator = operator;
        last_from = from;
        last_token = tokenId;
        last_data = data;
        calls += 1;
        return mode == 1 ? bytes4(0xdeadbeef) : bytes4(0x150b7a02);
    }
}
