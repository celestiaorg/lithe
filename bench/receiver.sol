// SPDX-License-Identifier: MIT
// Benchmark: an ERC-721 receiver that records each delivery. Mirrors receiver.lithe.
// In mode 1 it answers with the wrong selector; in mode 2 it refuses with a reason.
pragma solidity ^0.8.24;

contract Receiver {
    error Refused(uint256 tokenId);

    address lastOperator;
    address lastFrom;
    uint256 lastToken;
    bytes lastData;
    uint256 calls;
    uint256 mode;

    function setMode(uint256 m) external {
        mode = m;
    }

    function onERC721Received(address operator, address from, uint256 tokenId, bytes calldata data)
        external
        returns (bytes4)
    {
        if (mode == 2) revert Refused(tokenId);
        lastOperator = operator;
        lastFrom = from;
        lastToken = tokenId;
        lastData = data;
        calls += 1;
        return mode == 1 ? bytes4(0xdeadbeef) : bytes4(0x150b7a02);
    }
}
