// SPDX-License-Identifier: MIT
// Benchmark: an ERC-1155 receiver that records each delivery. Mirrors receiver1155.lithe.
// In mode 1 it answers with the wrong selector; in mode 2 it refuses with a reason; in
// mode 3 it reverts without one.
pragma solidity ^0.8.24;

contract Receiver1155 {
    error Refused(uint256 count);

    address lastOperator;
    address lastFrom;
    uint256[] lastIds;
    uint256[] lastValues;
    bytes lastData;
    uint256 calls;
    uint256 mode;

    function setMode(uint256 m) external {
        mode = m;
    }

    function onERC1155Received(address operator, address from, uint256 id, uint256 value, bytes calldata data)
        external
        returns (bytes4)
    {
        uint256[] memory ids = new uint256[](1);
        uint256[] memory values = new uint256[](1);
        ids[0] = id;
        values[0] = value;
        keep(operator, from, ids, values, data);
        return mode == 1 ? bytes4(0xdeadbeef) : bytes4(0xf23a6e61);
    }

    function onERC1155BatchReceived(
        address operator,
        address from,
        uint256[] calldata ids,
        uint256[] calldata values,
        bytes calldata data
    ) external returns (bytes4) {
        keep(operator, from, ids, values, data);
        return mode == 1 ? bytes4(0xdeadbeef) : bytes4(0xbc197c81);
    }

    function keep(address operator, address from, uint256[] memory ids, uint256[] memory values, bytes memory data)
        internal
    {
        if (mode == 2) revert Refused(ids.length);
        if (mode == 3) revert();
        lastOperator = operator;
        lastFrom = from;
        lastIds = ids;
        lastValues = values;
        lastData = data;
        calls += 1;
    }
}
