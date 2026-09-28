// SPDX-License-Identifier: MIT
// Benchmark: the contract's own balance and the blob base fee. Mirrors env.lithe.
pragma solidity ^0.8.24;

contract Env {
    uint256 deposits;

    function deposit() external payable returns (uint256) {
        deposits += 1;
        return address(this).balance;
    }

    function blob_fee() external view returns (uint256) {
        return block.blobbasefee;
    }
}
