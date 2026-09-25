// SPDX-License-Identifier: MIT
// Benchmark: lists of strings and bytes through another contract, and a payload decoded
// by a contract that another contract calls. Mirrors relay.lithe; calls texts.
pragma solidity ^0.8.24;

interface ITexts {
    function echo(string[] calldata xs) external view returns (string[] memory);
    function decoded(bytes calldata data) external view returns (bytes[] memory);
}

interface IKeeper {
    function echo(string[] calldata xs) external returns (string[] memory);
}

contract Relay {
    string[] names_;
    string[] kept_;
    uint256 count_;

    function ask(ITexts t, string[] calldata xs) external {
        string[] memory back = t.echo(xs);
        names_ = back;
    }

    function send(IKeeper k, string[] calldata xs) external {
        string[] memory back = k.echo(xs);
        kept_ = back;
    }

    function unpack(ITexts t, bytes calldata payload) external {
        count_ = t.decoded(payload).length;
    }

    function names() external view returns (string[] memory) {
        return names_;
    }

    function kept() external view returns (string[] memory) {
        return kept_;
    }

    function count() external view returns (uint256) {
        return count_;
    }
}
