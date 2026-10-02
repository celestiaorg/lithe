// SPDX-License-Identifier: MIT
// Benchmark: generic tallies in namespaced storage. Mirrors tally.lithe, where one
// generic module serves both key types.
pragma solidity ^0.8.24;

contract Tally {
    error ZeroWeight();

    struct AddressTally {
        mapping(address => uint256) counts;
        uint256 total;
    }

    struct Bytes32Tally {
        mapping(bytes32 => uint256) counts;
        uint256 total;
    }

    /// @custom:storage-location erc7201:bench.votes
    struct VotesStorage {
        AddressTally byVoter;
        Bytes32Tally byTopic;
    }

    // keccak256(abi.encode(uint256(keccak256("bench.votes")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant VOTES = 0x5908b0942d9295b8a877743dc654085399bec97ca9791ab414d36d912ee7e400;

    function _votes() private pure returns (VotesStorage storage $) {
        assembly {
            $.slot := VOTES
        }
    }

    function vote(bytes32 topic, uint256 weight) external {
        if (weight == 0) revert ZeroWeight();
        VotesStorage storage $ = _votes();
        $.byVoter.counts[msg.sender] += weight;
        $.byVoter.total += weight;
        $.byTopic.counts[topic] += weight;
        $.byTopic.total += weight;
    }

    function votesOf(address voter) external view returns (uint256) {
        return _votes().byVoter.counts[voter];
    }

    function votesFor(bytes32 topic) external view returns (uint256) {
        return _votes().byTopic.counts[topic];
    }

    function totalVotes() external view returns (uint256) {
        return _votes().byTopic.total;
    }
}
