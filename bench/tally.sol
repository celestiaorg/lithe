// SPDX-License-Identifier: MIT
// Benchmark: generic tallies in namespaced storage. Mirrors tally.lithe, where one
// generic module serves both key types.
pragma solidity ^0.8.24;

contract Tally {
    error Zero_weight();

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
        AddressTally by_voter;
        Bytes32Tally by_topic;
    }

    // keccak256(abi.encode(uint256(keccak256("bench.votes")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant VOTES = 0x5908b0942d9295b8a877743dc654085399bec97ca9791ab414d36d912ee7e400;

    function _votes() private pure returns (VotesStorage storage $) {
        assembly {
            $.slot := VOTES
        }
    }

    function vote(bytes32 topic, uint256 weight) external {
        if (weight == 0) revert Zero_weight();
        VotesStorage storage $ = _votes();
        $.by_voter.counts[msg.sender] += weight;
        $.by_voter.total += weight;
        $.by_topic.counts[topic] += weight;
        $.by_topic.total += weight;
    }

    function votes_of(address voter) external view returns (uint256) {
        return _votes().by_voter.counts[voter];
    }

    function votes_for(bytes32 topic) external view returns (uint256) {
        return _votes().by_topic.counts[topic];
    }

    function total_votes() external view returns (uint256) {
        return _votes().by_topic.total;
    }
}
