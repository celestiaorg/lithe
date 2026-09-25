// SPDX-License-Identifier: MIT
// Benchmark: token traits whose errors carry strings and lists. Mirrors traits.lithe.
pragma solidity ^0.8.24;

contract Traits {
    error EmptyTrait(string);
    error AttributeNotFound(uint256 tokenId, string traitType);
    error NotMinted(uint256[]);

    uint256 minted;
    uint256 tagged;

    function mint(uint256 count) external {
        minted += count;
    }

    function tag(uint256 token_id, string calldata trait_type) external {
        if (bytes(trait_type).length == 0) revert EmptyTrait("trait type is empty");
        if (token_id >= minted) revert AttributeNotFound(token_id, trait_type);
        tagged = token_id;
    }

    function background(uint256 token_id) external view returns (uint256) {
        if (token_id >= minted) revert AttributeNotFound(token_id, "Background");
        return token_id;
    }

    function check(uint256[] calldata ids) external view returns (uint256) {
        for (uint256 i = 0; i < ids.length; i++) {
            if (ids[i] >= minted) revert NotMinted(ids);
        }
        return ids.length;
    }
}
