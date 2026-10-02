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

    function tag(uint256 tokenId, string calldata traitType) external {
        if (bytes(traitType).length == 0) revert EmptyTrait("trait type is empty");
        if (tokenId >= minted) revert AttributeNotFound(tokenId, traitType);
        tagged = tokenId;
    }

    function background(uint256 tokenId) external view returns (uint256) {
        if (tokenId >= minted) revert AttributeNotFound(tokenId, "Background");
        return tokenId;
    }

    function check(uint256[] calldata ids) external view returns (uint256) {
        for (uint256 i = 0; i < ids.length; i++) {
            if (ids[i] >= minted) revert NotMinted(ids);
        }
        return ids.length;
    }
}
