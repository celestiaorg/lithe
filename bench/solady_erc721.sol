// SPDX-License-Identifier: MIT
// Benchmark: Solady's ERC721 with URIs from a base and the id, open minting as in
// Solady's own mocks, and burning by the owner or an approved account. Mirrors
// solady_erc721.lithe.
pragma solidity ^0.8.24;

import {ERC721} from "solady/tokens/ERC721.sol";
import {LibString} from "solady/utils/LibString.sol";

contract SoladyNFT is ERC721 {
    function name() public pure override returns (string memory) {
        return "Solady NFT";
    }

    function symbol() public pure override returns (string memory) {
        return "SNFT";
    }

    function tokenURI(uint256 id) public view override returns (string memory) {
        if (!_exists(id)) revert TokenDoesNotExist();
        return string.concat("https://nft.example/", LibString.toString(id));
    }

    function mint(address to, uint256 id) public {
        _mint(to, id);
    }

    function safeMint(address to, uint256 id, bytes calldata data) public {
        _safeMint(to, id, data);
    }

    function burn(uint256 id) public {
        _burn(msg.sender, id);
    }
}
