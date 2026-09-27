// SPDX-License-Identifier: MIT
// Benchmark: Solady's ERC1155 with one templated URI, open minting as in Solady's own
// mocks, and burning by the holder or an approved operator. Mirrors solady_erc1155.lithe.
pragma solidity ^0.8.24;

import {ERC1155} from "solady/tokens/ERC1155.sol";

contract SoladyMultiToken is ERC1155 {
    function uri(uint256) public pure override returns (string memory) {
        return "https://multi.example/{id}.json";
    }

    function mint(address to, uint256 id, uint256 amount, bytes calldata data) public {
        _mint(to, id, amount, data);
    }

    function mintBatch(address to, uint256[] calldata ids, uint256[] calldata amounts, bytes calldata data)
        public
    {
        _batchMint(to, ids, amounts, data);
    }

    function burn(address from, uint256 id, uint256 amount) public {
        _burn(msg.sender, from, id, amount);
    }

    function burnBatch(address from, uint256[] calldata ids, uint256[] calldata amounts) public {
        _batchBurn(msg.sender, from, ids, amounts);
    }
}
