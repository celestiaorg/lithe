// SPDX-License-Identifier: MIT
// Benchmark: Solady's ERC20 with EIP-2612 permits and its default Permit2 allowance, a
// fixed name, and open minting and burning as in Solady's own mocks. Mirrors
// solady_erc20.lithe.
pragma solidity ^0.8.24;

import {ERC20} from "solady/tokens/ERC20.sol";

contract SoladyToken is ERC20 {
    function name() public pure override returns (string memory) {
        return "Solady Token";
    }

    function symbol() public pure override returns (string memory) {
        return "SOLADY";
    }

    function _constantNameHash() internal pure override returns (bytes32) {
        return keccak256("Solady Token");
    }

    function mint(address to, uint256 amount) public {
        _mint(to, amount);
    }

    function burn(uint256 amount) public {
        _burn(msg.sender, amount);
    }
}
