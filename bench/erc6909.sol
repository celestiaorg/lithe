// SPDX-License-Identifier: MIT
// Benchmark: OpenZeppelin's ERC6909 with token supply, metadata, and content URIs, and an
// owner who mints and describes ids; holders, their operators, and spenders burn.
// Mirrors erc6909.lithe.
pragma solidity ^0.8.24;

import {ERC6909} from "@openzeppelin/contracts/token/ERC6909/ERC6909.sol";
import {ERC6909TokenSupply} from "@openzeppelin/contracts/token/ERC6909/extensions/ERC6909TokenSupply.sol";
import {ERC6909Metadata} from "@openzeppelin/contracts/token/ERC6909/extensions/ERC6909Metadata.sol";
import {ERC6909ContentURI} from "@openzeppelin/contracts/token/ERC6909/extensions/ERC6909ContentURI.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";

contract BenchClaims is ERC6909TokenSupply, ERC6909Metadata, ERC6909ContentURI, Ownable {
    constructor(address initialOwner) Ownable(initialOwner) {
        _setContractURI("https://bench.example/claims.json");
    }

    function mint(address to, uint256 id, uint256 amount) public onlyOwner {
        _mint(to, id, amount);
    }

    function burn(address from, uint256 id, uint256 amount) public {
        address caller = _msgSender();
        if (from != caller && !isOperator(from, caller)) {
            _spendAllowance(from, caller, id, amount);
        }
        _burn(from, id, amount);
    }

    function describe(uint256 id, string memory name_, string memory symbol_, uint8 decimals_, string memory uri)
        public
        onlyOwner
    {
        _setName(id, name_);
        _setSymbol(id, symbol_);
        _setDecimals(id, decimals_);
        _setTokenURI(id, uri);
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        override(ERC6909TokenSupply, ERC6909Metadata, ERC6909ContentURI)
        returns (bool)
    {
        return super.supportsInterface(interfaceId);
    }

    function _update(address from, address to, uint256 id, uint256 amount)
        internal
        override(ERC6909, ERC6909TokenSupply)
    {
        super._update(from, to, id, amount);
    }
}
