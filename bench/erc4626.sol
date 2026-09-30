// SPDX-License-Identifier: MIT
// Benchmark: OpenZeppelin's ERC-4626 vault with no decimals offset. Mirrors erc4626.lithe.
pragma solidity ^0.8.24;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";

contract BenchVault is ERC4626 {
    constructor(IERC20 asset_) ERC20("Bench Vault", "vBENCH") ERC4626(asset_) {}
}
