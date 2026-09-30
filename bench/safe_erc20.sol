// SPDX-License-Identifier: MIT
// Benchmark: token payments through OpenZeppelin's SafeERC20. Mirrors safe_erc20.lithe.
pragma solidity ^0.8.24;

import {SafeERC20, IERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";

contract Payer {
    using SafeERC20 for IERC20;

    function pay(address token, address to, uint256 amount) external {
        IERC20(token).safeTransfer(to, amount);
    }

    function pull(address token, address from, uint256 amount) external {
        IERC20(token).safeTransferFrom(from, address(this), amount);
    }

    function allow(address token, address spender, uint256 amount) external {
        IERC20(token).forceApprove(spender, amount);
    }
}
