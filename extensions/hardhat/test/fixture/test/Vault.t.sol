// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test} from "forge-std/Test.sol";

interface IVault {
    error Insufficient();

    function deposit() external payable;
    function withdraw(uint256 amount) external;
}

contract VaultTest is Test {
    IVault vault;

    function setUp() public {
        vault = IVault(deployCode("Vault"));
    }

    function test_withdraw() public {
        vault.deposit{value: 1 ether}();
        uint256 before = address(this).balance;
        vault.withdraw(0.4 ether);
        assertEq(address(this).balance, before + 0.4 ether);
    }

    function test_overdraw() public {
        vault.deposit{value: 1 ether}();
        vm.expectRevert(IVault.Insufficient.selector);
        vault.withdraw(2 ether);
    }

    receive() external payable {}
}
