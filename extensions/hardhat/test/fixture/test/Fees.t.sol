// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {Test} from "forge-std/Test.sol";

interface IFees {
    error FeeTooHigh(uint256 fee);

    function owner() external view returns (address);
}

contract FeesTest is Test {
    function test_deployArguments() public {
        IFees fees = IFees(deployCode("Fees", abi.encode(address(7), 250)));
        assertEq(fees.owner(), address(7));
    }

    function test_feeTooHigh() public {
        vm.expectRevert(abi.encodeWithSelector(IFees.FeeTooHigh.selector, 2000));
        deployCode("Fees", abi.encode(address(7), 2000));
    }
}
