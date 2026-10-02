// SPDX-License-Identifier: MIT
// Benchmark: an ERC-3156 flash borrower that records each loan, checks what it holds
// during it, and approves the repayment. Mirrors flash_borrower.lithe. In mode 1 it
// answers with the wrong value, in mode 2 it approves nothing, and in mode 3 it refuses
// with a reason.
pragma solidity ^0.8.24;

interface Token {
    function balanceOf(address account) external view returns (uint256);
    function approve(address spender, uint256 value) external returns (bool);
}

contract FlashBorrower {
    error Refused(uint256 amount);

    address lastInitiator;
    address lastToken;
    uint256 lastAmount;
    uint256 lastFee;
    bytes lastData;
    uint256 held;
    uint256 loans;
    uint256 mode;

    function setMode(uint256 m) external {
        mode = m;
    }

    function onFlashLoan(address initiator, address token, uint256 amount, uint256 fee, bytes calldata data)
        external
        returns (bytes32)
    {
        if (mode == 3) revert Refused(amount);
        lastInitiator = initiator;
        lastToken = token;
        lastAmount = amount;
        lastFee = fee;
        lastData = data;
        held = Token(token).balanceOf(address(this));
        loans += 1;
        if (mode != 2) Token(token).approve(token, amount + fee);
        return mode == 1 ? bytes32(0) : keccak256("ERC3156FlashBorrower.onFlashLoan");
    }
}
