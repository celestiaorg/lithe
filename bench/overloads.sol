// SPDX-License-Identifier: MIT
// Benchmark: overloaded internal functions, picked by argument count and type, including
// ones that take a storage mapping; and overloaded entrypoints. Mirrors overloads.lithe.
pragma solidity ^0.8.24;

type Shares is uint256;

contract Overloads {
    mapping(address => uint256) balances;
    mapping(address => uint256) staked;
    uint256 total_;

    function fee(uint256 amount) internal pure returns (uint256) {
        return fee(amount, 30);
    }

    function fee(uint256 amount, uint256 bps) internal pure returns (uint256) {
        return amount * bps / 10_000;
    }

    function credit(mapping(address => uint256) storage ledger, address to, uint256 amount) internal {
        ledger[to] += amount;
    }

    function credit(address to, uint256 amount) internal {
        credit(balances, to, amount);
        total_ += amount;
    }

    function credit(address to, Shares amount) internal {
        credit(staked, to, Shares.unwrap(amount));
    }

    function move(mapping(address => uint256) storage ledger, address to, uint256 amount) internal {
        ledger[msg.sender] -= amount;
        credit(ledger, to, amount);
    }

    function move(address to, uint256 amount) internal {
        move(balances, to, amount);
    }

    function move(address to, Shares amount) internal {
        move(staked, to, Shares.unwrap(amount));
    }

    function deposit(uint256 amount) external {
        credit(msg.sender, amount - fee(amount));
    }

    function deposit(uint256 amount, uint256 bps) external {
        credit(msg.sender, amount - fee(amount, bps));
    }

    function stake(uint256 amount) external {
        credit(msg.sender, Shares.wrap(amount));
    }

    function transfer(address to, uint256 amount) external {
        move(to, amount);
    }

    function transferStaked(address to, uint256 amount) external {
        move(to, Shares.wrap(amount));
    }

    function balanceOf(address who) external view returns (uint256) {
        return balances[who];
    }

    function stakedOf(address who) external view returns (uint256) {
        return staked[who];
    }

    function total() external view returns (uint256) {
        return total_;
    }
}
