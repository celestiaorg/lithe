// SPDX-License-Identifier: MIT
// Benchmark: selectors and ERC-165 ids taken from interfaces, as constants. Mirrors
// selectors.lithe.
pragma solidity ^0.8.24;

interface IERC165 {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface Vault {
    function deposit(uint256 amount) external;
    function withdraw(uint256 amount, address to) external;
    function balanceOf(address who) external view returns (uint256);
}

interface Token {
    function transfer(address to, uint256 amount) external returns (bool);
}

contract Selectors {
    error Unrouted(bytes4);

    mapping(bytes4 => uint256) handled_;

    function supportsInterface(bytes4 interfaceId) external pure returns (bool) {
        return interfaceId == type(Vault).interfaceId || interfaceId == type(IERC165).interfaceId;
    }

    function handle(bytes4 selector) external {
        if (
            selector != Vault.deposit.selector && selector != Vault.withdraw.selector
                && selector != Token.transfer.selector
        ) revert Unrouted(selector);
        handled_[selector] += 1;
    }

    function handled(bytes4 selector) external view returns (uint256) {
        return handled_[selector];
    }

    function transfer_call(address to, uint256 amount) external pure returns (bytes memory) {
        return abi.encodeWithSelector(Token.transfer.selector, to, amount);
    }

    function ids() external pure returns (bytes4, bytes4, bytes4) {
        return (type(Vault).interfaceId, type(Token).interfaceId, Vault.balanceOf.selector);
    }
}
