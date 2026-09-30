// SPDX-License-Identifier: MIT
// Benchmark: role checks with roles as bits of one mask per account, as Solady's
// OwnableRoles keeps them, on OpenZeppelin's Ownable. Mirrors ownable_roles.lithe.
pragma solidity ^0.8.24;

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";

contract Minter is Ownable {
    event RolesUpdated(address indexed user, uint256 indexed roles);

    error Unauthorized();

    mapping(address => uint256) private _minted;
    bool private _paused;
    mapping(address => uint256) private _roles;

    uint256 private constant MINTER = 1 << 0;
    uint256 private constant PAUSER = 1 << 1;

    constructor() Ownable(msg.sender) {}

    function _update(address user, uint256 roles, bool add) private {
        uint256 next = add ? _roles[user] | roles : _roles[user] & ~roles;
        _roles[user] = next;
        emit RolesUpdated(user, next);
    }

    function grantRoles(address user, uint256 roles) external onlyOwner {
        _update(user, roles, true);
    }

    function revokeRoles(address user, uint256 roles) external onlyOwner {
        _update(user, roles, false);
    }

    function renounceRoles(uint256 roles) external {
        _update(msg.sender, roles, false);
    }

    function rolesOf(address user) external view returns (uint256) {
        return _roles[user];
    }

    function hasAnyRole(address user, uint256 roles) external view returns (bool) {
        return _roles[user] & roles != 0;
    }

    function hasAllRoles(address user, uint256 roles) external view returns (bool) {
        return _roles[user] & roles == roles;
    }

    function mint(address to, uint256 amount) external {
        if (_roles[msg.sender] & MINTER == 0) revert Unauthorized();
        _minted[to] += amount;
    }

    function minted(address who) external view returns (uint256) {
        return _minted[who];
    }

    function pause() external {
        if (owner() != msg.sender && _roles[msg.sender] & PAUSER == 0) revert Unauthorized();
        _paused = true;
    }

    function unpause() external {
        if (_roles[msg.sender] & (PAUSER | MINTER) == 0 && owner() != msg.sender) revert Unauthorized();
        _paused = false;
    }

    function paused() external view returns (bool) {
        return _paused;
    }
}
