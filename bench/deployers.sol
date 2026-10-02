// SPDX-License-Identifier: MIT
// Benchmark: contracts from creation code built at runtime, with OpenZeppelin's `Clones`
// and Solady's `SSTORE2` and `CREATE3`. Mirrors deployers.lithe.
pragma solidity ^0.8.24;

import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {SSTORE2} from "solady/utils/SSTORE2.sol";
import {CREATE3} from "solady/utils/CREATE3.sol";

contract Deployers {
    address public last;
    address pointer;

    function clone(address implementation) external {
        last = Clones.clone(implementation);
    }

    function cloneWithArgs(address implementation, bytes calldata args) external {
        last = Clones.cloneWithImmutableArgs(implementation, args);
    }

    function cloneDeterministic(address implementation, bytes32 salt) external returns (address) {
        last = Clones.cloneDeterministic(implementation, salt);
        return last;
    }

    function predictClone(address implementation, bytes32 salt) external view returns (address) {
        return Clones.predictDeterministicAddress(implementation, salt);
    }

    function argsOf(address instance) external view returns (bytes memory) {
        return Clones.fetchCloneArgs(instance);
    }

    function write(bytes calldata data) external {
        pointer = SSTORE2.write(data);
    }

    function writeCounterfactual(bytes calldata data, bytes32 salt) external returns (address) {
        pointer = SSTORE2.writeCounterfactual(data, salt);
        return pointer;
    }

    function read() external view returns (bytes memory) {
        return SSTORE2.read(pointer);
    }

    function deploy3(bytes calldata code, bytes32 salt) external payable returns (address) {
        last = CREATE3.deployDeterministic(msg.value, code, salt);
        return last;
    }

    function predict3(bytes32 salt) external view returns (address) {
        return CREATE3.predictDeterministicAddress(salt);
    }
}
