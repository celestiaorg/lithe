// SPDX-License-Identifier: MIT
// Benchmark: another contract reached only through low-level calls. Mirrors dialer.lithe;
// calls book.
pragma solidity ^0.8.24;

import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";

interface IBook {
    struct Order {
        uint256 id;
        string note;
        uint256[] legs;
    }

    function place(Order[] calldata os) external returns (uint256[] memory);
    function noteOf(uint256 id) external view returns (string memory);
}

contract Dialer is ReentrancyGuardTransient {
    uint256[] ids_;
    uint256 refused_;

    function place(address book, IBook.Order[] calldata os) external nonReentrant {
        (bool ok, bytes memory answer) = book.call(abi.encodeCall(IBook.place, (os)));
        if (ok) {
            ids_ = abi.decode(answer, (uint256[]));
        } else {
            if (answer.length != 36 || bytes4(answer) != 0x94064f91) {
                assembly {
                    revert(add(answer, 32), mload(answer))
                }
            }
            uint256 id;
            assembly {
                id := mload(add(answer, 36))
            }
            refused_ = id;
        }
    }

    function note(address book, uint256 id) external view returns (string memory) {
        (bool ok, bytes memory answer) = book.staticcall(abi.encodeWithSignature("noteOf(uint256)", id));
        require(ok);
        return abi.decode(answer, (string));
    }

    function ids() external view returns (uint256[] memory) {
        return ids_;
    }

    function refused() external view returns (uint256) {
        return refused_;
    }
}
