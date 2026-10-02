// SPDX-License-Identifier: MIT
// Benchmark: the target of dialer's raw calls. Mirrors book.lithe.
pragma solidity ^0.8.24;

contract Book {
    struct Order {
        uint256 id;
        string note;
        uint256[] legs;
    }

    error Rejected(uint256);

    mapping(uint256 => string) notes_;
    uint256 placed_;

    function place(Order[] calldata os) external returns (uint256[] memory ids) {
        ids = new uint256[](os.length);
        for (uint256 i = 0; i < os.length; i++) {
            if (os[i].legs.length == 0) revert Rejected(os[i].id);
            notes_[os[i].id] = os[i].note;
            ids[i] = os[i].id;
        }
        placed_ += os.length;
    }

    function noteOf(uint256 id) external view returns (string memory) {
        return notes_[id];
    }

    function placed() external view returns (uint256) {
        return placed_;
    }
}
