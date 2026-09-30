// SPDX-License-Identifier: MIT
// Benchmark: a subscription calendar on Solady's DateTimeLib. Mirrors date_time.lithe.
pragma solidity ^0.8.24;

import {DateTimeLib} from "solady/utils/DateTimeLib.sol";

contract Billing {
    uint256 private started;
    uint256 private renews;

    function start_on(uint256 year, uint256 month, uint256 day) external {
        uint256 t = DateTimeLib.dateToTimestamp(year, month, day);
        started = t;
        renews = t;
    }

    function renew(uint256 months) external {
        renews = DateTimeLib.addMonths(renews, months);
    }

    function extend(uint256 count) external {
        renews = DateTimeLib.addYears(renews, count);
    }

    function months_active(uint256 now_) external view returns (uint256) {
        return DateTimeLib.diffMonths(started, now_);
    }

    function years_active(uint256 now_) external view returns (uint256) {
        return DateTimeLib.diffYears(started, now_);
    }

    function renewal_date() external view returns (uint256, uint256, uint256) {
        return DateTimeLib.timestampToDate(renews);
    }

    function stamp(uint256 year, uint256 month, uint256 day, uint256 hour, uint256 minute, uint256 second)
        external
        pure
        returns (uint256)
    {
        return DateTimeLib.dateTimeToTimestamp(year, month, day, hour, minute, second);
    }

    function parts(uint256 t) external pure returns (uint256, uint256, uint256, uint256, uint256, uint256) {
        return DateTimeLib.timestampToDateTime(t);
    }

    function weekday_of(uint256 t) external pure returns (uint256) {
        return DateTimeLib.weekday(t);
    }

    function valid(uint256 year, uint256 month, uint256 day) external pure returns (bool) {
        return DateTimeLib.isSupportedDate(year, month, day);
    }

    function days_in(uint256 year, uint256 month) external pure returns (uint256) {
        return DateTimeLib.daysInMonth(year, month);
    }
}
