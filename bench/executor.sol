// SPDX-License-Identifier: MIT
// Benchmark: an order executor that consumes call results. Mirrors executor.lithe,
// which receives the results in continuations.
pragma solidity ^0.8.24;

interface IExchange {
    struct SwapResult {
        uint256 amount_out;
        uint256 fee;
    }

    function swap(uint256 amount_in, uint256 min_out) external returns (SwapResult memory);
    function deposit(uint256 amount) external returns (uint256);
    function split(uint256 shares) external returns (uint256, uint256);
}

contract Executor {
    struct Order {
        uint8 status;
        uint256 amount_in;
        uint256 amount_out;
        uint256 shares;
    }

    error AlreadyExecuted(uint256 id);
    error NotComplete(uint256 id);
    error TooLittle(uint256 amount_out, uint256 floor);

    event Executed(uint256 indexed id, uint256 amount_out, uint256 fee);
    event Deposited(uint256 indexed id, uint256 shares);

    IExchange exchange;
    uint256 floor;
    uint256 executed;
    uint256 total_out;
    uint256 left;
    uint256 right;
    mapping(uint256 => Order) orders;

    constructor(IExchange exchange_, uint256 floor_) {
        exchange = exchange_;
        floor = floor_;
    }

    function execute(uint256 id, uint256 amount, uint256 min_out) external {
        Order storage o = orders[id];
        if (o.status != 0) revert AlreadyExecuted(id);
        o.status = 1;
        o.amount_in = amount;
        IExchange.SwapResult memory result = exchange.swap(amount, min_out);
        if (result.amount_out < floor) revert TooLittle(result.amount_out, floor);
        o.status = 2;
        o.amount_out = result.amount_out;
        executed += 1;
        total_out += result.amount_out;
        emit Executed(id, result.amount_out, result.fee);
    }

    function execute_and_deposit(uint256 id, uint256 amount) external {
        Order storage o = orders[id];
        if (o.status != 0) revert AlreadyExecuted(id);
        o.status = 1;
        o.amount_in = amount;
        IExchange.SwapResult memory result = exchange.swap(amount, 0);
        o.status = 2;
        o.amount_out = result.amount_out;
        uint256 minted = exchange.deposit(result.amount_out);
        o.shares = minted;
        emit Deposited(id, minted);
    }

    function unwind(uint256 id) external {
        Order storage o = orders[id];
        if (o.status != 2) revert NotComplete(id);
        (uint256 a, uint256 b) = exchange.split(o.shares);
        o.status = 3;
        left += a;
        right += b;
    }

    function order_of(uint256 id) external view returns (Order memory) {
        return orders[id];
    }
}
