// SPDX-License-Identifier: MIT
// Benchmark: an order executor that consumes call results. Mirrors executor.lithe,
// which receives the results in continuations.
pragma solidity ^0.8.24;

interface IExchange {
    struct SwapResult {
        uint256 amountOut;
        uint256 fee;
    }

    function swap(uint256 amountIn, uint256 minOut) external returns (SwapResult memory);
    function deposit(uint256 amount) external returns (uint256);
    function split(uint256 shares) external returns (uint256, uint256);
}

contract Executor {
    struct Order {
        uint8 status;
        uint256 amountIn;
        uint256 amountOut;
        uint256 shares;
    }

    error AlreadyExecuted(uint256 id);
    error NotComplete(uint256 id);
    error TooLittle(uint256 amountOut, uint256 floor);

    event Executed(uint256 indexed id, uint256 amountOut, uint256 fee);
    event Deposited(uint256 indexed id, uint256 shares);

    IExchange immutable exchange;
    uint256 immutable floor;
    uint256 executed;
    uint256 totalOut;
    uint256 left;
    uint256 right;
    mapping(uint256 => Order) orders;

    constructor(IExchange exchange_, uint256 floor_) {
        exchange = exchange_;
        floor = floor_;
    }

    function execute(uint256 id, uint256 amount, uint256 minOut) external {
        Order storage o = orders[id];
        if (o.status != 0) revert AlreadyExecuted(id);
        o.status = 1;
        o.amountIn = amount;
        IExchange.SwapResult memory result = exchange.swap(amount, minOut);
        if (result.amountOut < floor) revert TooLittle(result.amountOut, floor);
        o.status = 2;
        o.amountOut = result.amountOut;
        executed += 1;
        totalOut += result.amountOut;
        emit Executed(id, result.amountOut, result.fee);
    }

    function executeAndDeposit(uint256 id, uint256 amount) external {
        Order storage o = orders[id];
        if (o.status != 0) revert AlreadyExecuted(id);
        o.status = 1;
        o.amountIn = amount;
        IExchange.SwapResult memory result = exchange.swap(amount, 0);
        o.status = 2;
        o.amountOut = result.amountOut;
        uint256 minted = exchange.deposit(result.amountOut);
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

    function orderOf(uint256 id) external view returns (Order memory) {
        return orders[id];
    }
}
