// SPDX-License-Identifier: MIT
// Benchmark: structs in mappings, packed. Mirrors records.lithe.
pragma solidity ^0.8.24;

contract Records {
    struct Inner {
        bool flag;
        int16 delta;
    }

    struct Order {
        uint8 status;
        address owner;
        uint256 amount;
        uint32 small;
        Inner inner;
        uint64 last;
    }

    struct Pair {
        uint128 a;
        uint128 b;
    }

    error Missing(uint256 id);

    event Placed(uint256 indexed id, uint256 amount, uint8 status);

    uint256 count;
    mapping(uint256 => Order) orders;
    mapping(address => mapping(uint256 => Pair)) pairs;
    uint8 tail;
    Pair head;
    Order top;

    function fresh(address owner, uint256 amount, int16 delta) internal pure returns (Order memory) {
        return Order(2, owner, amount, 5, Inner(delta < 0, delta), 9);
    }

    function split(uint128 total) internal pure returns (Pair memory) {
        return Pair(total / 2, total - total / 2);
    }

    function place(uint256 id, uint256 amount, uint32 small, int16 delta) external {
        orders[id] = Order(1, msg.sender, amount, small, Inner(true, delta), 7);
        count += 1;
        emit Placed(id, orders[id].amount, orders[id].status);
    }

    function bump(uint256 id, uint256 by) external {
        Order storage o = orders[id];
        if (o.status == 0) revert Missing(id);
        o.status += 1;
        o.amount += by;
        o.inner.delta -= 1;
        o.last += 1;
        tail = o.status;
    }

    function copy(uint256 src, uint256 dst) external {
        Order memory o = orders[src];
        orders[dst] = o;
        orders[dst].inner = Inner(!o.inner.flag, o.inner.delta);
    }

    function pairSet(uint256 k, uint128 a, uint128 b) external {
        pairs[msg.sender][k] = Pair(a, b);
        pairs[msg.sender][k + 1].b = b;
    }

    function headSet(uint128 total) external {
        head = split(total);
        pairs[msg.sender][0] = split(total + 1);
    }

    function headSwap() external {
        head = Pair(head.b, head.a);
    }

    function oddOf(uint128 total) external pure returns (uint128) {
        Pair memory p = split(total);
        return p.b - split(total).a;
    }

    function promote(uint256 id) external {
        top = orders[id];
    }

    function resetTop(uint256 amount, int16 delta) external {
        top = fresh(msg.sender, amount, delta);
    }

    function topOrder() external view returns (Order memory) {
        return top;
    }

    function headPair() external view returns (Pair memory) {
        return head;
    }

    function orderOf(uint256 id) external view returns (Order memory) {
        return orders[id];
    }

    function statusOf(uint256 id) external view returns (uint8) {
        return orders[id].status;
    }

    function deltaOf(uint256 id) external view returns (int16) {
        return orders[id].inner.delta;
    }

    function pairOf(address who, uint256 k) external view returns (Pair memory) {
        return pairs[who][k];
    }
}
