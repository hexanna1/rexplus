#!/usr/bin/env python3
"""Exhaustively compare completion-hypergraph and direct Rex+ on 3x3."""

from functools import lru_cache


BLACK, WHITE = 0, 1
SIZE = 3
CELLS = SIZE * SIZE
BOARD = (1 << CELLS) - 1
DIRECTIONS = ((0, 1), (0, -1), (1, 0), (-1, 0), (-1, 1), (1, -1))

NEIGHBORS = []
for point in range(CELLS):
    row, column = divmod(point, SIZE)
    adjacent = 0
    for dr, dc in DIRECTIONS:
        rr, cc = row + dr, column + dc
        if 0 <= rr < SIZE and 0 <= cc < SIZE:
            adjacent |= 1 << (rr * SIZE + cc)
    NEIGHBORS.append(adjacent)


def connected(stones, color):
    if color == BLACK:
        first = (1 << SIZE) - 1
        second = first << (CELLS - SIZE)
    else:
        first = sum(1 << (row * SIZE) for row in range(SIZE))
        second = first << (SIZE - 1)
    frontier = seen = stones & first
    while frontier:
        if frontier & second:
            return True
        adjacent = 0
        work = frontier
        while work:
            cell = work & -work
            work -= cell
            adjacent |= NEIGHBORS[cell.bit_length() - 1]
        frontier = adjacent & stones & ~seen
        seen |= frontier
    return False


@lru_cache(maxsize=None)
def direct_win(black, white, color):
    remaining = BOARD & ~(black | white)
    batch = remaining
    while batch:
        own = (black if color == BLACK else white) | batch
        if not connected(own, color):
            next_black = own if color == BLACK else black
            next_white = own if color == WHITE else white
            if not direct_win(next_black, next_white, color ^ 1):
                return True
        batch = (batch - 1) & remaining
    return False


def minimal_completions(base_white, remaining):
    result = []
    subset = remaining
    while subset:
        if connected(base_white | subset, WHITE):
            work = subset
            minimal = True
            while work and minimal:
                cell = work & -work
                work -= cell
                minimal = not connected(base_white | (subset & ~cell), WHITE)
            if minimal:
                result.append(subset)
        subset = (subset - 1) & remaining
    return tuple(sorted(result))


def hypergraph_win(remaining, initial_edges, initial_color):
    @lru_cache(maxsize=None)
    def win(left, edges, color):
        work = left
        while work:
            cell = work & -work
            work -= cell
            if color == BLACK:
                child = tuple(edge for edge in edges if not edge & cell)
                if not child:
                    continue
            else:
                reduced = [edge & ~cell for edge in edges]
                if not all(reduced):
                    continue
                child = []
                for edge in sorted(set(reduced), key=lambda e: (e.bit_count(), e)):
                    if not any(not kept & ~edge for kept in child):
                        child.append(edge)
                child = tuple(sorted(child))
            rest = left & ~cell
            if (not win(rest, child, color ^ 1)
                    or win(rest, child, color)):
                return True
        return False

    return win(remaining, initial_edges, initial_color)


def normalized_hypergraph_win(remaining, initial_edges, initial_color):
    @lru_cache(maxsize=None)
    def win(active, isolates, edges, color):
        if isolates and (not win(active, False, edges, color ^ 1)
                         or win(active, False, edges, color)):
            return True
        work = active
        while work:
            cell = work & -work
            work -= cell
            if color == BLACK:
                child = tuple(edge for edge in edges if not edge & cell)
                if not child:
                    continue
            else:
                reduced = [edge & ~cell for edge in edges]
                if not all(reduced):
                    continue
                child = []
                for edge in sorted(set(reduced), key=lambda e: (e.bit_count(), e)):
                    if not any(not kept & ~edge for kept in child):
                        child.append(edge)
                child = tuple(sorted(child))
            rest = active & ~cell
            child_active = 0
            for edge in child:
                child_active |= edge
            child_isolates = isolates or bool(rest & ~child_active)
            if (not win(child_active, child_isolates, child, color ^ 1)
                    or win(child_active, child_isolates, child, color)):
                return True
        return False

    active = 0
    for edge in initial_edges:
        active |= edge
    return win(active, bool(remaining & ~active), initial_edges,
               initial_color)


def main():
    positions = 0
    for code in range(3 ** CELLS):
        value = code
        black = white = 0
        for point in range(CELLS):
            digit = value % 3
            value //= 3
            if digit == 1:
                black |= 1 << point
            elif digit == 2:
                white |= 1 << point
        if connected(black, BLACK) or connected(white, WHITE):
            continue
        remaining = BOARD & ~(black | white)
        edges = minimal_completions(white, remaining)
        assert bool(edges) == (not connected(black, BLACK))
        for color in (BLACK, WHITE):
            direct = direct_win(black, white, color)
            assert hypergraph_win(remaining, edges, color) == direct
            assert normalized_hypergraph_win(remaining, edges, color) == direct
        positions += 1
    print(f"verified {positions} positions and both turns")


if __name__ == "__main__":
    main()
