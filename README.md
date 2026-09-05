# Rex+

The empty 5×5 Rex+ board is a **P-position**: the first player loses under
optimal play. The supplied code verifies this result by exact search. The empty
2×2, 3×3, and 4×4 boards are P-positions as well.

## Rules

Rex+ is reverse Hex with set-valued turns. Each turn places a nonempty set of
stones of the player's color on empty cells. A player loses by connecting
their own opposite sides. Black connects north–south; White connects west–east.
Coordinates run from `a1` to `e5`, with letters for columns and numbers for rows.

## Verify

Requirements: a C++20 compiler, CMake, and Python 3.10 or newer. Python uses
only the standard library.

```sh
cmake -S . -B build
cmake --build build -j2
python3 -B verify.py
```

The verifier generates all 255 candidate first sets and recomputes the
outcomes needed to rule them out. Successful verification ends with
`verified all 255 exact roots`. `--jobs N` controls concurrent searches;
the two largest searches run sequentially.

`ctest --test-dir build` runs the small-board equivalence check alone.
Full verification needs several gigabytes of available memory.

## Proof

Veronika Keras's unique-winning-set theorem implies that a winning first set
on the empty square board must be invariant under its color-preserving and
color-exchanging symmetries. On 5×5, these partition the cells into nine
orbits. Their unions give 512 sets; Hex duality pairs connecting and
nonconnecting sets by complementation. Excluding the empty set leaves 255
nonconnecting candidate first sets.

For each candidate, the verification proves White wins after Black places
that set. Therefore none can be a winning first set, proving the empty board
is P. The rules and reduction follow Keras,
[*The Combinatorial Game Theory of Rex+*](https://arxiv.org/abs/2606.02468).

The records in `certificates/first-move-witnesses.txt` supply White replies
for 253 candidates. Each reply is verified by proving the resulting
Black-to-move position loses. The remaining two candidates and their winning
replies are recorded in `certificates/hard-roots.txt` and solved by the
completion-hypergraph engine.

## Search

Both engines generate a set-valued turn one cell at a time. After a safe
placement, the mover may continue the batch or end it. For player `p`,

```
win_p(s) = OR over safe cells x of
           (win_p(s + p{x}) OR NOT win_other(s + p{x})).
```

Every safe batch has safe prefixes because connection is monotone. This
recurrence therefore covers every nonempty legal set, without enumerating
all subsets as separate moves.

`rexplus.cpp` searches board positions with exact transposition tables,
symmetry, monotone bounds, and winning-set deductions.

`completion_hypergraph.cpp` represents a position by the inclusion-minimal
sets of empty cells that would complete White's connection. White taking a
cell removes it from each set and then removes redundant supersets. Black
taking a cell deletes every set containing it. White connects exactly when
an empty set appears; by Hex duality, Black connects exactly when no set
remains. Cells outside the edges are dead for both players. The Rex+ dead-cell
identity reduces any positive number of them to one. The search state is
therefore the hypergraph, whether a dead cell remains, and the player to move.
Equal search states share their computed outcomes. Vertices appearing
in exactly the same edges are interchangeable, so the search considers one
representative of each such class at a node.

The independent Python audit enumerates all 11,741 nonterminal 3×3 boards
and both players, comparing the quotient with direct full-batch minimax.
Full verification also compares the C++ engines on fixed positions.

## Individual positions

```sh
build/rexplus_solver 5 --black a1,b2 --white c2 --to-play black
build/rexplus_hypergraph 5 c3 - white
```

Use `-` for an empty stone set. The direct solver accepts `--tt-mb N` and
`--time SECONDS`; reaching a limit returns `unknown`. The hypergraph engine
requires at most 24 empty cells.
