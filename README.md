# Rex+

The empty 5×5 and 6×6 Rex+ boards are **P-positions**: the first player loses
under optimal play. The supplied code verifies these results by exact search.
The empty 2×2, 3×3, and 4×4 boards are P-positions as well.

## Rules

Rex+ is reverse Hex with set-valued turns. Each turn places a nonempty set of
stones of the player's color on empty cells. A player loses by connecting
their own opposite sides. Black connects north–south; White connects west–east.
Letters denote columns and numbers denote rows.

## Verify

Requirements: a C++20 compiler, CMake, and Python 3.10 or newer. Python uses
only the standard library.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j2
python3 -B verify.py
python3 -B verify_six.py
```

`verify.py` checks all 255 required 5×5 roots. `verify_six.py` checks all
2,047 required 6×6 roots. The files in `certificates/` supply White replies;
each required outcome is recomputed.

The 6×6 verifier solves 1,926 tails with the direct solver and 115 with the
completion-hypergraph engine. For five further tails it generates four proof
DAGs and streams them into a separate checker. One DAG covers two physical
positions with the same connection function. A self-duality check handles
the last opening through a conditional winning prefix.

The 6×6 workflow runs two searches concurrently and keeps generated proofs
in pipes. No proof downloads or saved search checkpoints are needed.
`--jobs 1` runs searches sequentially. Search limits are configurable;
an unresolved query reports `unknown` and fails verification.
`ctest --test-dir build` runs the small-board equivalence audit alone.

## Proof

Veronika Keras's unique-winning-set theorem implies that a winning first set
on the empty square board must be invariant under its color-preserving and
color-exchanging symmetries. These partition the cells into nine orbits on
5×5 and twelve on 6×6. Their unions give 512 and 4,096 sets respectively.
Hex duality pairs connecting and nonconnecting sets by complementation.
Excluding the empty set leaves 255 and 2,047 nonconnecting candidates.

For each candidate, verification proves White wins after Black places that
set. None can therefore be a winning first set, proving the empty board is P.
The rules and reduction follow Keras,
[*The Combinatorial Game Theory of Rex+*](https://arxiv.org/abs/2606.02468).

For most candidates, White's proposed batch leaves a Black-to-move losing
tail. For the 6×6 corner pair, the verifier instead checks a nonterminal
White prefix whose connection predicate is color-self-dual under an explicit
permutation of every remaining cell. The two mover-relative values of the
tail agree. White can end the turn if Black loses, or continue it if White
wins. Thus the prefix extends to a winning complete batch without requiring
an individual outcome for the tail.

## Search

Both engines generate a set-valued turn one cell at a time. After a safe
placement, the mover may continue the batch or end it. For player `p`,

```
win_p(s) = OR over safe cells x of
           (win_p(s + p{x}) OR NOT win_other(s + p{x})).
```

Every safe batch has safe prefixes because connection is monotone. This
recurrence covers every nonempty legal set without enumerating all subsets
as separate moves.

`rexplus.cpp` searches board positions with exact transposition tables,
symmetry, monotone bounds, and winning-set deductions.

`completion_hypergraph.hpp` represents a position by the inclusion-minimal
sets of empty cells that would complete White's connection. White taking a
cell removes it from each set and then removes redundant supersets. Black
taking a cell deletes every set containing it. White connects when an empty
set appears; by Hex duality, Black connects when no set remains.

The completion API lives in `rexplus::completion`. `Position` owns the board
geometry and initial stones; `Solver` owns its graph pool, cached outcomes,
and query budget. Pass the position explicitly when constructing completions
or exporting proofs. Separate instances can be used in independent threads,
and the headers can be included in multiple translation units.

Cells outside the edges are dead for both players. Multiple dead cells are
equivalent to a single dead cell. If `(b,w)` records whether Black and White
can win on their turn, adding a dead cell gives `(b OR NOT w, w OR NOT b)`.
Active vertices are renumbered before interning so that equivalent edge sets
can share computed outcomes. Incidence dominance removes redundant choices.

Unfilling a stone of a color which alone wins preserves that color-only
result. The search reuses this deduction once both child outcomes are known;
the proof records the cofactor and both outcomes explicitly.

For a White completion family, `Phi = sum(2^-|E|)` below one half proves
White wins in either move order. This is the unbiased case of the monotone
Avoider criterion in Hefetz, Krivelevich, Stojaković and Szabó,
[*Avoider–Enforcer: The Rules of the Game*, Theorem 1.4](https://www.cs.tau.ac.il/~krivelev/Avoi-new.pdf).

To see why, retain the original completion terms even when they become
redundant. White takes a physical cell of minimum incident weight `d`.
This increases `Phi` by `d <= Phi`, leaving it below one, so the move is
safe. The first cell in Black's next batch had incident weight at least `d`
before White's move; its weight cannot have decreased. Deleting its terms
therefore restores the previous bound on `Phi`. Further Black placements
only lower it. This gives White a safe strategy throughout the finite game.
Dead cells have weight zero and obey the same argument. If Black starts,
his first batch only lowers the initial potential.

The search also applies this criterion after each possible first Black
placement. If every such cofactor has potential below one half, Black loses
on the active domain. A legal White placement whose every Black reply
meets the same bound proves White wins. Existing dead cells can be included
in White's batch before ending the turn. A Black loss with dead cells also
requires an active White win, by the dead-cell formula above.

Small structural certificates retain at most five physical cells. Their
complement must be a winning batch for one color and a losing or illegal
batch for the other. The unique-winning-set theorem then proves that only
the first color wins. The checker verifies both residual games by literal
full-batch minimax, including every retained physical cell.

## Independent proof checking

`generate_proof.cpp` emits completion families, turn outcomes, cofactor maps,
and their derivations. `check_proof.cpp` independently reconstructs cofactors
and checks each inference, including potential inequalities, dominance,
physical dead options, and strict decrease in support. An independent
connectivity BDD binds each claimed result to its physical board.

The checker contains neither the producer's continuation search nor its
completion constructor. Its only whole-game enumeration is the bounded,
cached minimax on at most five cells used for structural certificates.

The Python audit enumerates every nonterminal 3×3 board and both players,
comparing the quotient with literal full-batch minimax. Full verification
also compares the C++ engines on fixed positions.

## Individual positions and proofs

```sh
build/rexplus_solver 6 --black b2 --white c3 --to-play black
build/rexplus_hypergraph 6 a1,b1,a2,f5,e6,f6 a4,a5,d6 black --fold-labels
build/rexplus_proof_generator 3 b1 c1 white - 30 512 | build/rexplus_proof_checker -
```

Use `-` for an empty stone set. The direct solver accepts `--tt-mb` and
`--time`. The hypergraph engine accepts `--pool-mb`, `--time`, and
`--fold-labels`; it requires at most 32 physical empty cells. Reaching a
search limit reports `unknown`.
