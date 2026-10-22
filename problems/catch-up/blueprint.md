# Blueprint

Status: a step of the promotion ladder (`CLAUDE.md`, Workflow).

| ID | Name | Statement | Uses | Line | Lean | Status |
|---|---|---|---|---|---|---|
| L1 | Main conjecture | On {1..N} with 1 + … + N even, optimal play is a draw | — | all | `CatchUp.Conjecture` (statement) | computed (N ≤ 32); statement approved |
| L2 | Every opening draws | For even-total N ≥ 12, every opening move of player 1 still leads to a draw; implies L1 for those N | — | A3 | — | computed (12 ≤ N ≤ 32) |
| L3 | Parity law | In any position, the final score difference ≡ gap + sum of the numbers left (mod 2); so a draw needs gap ≡ sum left (mod 2) | — | A2 | — | paper proof |

## L1 Main conjecture
**Proof.** Open.
**Evidence.** Every even-total N ≤ 32 is a draw ([results/](results/)).

## L2 Every opening draws
**Proof.** Open.
**Evidence.** Every opening draws for each even-total N with 12 ≤ N ≤ 32 ([results/](results/)).

## L3 Parity law
**Proof.** The two players take every remaining number between them. If the mover's future picks sum to A and the opponent's to B, the mover's final lead is −gap + A − B, and A − B ≡ A + B = sum of the numbers left (mod 2). A draw means a final lead of 0, so gap ≡ sum left (mod 2).
**Evidence.** Consistent with `row_stats` (N ≤ 22): the most common rows alternate with the gap's parity. Not checked exhaustively.
