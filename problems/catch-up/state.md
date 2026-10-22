# State

- **Stage:** Explore.
- **Loop:** stopped: not started yet. Iterations since last review: 0. Reviews in a row without metric movement: 0.

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 32 is a draw, and for N ≥ 12 every opening move draws. N = 31 and 32 are new.
- **Proved on paper:** L3, the parity law ([blueprint.md](blueprint.md)). Formalized: only the statement.
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3, induction by four on sets (even complete ones) and completeness as the characterization of draws.
- **Leads:** complete even-sum sets are draws up to max 21, with sparse exceptions beyond; most positions follow the parity rule "mover wins where a draw is impossible, draws where it is possible" (deviations at gaps ≤ 2 and the largest gaps). The invariant must be about positions (numbers left + gap), not starting sets.

## Claims

| Thread | Session | Since | Note |
|---|---|---|---|
| Solver: GPU tile streaming for N ≥ 32, then N = 33–36 | solver session | 2026-10-22 | `cuda` engine done for N ≤ 31 (results/values-n1-31.md); from N = 32 two layers exceed 8 GB, so tiles must stream |

## Next step

Line A1 (main), survey/conjecture, B1 near-pair switches: check value(S ⊎ {x, x}) = value(S) for x ≥ max(S) on multisets first, then whether adding {x, x+1} acts on a position's values as a function of the gaps g − 1, g, g + 1.

## Awaiting review

None.

## Last review

None yet.
