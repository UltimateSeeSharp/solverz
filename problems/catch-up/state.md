# State

- **Stage:** Attack.

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 32 is a draw, and for N ≥ 12 every opening move draws. N = 31 and 32 go beyond the published N = 28.
- **Blueprint** ([blueprint.md](blueprint.md)): L1–L3 at `conjecture`, goal statement approved; L3 (parity law) has a draft paper proof the refuter hasn't seen.
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3, induction by four on sets (even complete ones) and completeness as the characterization of draws.
- **Leads:** complete even-sum sets are draws up to max 21, with sparse exceptions beyond; most positions follow the parity rule "mover wins where a draw is impossible, draws where it is possible" (deviations at gaps ≤ 2 and the largest gaps). The invariant must be about positions (numbers left + gap), not starting sets.

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|
| Solver: compact rows + GPU tile streaming for N ≥ 32, then N = 33–36 (tiled-cuda session) | GPU; RAM and disk for streamed tiles | 2026-10-22 | `cuda` engine done for N ≤ 31 (results/values-n1-31.md); building `tiled_cuda`: only reachable-parity gaps, base-3 packed, 4 B/row; tiles stream through RAM/disk |

## Next step

Line A1 (main), B1 near-pair switches: check value(S ⊎ {x, x}) = value(S) for x ≥ max(S) on multisets first, then whether adding {x, x+1} acts on a position's values as a function of the gaps g − 1, g, g + 1.

## Awaiting review

None.

## Last review

None yet.
