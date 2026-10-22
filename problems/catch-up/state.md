# State

- **Stage:** Attack.

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 35 is a draw, and for even totals with N ≥ 12 every opening move draws. N = 33 and 34 (odd totals) are player-1 wins, only by opening 1 and 2 respectively. N = 31–35 go beyond the published N = 28; N = 33–35 come from one engine (`tiled-cuda`) and are not independently checked.
- **Blueprint** ([blueprint.md](blueprint.md)): L1–L3 at `conjecture`, goal statement approved; L3 (parity law) has a draft paper proof the refuter hasn't seen.
- **Ruled out** ([obstructions.md](obstructions.md)): O1–O3, induction by four on sets (even complete ones) and completeness as the characterization of draws.
- **Leads:** complete even-sum sets are draws up to max 21, with sparse exceptions beyond; most positions follow the parity rule "mover wins where a draw is impossible, draws where it is possible" (deviations at gaps ≤ 2 and the largest gaps). The invariant must be about positions (numbers left + gap), not starting sets.

## Claims

| Work | Resources | Since | Note |
|---|---|---|---|

## Next step

Line A1 (main), B1 near-pair switches: check value(S ⊎ {x, x}) = value(S) for x ≥ max(S) on multisets first, then whether adding {x, x+1} acts on a position's values as a function of the gaps g − 1, g, g + 1.

## Awaiting review

- **Compressed tiles?** Layer data compresses to 13–15% (zlib/lzma on N = 28's middle layer: ~6 bits of information per 32-bit row). Compressing tiles in RAM would keep N = 35 and 36 entirely in the 16 GB budget, with no disk. Needs the `zstd` crate (a download for the user to run).
- **N = 36?** Estimated 50–60 min, ~170 GB written to F: and ~230 GB read, peak ~55 GB of layer files (434 GB free), 16 GB RAM, GPU alone. Waiting for a go-ahead.
- `results/values-n27-32.md` repeats its rows for N = 30–32 at the end of the table (harmless; results are never edited).

## Last review

None yet.
