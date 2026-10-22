# State

The handoff between sessions: read first, rewritten at the end of every iteration. History lives in [log.md](log.md).

- **Stage:** Explore. Statement approved 2026-10-22; computation done through N = 32.
- **Updated:** 2026-10-22, after splitting the README into the template files.

## Where things stand

- **Computed** ([results/](results/)): every even-total N ≤ 32 is a draw, and for N ≥ 12 every opening move draws. N = 28 matches von Stengel's unpublished result; N = 31 and 32 are new. Odd totals: player 2 wins only at N = 9, 10, 14, 18; from N = 21 player 1 wins with opening 3 (N ≡ 1 mod 4) or 2 (N ≡ 2 mod 4).
- **Proved on paper:** the parity law ([blueprint.md](blueprint.md)). Formalized: only the statement.
- **Ruled out** ([obstructions.md](obstructions.md)): induction by four on sets, even on complete sets.
- **Leads:** complete even-sum sets are draws up to max 21, with sparse exceptions beyond; most positions follow the parity rule "mover wins where a draw is impossible, draws where it is possible" (deviations at gaps ≤ 2 and the largest gaps). The invariant must be about positions (numbers left + gap), not starting sets.

## Open threads

- Proof hunt (explore loop): backlog item 1 next.
- Solver (main session): CUDA engine waits for the CUDA install; then N = 33–36 with tiling + SSD.

## Next step

Backlog 1, near-pair switches: check value(S ⊎ {x, x}) = value(S) for x ≥ max(S) on multisets first, then whether adding {x, x+1} acts on a position's values as a function of the gaps g − 1, g, g + 1.

## Awaiting review

- CUDA Toolkit 13.3 install (user; download and installer steps are in the session that proposed it).
