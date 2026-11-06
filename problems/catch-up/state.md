# State

**Focus.** C1 (Lean `CatchUp.Goal`) reduces in Lean to each of these open statements; every route ends at the same barrier, the leader's defense in the low phase (understanding.md, Blocks).
- C119 (cheapest): ({1..N−1}, N) is not a mover win for every even-total N ≥ 13 (`conjecture_of_max_opening`, I33).
- C110, the one-hole band: odd blocks of 2k + 1 numbers minus any one, every deficit d ≤ k − 1 of the draw parity, every height (`conjecture_of_one_hole_band`; by C13 heights a ≤ k(2k + 1) + k suffice, `oneHoleBand_of_bounded_heights`). Data: every height for k ≤ 9 (E45). Lean has its high part from linear height for d = 0 and 1 ≤ d ≤ o + 1 − k with holes o ≥ k (`one_hole_block_draw_linear`, `one_hole_band_draw_linear`).
- C104, the low column (`conjecture_of_low_column`); C86, the band (`conjecture_of_band`); C92's three families (`conjecture_of_canonical_ray`); C74's ray (`conjecture_of_lower_ray`); C112, no controller wins (`conjecture_of_controller_games`, C111 verified).
Picture of the low phase (2026-11-05): the defender never needs turns of more than two numbers, the second after the largest number below its deficit (C114, C116, E41/E42/E44); along optimal play the attacker's best turns are short too, but its long turns must be answered and have no canonical shape (I27). The draw at even totals is universal across catch-up-like turn rules at large N (I31, C120, E46), and low and dense families are rule-robust, but play from {1..N} is forced into medium-height positions, where values depend on the exact rule (I34). No fixed defender rule works (ideators fresh05–08; I29 mirror dead).

**Next step.**
1. When the user starts the overnight session: run the queue under Optional long runs, one at a time, each stated as an experiment first.
2. Promote scratch-only results that a decision may rest on (each is recorded in the file named, with scratch evidence only; a committed experiment, two engines where possible, makes it count):
   - C116 on C104's low column, n ≤ 18: `scratch/a19/uni/src/bin/c104short.rs` (committed `ShortTurns`); record in C116.
   - I27's measures (turn lengths, slack, domination on the defender's tree, tempo, reactive change, the windowed attacker): `scratch/a19/short/{short,short2,short3,shape,react,tempo,reach,turnlen,ashape}.rs`, `scratch/a19/variant/extreme.rs`; recorded in I27, C114, C116.
   - Rule robustness (I31, I34): `scratch/a19/variant/{var,asym,order,window,partner2,level,vararr}.rs` (outputs `far.txt`, `edge.txt`), `scratch/a19/uni/src/bin/{bandtheta,c104theta,densetheta}.rs`, `scratch/a19/short/robust.rs`; recorded in I31, I34, C120 (E46 is committed for the {1..N} roots only).
   - C110's profile and high part: `scratch/a19/uni/src/bin/{col1,band10}.rs`, `scratch/a19/cap/cap1.rs`, `scratch/a19/{rb1,c18,c18cls,gfp}.rs`; recorded in C110.
   - Smaller checks, recorded where named: `uni/src/bin/{mono,thermo,rows,depth,tied5,lowab,lowj,tiedloss}.rs` (C109, I32, I30, I33, I20, C104, C99, C106), `scratch/a19/mirror/mirror.rs` (I29), `scratch/a19/ctl/ctl.rs` (I25, C112), `scratch/ideator/2026-11-05-*.md` (fresh05–08, recorded as I25–I28, I33, C111–C113, C115, C117–C119).
3. Research, light runs only: C110's band at linear height for the remaining holes needs a class for AM+T (the greatest closed class inside C18's condition is irregular; hole o = 1 needs its own answer rule, C110 Proof); C119's play enters C104's low blocks after the attacker drains the change (I33).
4. When agents are allowed again: a refuter on `ShortTurns`/`Threshold` (one implementation each) and on C114/C116, I31's data; an ideator round.

**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds to a few minutes, under 1 GB) are fine. Lean: one module per `lake build` (memory: a parallel build beside an experiment froze the PC).
**Agents paused (user, 2026-11-05 20:55).** No ideator, refuter or other agent until the user allows it again or a new session starts.
**Running.**
(none) — nothing running or suspended at the 2026-11-06 migration pause; no agent active.

## Optional long runs
- Queued for the overnight session (user, 2026-11-05 21:20: "not yet, later in the overnight session"); start when the user says it has begun, one at a time, each stated as an experiment first:
  - C116 at the C1 roots N = 23, 24 and C92's families: `target/release/e42_largest_change.exe 3 3 24` (about 5 GB at N = 24, 1 thread).
  - C120, θ = 6..10 at N = 24 (about 1.3 GB each) and θ = 6, 7 at N = 27 (about 11 GB): `target/release/e46_threshold_variants.exe <θ> <θ> 24 24` (committed `Threshold` engine).
  - C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4).
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
- Start of the overnight session (the queue above) and when agents may run again.
