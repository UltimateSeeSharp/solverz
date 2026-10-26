# Catch-Up solver

Exact Catch-Up game values. Library crate `catch_up`, CLI `catch-up`, experiments in `src/bin/`.

## Engines

`cargo run --release -p catch-up -- --engine <engine> [--top H] [--ram GB] [--from N] <to>` prints, per N, the value of {1..N} and player 1's outcome after each opening. The CUDA engines need the CUDA `bin\x64` folder (NVRTC) on `PATH`.

| Engine | Library | What | Limits |
|---|---|---|---|
| `dfs` | `Solver` | Memoized search mirroring Lean `valueAux`; any set, multisets too; `position(mask, gap)` | N ≈ 24 (25 s) |
| `layered` | `layered::Layered` | Every position, one layer of equal size at a time, all CPU threads | N = 32 in 6 min, 14 GB |
| `tiled` | `tiled::Tiled` | Layers split by which top numbers remain; basis for streaming beyond memory | as layered |
| `cuda` | `cuda::Cuda` (`--features cuda`) | Layered, each layer one CUDA kernel launch (`layered.cu`), layers resident on the GPU | N ≤ 31 (two layers must fit in 8 GB); N = 31 in 41 s. Run it alone: next to a large CPU run, memory contention stalled N = 31 for over 9 minutes |
| `tiled-cuda` | `tiled_cuda::TiledCuda` (`--features cuda`) | Tiled, with compact rows: only the gaps a game can reach (gap ≡ amount taken, mod 2), packed in base 3, 4 bytes per row up to N = 39. One CUDA launch per tile (`tiled.cu`, all cells of a row at once on bit planes); layers stored tile by tile, zstd-compressed (lossless, checksummed; ~20% of raw at N = 34), in RAM up to `--ram` (default 16 GB), the rest in files under `scratch/tiled-cuda/`; input tiles cached in VRAM (6 GB) | N ≤ 39 at 4 bytes per row (N = 40 doubles it); stores only the reachable half of the positions. Before compression (50e494a): N = 31 in 6 s, 33 in 25 s, 34 in 1–2 min, 35 in 14 min, bound by disk writes (F: sustains ~100 MB/s). Compressed: N = 31 in 18 s (small tiles keep few threads busy); N = 34–35 stay in RAM, not yet timed on an idle machine. Use `--top 10` from N = 34; run it alone |

Verification chain (`cargo test --release`, CUDA tests with `--features cuda`): independent turn-by-turn `reference_value` = `dfs` on all subsets of {1..8}; `dfs` = OEIS A278587; `layered` = `dfs` on every position for N ≤ 10; `tiled` = `layered` on every position for N ≤ 10 and every tiling; `cuda` = `layered` word for word on every layer for N ≤ 12, and on all openings for N ≤ 20 and all subsets of {1..8}; `tiled-cuda` = `tiled` on every reachable position of every layer for N ≤ 12 and tilings 0, 1, N/2, N (layers in RAM, in files with the smallest possible VRAM cache, and split between the two), with unreachable gaps reported absent, and = `layered` on all openings for N ≤ 20 and all subsets of {1..8}.

## Experiments

| Binary | Question | Run |
|---|---|---|
| `row_stats` | How are a position's values arranged by gap (parity pattern, distinct rows)? | `cargo run --release -p catch-up --bin row_stats -- 22` |
| `quad_step` | Does adding a balanced quadruple keep a drawn set drawn? Also: values of complete sets | `cargo run --release -p catch-up --bin quad_step -- 30` |
| `pair_step` | Do top twins {x, x} cancel? Does a top pair {x, x+1} act on V(R, ·) by a local rule in g? | `cargo run --release -p catch-up --bin pair_step -- 22` |
| `strategy_eval` | Which fixed pick rules hold a draw against a perfect opponent? Reusable evaluator: a rule is a function (numbers left, gap) → pick | `cargo run --release -p catch-up --bin strategy_eval -- 20` |
| `interval_rows` | Where do interval rows V({1..m}, g), all gaps, break the parity rule? Census over all R ⊆ {1..U} by completeness and holes; near-intervals at gap 0 | `cargo run --release -p catch-up --bin interval_rows -- 22` (1 GB) |
| `near_intervals` | Are {1..m} ∖ H, \|H\| ≤ 6, draws (gap 0, and moderate gaps)? | `cargo run --release -p catch-up --bin near_intervals -- 30` (64 s, ~3 GB) |
| `hole_game` | With both players restricted to drawing picks, how few holes (four measures, incl. broken adjacent pairs) can a defender keep at its turn starts? `line <measure> <1\|2> <h>` prints an optimal line | `cargo run --release -p catch-up --bin hole_game -- 24` (4 min, ~7 GB) |
| `partner_reply` | Is answering the attacker's last pick with its adjacent partner a drawing reply? By broken pairs and game phase | `cargo run --release -p catch-up --bin partner_reply -- 24` (30 s, ~1 GB) |
| `partner_game` | When must a pairing defender refuse the partner? Explores every position reachable when D answers with the partner whenever it draws | `cargo run --release -p catch-up --bin partner_game -- 20` (36 s) |
| `pair_sets` | Do sets made of adjacent pairs draw at gap p mod 2 (and {1,2,3} ∪ pairs)? Also each pair set's first non-draw draw-parity gap | `cargo run --release -p catch-up --bin pair_sets -- 30` (71 s, ~3 GB) |
| `far_pairs` | Do far-apart pair sets have the exact row f_p (L9)? Which spacing hypotheses matter (p = 2–4, all sets)? `Solver` per set | `cargo run --release -p catch-up --bin far_pairs` (1 s) |
| `pair_moves` | Which first picks draw in a pair set at g0, by role (pair from below/above, half; 1, 2, 3 in T)? Also V(E, g0 + 2j) | `cargo run --release -p catch-up --bin pair_moves -- 28` (25 s) |
| `top_reserve` | Can the defender leave the top 2q numbers for last (A6, Γ_N)? `compare`: does barring the attacker too change values where the top block is intact (Lemma A)? Own full tables, one u64 row per set | `cargo run --release -p catch-up --bin top_reserve -- 23 28 0 1 2 3` (4 min, 4.3 GB at N = 28); `... -- compare 7 24 2` (6 s) |
| `block_rows` | Do even blocks {a..a+2p−1} draw at g0 (A7, TI)? Their rows against t_p, by height | `cargo run --release -p catch-up --bin block_rows -- 8 80` (5 s) |
| `low_change` | How large must k be for {1..k} ∪ C to draw, C a failing 5-pair core (B22)? | `cargo run --release -p catch-up --bin low_change -- 6 20 1` (40 s) |
| `rounds_game` | The rounds game (Catch-Up on high offsets, B20): rows of {0..2p−1} against t_p (T1), pair sets at debts 0, 1 (T2), and the tie law over every even O ⊆ {0..U−1} | `cargo run --release -p catch-up --bin rounds_game -- 24` (12 s, ~400 MB) |
| `max_strategy` | Do greedy strategies keep a draw in the rounds game? `max` = always take the largest (L15); `amx` = B25's exception; `amt` = never answer with an exact tie (B26). Least final margin by start (mover at debt 0, 1; non-mover leading by l) and p over pair sets, and on {0..2p−1} at every debt d ≤ p + 1 in both roles against t_p | `cargo run --release -p catch-up --bin max_strategy -- 22 8` (8 s); `... -- 24 12 amt` (1 min); `... -- 24 10 amx` (8 min) |
| `set_value` | Value of one set and player 1's outcome after each opening (`Solver`, and `reference_value` up to 10 numbers) | `cargo run --release -p catch-up --bin set_value -- 75 80 81 84 86 88 89 91` |
| `round_potential` | Is a round-by-round invariant for L15 (always-max) closed under play, over every state satisfying it? (No from p = 6.) | `cargo run --release -p catch-up --bin round_potential -- 8 18 120` (11 min) |

## Recipes

- **value(S) for every S ⊆ {1..U} at once:** one `Layered` run on {1..U}; the row of S at gap 0 is value(S), because a gap-0 turn is a single pick like the opening (`quad_step::all_values`). Not `tiled-cuda`: it stores gap 0 only for S whose complement sums to an even number.
- **One position:** `Solver::position(mask, gap)` = mover's value with `mask` left, trailing by `gap`. Only for gap ≤ the largest number: the memo has no check, and a larger gap reads another mask's slot.
- **Every gap up to sum(R):** `interval_rows`'s own table (stride sum + 1; 1 GB at U = 22).
