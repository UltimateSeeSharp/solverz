# Catch-Up solver

Exact game values, untrusted (a result counts only once Lean checks it). Library crate `catch_up`, CLI `catch-up`, experiments in `src/bin/`.

## Engines

`cargo run --release -p catch-up -- --engine <engine> [--top H] [--from N] <to>` prints, per N, the value of {1..N} and player 1's outcome after each opening.

| Engine | Library | What | Limits |
|---|---|---|---|
| `dfs` | `Solver` | Memoized search mirroring Lean `valueAux`; any set, multisets too; `position(mask, gap)` | N ≈ 24 (25 s) |
| `layered` | `layered::Layered` | Every position, one layer of equal size at a time, all CPU threads | N = 32 in 6 min, 14 GB |
| `tiled` | `tiled::Tiled` | Layers split by which top numbers remain; basis for GPU and out-of-core | as layered |
| `gpu` | `gpu::Gpu` (`--features gpu`) | Tiled, each tile a wgpu compute shader | correct but slow; CUDA port pending |

Verification chain (`cargo test --release`, GPU tests with `--features gpu`): independent turn-by-turn `reference_value` = `dfs` on all subsets of {1..8}; `dfs` = OEIS A278587; `layered` = `dfs` on every position for N ≤ 10; `tiled` = `layered` on every position for N ≤ 10 and every tiling; `gpu` = `tiled` on every layer for N ≤ 10.

## Experiments

| Binary | Question | Run |
|---|---|---|
| `row_stats` | How are a position's values arranged by gap (parity pattern, distinct rows)? | `cargo run --release -p catch-up --bin row_stats -- 22` |
| `quad_step` | Does adding a balanced quadruple keep a drawn set drawn? Also: values of complete sets | `cargo run --release -p catch-up --bin quad_step -- 30` |

## Recipes

- **value(S) for every S ⊆ {1..U} at once:** one `Layered` run on {1..U}; the row of S at gap 0 is value(S), because a gap-0 turn is a single pick like the opening (`quad_step::all_values`).
- **One position:** `Solver::position(mask, gap)` = mover's value with `mask` left, trailing by `gap`.
- **Before trusting a new experiment:** reproduce known values with it first (A278587, or `Solver` on small sets).
