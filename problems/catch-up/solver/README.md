# Catch-Up solver

Exact Catch-Up game values. Library crate `catch_up`, CLI `catch-up`, experiments in `src/bin/`.

## Engines

`cargo run --release -p catch-up -- --engine <engine> [--top H] [--ram GB] [--from N] <to>` prints, per N, the value of {1..N} and player 1's outcome after each opening. The CUDA engines need the CUDA `bin\x64` folder (NVRTC) on `PATH`.

| Engine | Library | What | Limits |
|---|---|---|---|
| `dfs` | `Solver` | Memoized search mirroring Lean `valueAux`; any set, multisets too; `position(mask, gap)` | N ≈ 24 (25 s) |
| `margin` | `margin::Margin` | The margin game m(S, d) (C33) on the subsets of one number list, memo over (mask, deficit); used by E34–E36 next to `Solver` | about 24 numbers (2 bytes per (mask, deficit)) |
| `layered` | `layered::Layered` | Every position, one layer of equal size at a time, all CPU threads | N = 32 in 6 min, 14 GB |
| `tiled` | `tiled::Tiled` | Layers split by which top numbers remain; basis for streaming beyond memory | as layered |
| `cuda` | `cuda::Cuda` (`--features cuda`) | Layered, each layer one CUDA kernel launch (`layered.cu`), layers resident on the GPU | N ≤ 31 (two layers must fit in 8 GB); N = 31 in 41 s. Run it alone: next to a large CPU run, memory contention stalled N = 31 for over 9 minutes |
| `tiled-cuda` | `tiled_cuda::TiledCuda` (`--features cuda`) | Tiled, with compact rows: only the gaps a game can reach (gap ≡ amount taken, mod 2), packed in base 3, 4 bytes per row up to N = 39. One CUDA launch per tile (`tiled.cu`, all cells of a row at once on bit planes); layers stored tile by tile, zstd-compressed (lossless, checksummed; ~20% of raw at N = 34), in RAM up to `--ram` (default 16 GB), the rest in files under `scratch/tiled-cuda/`; input tiles cached in VRAM (6 GB) | N ≤ 39 at 4 bytes per row (N = 40 doubles it); stores only the reachable half of the positions. Before compression (50e494a): N = 31 in 6 s, 33 in 25 s, 34 in 1–2 min, 35 in 14 min, bound by disk writes (F: sustains ~100 MB/s). Compressed: N = 31 in 18 s (small tiles keep few threads busy); N = 34–35 stay in RAM, not yet timed on an idle machine. Use `--top 10` from N = 34; run it alone |

Verification chain (`cargo test --release`, CUDA tests with `--features cuda`): independent turn-by-turn `reference_value` = `dfs` on all subsets of {1..8}; `dfs` = OEIS A278587; `margin`'s sign = `dfs` on every subset of {1..9} at every gap ≤ 9; `layered` = `dfs` on every position for N ≤ 10; `tiled` = `layered` on every position for N ≤ 10 and every tiling; `cuda` = `layered` word for word on every layer for N ≤ 12, and on all openings for N ≤ 20 and all subsets of {1..8}; `tiled-cuda` = `tiled` on every reachable position of every layer for N ≤ 12 and tilings 0, 1, N/2, N (layers in RAM, in files with the smallest possible VRAM cache, and split between the two), with unreachable gaps reported absent, and = `layered` on all openings for N ≤ 20 and all subsets of {1..8}.

## Recipes

- **value(S) for every S ⊆ {1..U} at once:** one `Layered` run on {1..U}; the row of S at gap 0 is value(S), because a gap-0 turn is a single pick like the opening (`quad_step::all_values`). Not `tiled-cuda`: it stores gap 0 only for S whose complement sums to an even number.
- **One position's margin:** `set_margin <d> <numbers>` = m(S, d) of the margin game (C33), any multiset; checks its sign against `Solver`.
- **One position:** `Solver::position(mask, gap)` = mover's value with `mask` left, trailing by `gap`, any gap; gaps above the largest number are not memoized.
- **Every gap up to sum(R):** `interval_rows`'s own table (stride sum + 1; 1 GB at U = 22).
- **A value Lean proves:** `Position.eval ⟨R, d⟩` = V(R, d) (`Position.eval_eq_value`) and `evalInitial S` = value(S) (`eval_initial_eq_value`), in `lean/CatchUp/Executable.lean`; `example : Position.eval ⟨{2, 5, 7}, 3⟩ = .win := by decide +kernel`. About 10 s to load; {1..12} takes 66 s and each extra number doubles it.
