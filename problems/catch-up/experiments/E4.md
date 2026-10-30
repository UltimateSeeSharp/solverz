# Entry into a provable high-phase class, N ≤ 24

A8's question in formal terms: from L31's starts ({2..N} and {3..N} at deficit 1) and from {1..N} at gap 0, in both roles, can a defender D, playing freely against a perfect opponent, force the first high round start (|R| even, min R ≥ span R, mover's debt ≤ min R) into a class C where the high phase is covered by provable pieces? With a = min R and offsets T = R − a, C is the debt part W ≤ a with the mover's debt ≤ a (L25: Hyb2T's potential never rises, so every later debt fits L22's transfer) and an outcome part:

- `o`: L23's depth classes (D to move: KZc(T, d); the opponent to move: KYc(T, e)) or the opponent to move with e ≥ c(T) (after Hyb2T's switch, L20).
- `s<k>`: `o`, or Hyb2T's exact rounds-game guarantee (≥ draw) on sets of at most k offsets.
- `h`: Hyb2T's exact rounds-game guarantee, the largest outcome class any proof of a Hyb2T high phase can use.

Hyb2T: as mover the largest; as answerer the smallest j with e + j − i ≥ c of what is left, else AM+T's answer.

- Date: 2026-10-26
- Command: `formal_entry <lo> <n_max> <deficit> <parts>` (`./target/release/formal_entry`) with (lo, deficit) ∈ {(2, 1), (3, 1), (1, 0)}: parts `wo` to 22, `w` and `o` alone to 20, `wh` to 22 and 24, `wos2`, `wos4`, `wos6` to 20, `wos4` and `wos6` to 24, `wos4b4` to 16, `c` to 20.
- Commit: 86fda13 (runs before it used the same code without the later options)
- Machine: AMD Ryzen 7 3700X, 32 GB RAM; rustc 1.99.1 (MSVC)
- Runtime: `wos4` to 24: 3 min 49 s; `wh` and `wos6` to 24: 113 min together
- Checked: mode `c` asserts at every scored position reached to N = 20 (all three starts) that L23's class and e ≥ c lie inside Hyb2T's exact guarantee: no violation, so the class code and the rounds-game engine agree. The real-game engine is not independently checked here; with no class restriction it reproduces draws everywhere (a scored position counts as a draw).
- Data: `scratch/a8/formal_entry-22.txt` (SHA-256 `8d33e57a7efedd4dfd682440e19347ca76781e4ec1a53630e44988bc273f238c`), `formal_entry-22-wh.txt` (`bf2806664c91068789ec76d3cdae1b4f3f2bc71c0f19b21e5a1c2ba9c4d9677f`), `formal_entry-24-wos4.txt` (`63224622354ca25b3c73f15c63e289e91b6a5a5d46774e45118b5b9ac3261d65`), `formal_entry-24-wh-wos6.txt` (`a09e08c3e1ca751656b0a9f29cd380be7fc1f2b41d068b074996c96762795417`)

## Outcome

Scope: every even-total N ≤ 24 (lo = 1, 2) and every N ≤ 24 with 3 + … + N + 1 even (lo = 3). The three starts give the same answer in both roles at every N.

| Outcome part | D forces entry for N ≤ | First failure |
|---|---|---|
| `o` (L23 or e ≥ c) | 16 | 19 |
| `w` alone (debt part, any outcome) | 20 (scope) | none |
| `s2` | 16 | 19 |
| `s4` | 20 | 23 |
| `s6` | 24 (scope) | none to 24 |
| `h` (Hyb2T exact) | 24 (scope) | none to 24 |
| `s4` with D on its 4 smallest numbers while low | 12 | 16 |

The debt part is never the obstacle. Hyb2T's exact guarantee suffices to N = 24, but every describable subclass tried breaks a few steps later: the exact table needed grows with N (4 offsets to 20, 6 to at least 24).
