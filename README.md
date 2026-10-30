# solverz

AI-assisted attacks on open math problems; every result is machine-checked
in Lean 4. How it works: [CLAUDE.md](CLAUDE.md). How we think:
[principles.md](principles.md). All problems: [problems.md](problems.md);
being attacked: [problems/active-problems.md](problems/active-problems.md).

## Use
- "choose a problem": picks from problems.md and sets the problem up.
- "attack <problem>": runs the attack loop until the goal is verified or you
  stop it. What needs you is listed in the problem's `state.md`.

## Setup
1. Install [elan](https://github.com/leanprover/elan), the VS Code "Lean 4"
   extension and [Rust](https://rustup.rs).
2. `lake exe cache get` (prebuilt Mathlib instead of hours of compiling).
3. `lake build` and `cargo build --release`.

## Verify
`lake build --wfail` and `#print axioms` (trust rules in CLAUDE.md);
`cargo test --release`.
