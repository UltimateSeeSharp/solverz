# Proof-hunt agent prompt

For a looping Claude Code session in this repo (e.g. `/loop` with this prompt). One iteration per firing.

```text
You are hunting for a proof (or disproof) of the Catch-Up conjecture in this repo.
Target: `CatchUp.Conjecture` in problems/catch-up/lean/CatchUp/Statement.lean: on {1..N}, if 1+…+N is
even, optimal play is a draw. Verified by computer up to N = 26 here (28 per an unpublished talk);
no proof is known. Read problems/catch-up/README.md first: rules, known data, and the idea log.

EACH ITERATION: work on exactly ONE idea, then stop.
1. Diverge before choosing. Read "## Log" and "## Backlog" in problems/catch-up/README.md, then
   write down 3 candidate ideas: the best open backlog item, a variation of the best result so far,
   and one wild idea unlike anything logged (different angle: a strategy, an invariant, a stronger
   general statement, a known result from another game). Never repeat a logged attempt. If the last
   3 log entries share one approach and all failed, don't pick that approach. Pick one; add the
   other two to the backlog. Stuck? Try anything, even a naive idea: how it fails is a clue.
   Or cheat strategically: switch off all difficulties but one (a simpler variant of the game,
   one player fixed to a rule, few numbers left), solve that, then add difficulties back.
2. Turn it into a precise, falsifiable claim and try to KILL it before believing it:
   - Look for the smallest counterexample first (small N, small subsets, extreme positions).
   - Fit on small N, test on the rest: a pattern found on N ≤ 16 must also hold for 17..max with no
     changes. A rule with nearly as many special cases as data points is overfitting, not a pattern.
   - Write experiments as new files solver/src/bin/<short_name>.rs using the `catch_up` library
     (`Solver`, `layered::Layered`, `interval`, `Outcome`). For constrained play (one side follows a
     fixed rule), write your own memoized search in the bin file and first check that it reproduces
     the library's values for unconstrained play.
   - Prefer reusable evaluators over one-off checks: e.g. `strategy_eval.rs` takes a rule and reports
     the first N (and position) where it fails against a perfect opponent. A scored evaluator lets
     later iterations mutate the best rule instead of starting over; keep a leaderboard of rules and
     their scores in the README.
   - Run with `cargo run --release -p catch-up --bin <short_name>`. Keep runs under ~10 minutes.
   - Scratch output goes to problems/catch-up/scratch/ (git-ignored).
3. Mine data, not just verdicts. When a claim fails, record WHY (the counterexample position and
   what is special about it) and how the claim could be weakened to survive; when it holds, record
   the structure it revealed. Dump tables to scratch/ and look for patterns before guessing again.
   A counterexample to a generalization is an OBSTRUCTION: it shows any proof must use some
   property the counterexample lacks. Keep these in the README under "## Obstructions" (what
   fails, so which proof methods are dead).
4. Self-review before logging. Re-read your claim and experiment as a skeptical referee: does the
   code test what the claim says? Off-by-one in N, gap or who moves? Did it reproduce known values?
   In a proof sketch, list every case and check each one; a missed case is the usual failure.
   If a step splits the problem, check each piece is really easier than the whole. If a proof
   looks too easy, assume it's wrong until you find the error or the reason it isn't one.
   If you can spawn a subagent, have a fresh one try to break the claim or find it in the literature.
5. Log the result in the README under "## Log": date, claim, experiment (file + command), outcome
   (holds up to N = …, or the first counterexample), and what it means. Failures are valuable: say
   why it failed. Update the backlog: remove the item, add follow-ups.
6. If a claim holds for every computable case:
   - Search for it (OEIS, arXiv, Google Scholar: "Catch-Up" game, Isaksen, Brams, von Stengel). Log
     whether it is already known.
   - Write it as a lemma with a paper proof sketch in the log.
   - Small, self-contained lemmas (endgames, the parity law) may go to Lean right away: iterate
     against the compiler. Big steps only once the paper proof is complete. Lean files go in
     problems/catch-up/lean/CatchUp/, imported from CatchUp.lean, and must build with
     `lake build --wfail` (no sorry, no axioms, no native_decide). State each new Lean statement in
     plain words in the log so the user can check it says the right thing.
7. End with a 3-line summary: idea, result, next.

Seed backlog (if the README has none yet):
- Induction by four: is value({1..N+4}) = value({1..N})? More generally, does adding a "balanced
  quadruple" a < b < c < d above max(S) with a + d = b + c preserve a draw? If yes for all small S,
  that is the induction step from the base cases N = 3, 4.
- Generalize: for every set S ⊆ {1..m} (m ≤ 16) with even sum, which are draws? Find a clean
  characterization; a stronger general statement is often easier to prove by induction.
- Drawing strategies: test simple rules for player 2 and for player 1 against a perfect opponent
  (largest number that catches up; smallest; minimal overshoot; mirror x ↦ N+1−x). Report the first
  N where each fails. Then evolve: combine and patch the best rules at their failure positions.
- Position structure: from the layered tables (N ≤ 20), is the value monotone in the gap? Does it
  depend only on a few features (sum, count, gap, parity)? Look for a compact "draw region".
- Parity rule: when do rows follow "win where a draw is impossible, draw where possible" exactly?
  (see README Observations; `solver/src/bin/row_stats.rs`).
- Endgames: exact value formulas for positions with ≤ 3 numbers left (future Lean lemmas).
- Invariant hunt: is there a simple quantity of a position (gap, sum left, count, largest number…)
  that decides its value, or that a drawing player can keep within bounds? A proof usually runs
  on such a quantity.
- Robustness: which even-sum sets are NOT draws? Remove, add or swap one number in {1..N}: does
  the draw survive? Fragile means the proof must use a precise property of {1..N} (an
  obstruction); robust means a general statement for many sets may be true and easier to prove.

RULES
- Never edit lean/CatchUp/Statement.lean, solver/src/lib.rs, solver/src/layered.rs or
  solver/src/main.rs (another session is changing the solver); only add new files.
- Computer evidence is not a proof. Never call something proven unless Lean checked it.
- Never call something new unless step 6's search found nothing; say what you searched.
- Cite only sources you opened in this session; AI-recalled references are often invented.
- Don't install anything, don't bump toolchains, don't commit or push: the user reviews and commits.
- Explain findings in plain terms; the user is a developer, not a mathematician.
```
