---
name: audit-statement
description: Prepare a Lean statement for the user's approval — write it, read it back in plain terms, unit-test it, check junk values and degenerate cases, check it implies known weaker results, and try to disprove it. Use for every new or changed theorem statement or definition, e.g. `/audit-statement catch-up <node>`. Never marks anything approved; only the user does.
---

# Audit a statement

Arguments: the problem folder and the blueprint node or statement. Principles: `principles/lean.md`. Most first-draft statements are wrong `[Buzzard]`; this step finds out how.

1. **Write it** in `lean/<Problem>/` next to the statement it serves, with its informal version as a doc comment. Reuse Mathlib definitions; any new definition is flagged and audited the same way `[Buzzard]`. Never edit an approved statement; a change is a new statement.
2. **Read it back**: translate the Lean into plain words without looking at the informal version, then compare the two sentence by sentence. Every difference is a finding.
3. **Check the traps**: division, ℕ subtraction, casts, inverses, minimums or suprema that may not exist (junk values `[NSLost]`); empty, zero and degenerate cases; quantifier order and ∀ vs ∃; off-by-one in ranges; implicit assumptions (finiteness, nonemptiness, distinctness).
4. **Unit-test** in `lean/<Problem>/Tests/` (imported by the library root) `[Methods]` `[Riehl]`:
   - small instances that should hold, proved by `decide` or a short proof (trust rules apply);
   - drop each hypothesis in turn: a known counterexample should then satisfy the weakened statement's negation;
   - the statement should imply the known weaker results and special cases;
   - for definitions: standard examples satisfy them, and a basic expected property follows.
5. **Try to disprove it**: compute small cases with the solver, and run the `refuter` agent in `statement` mode with the Lean, the informal version and the findings so far.
6. **Report**: `lake build --wfail` must pass (tests included). Add to "Awaiting review" in `state.md`: the Lean statement, its plain reading, the trap checklist with results, the tests, the refuter's verdict, and the question "Does this say what we mean?". The blueprint node moves to `statement approved` only after the user says yes.
