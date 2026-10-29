---
name: audit
description: Prepares a claim's Lean statement for the user's approval: writes it, reads it back in plain terms, checks the traps, unit-tests it and tries to disprove it. Use for the goal, and for a claim before it is shared outside the repo. Never marks anything approved; only the user does.
---

# Audit a claim's Lean statement

Most first-draft statements are wrong; this finds out how.

1. Write it where it belongs (the goal: `lean/<Problem>/Statement.lean`),
   its plain version as a doc comment marked pending approval. Reuse Mathlib
   definitions; a new definition is audited the same way.
2. Read it back: put the Lean into plain words without looking at the
   plain version, then compare sentence by sentence.
3. Check the traps: junk values (division, ℕ subtraction, casts, minimums
   that may not exist), empty and degenerate cases, quantifier order,
   off-by-one ranges, hidden assumptions.
4. Unit-test in `lean/<Problem>/Tests/`: small instances that should hold;
   each hypothesis dropped in turn fails on a known counterexample; it
   implies the known weaker results.
5. Try to disprove it: small cases with the solver, and the `refuter` on
   the statement.
6. Report under "Needs the user" in `state.md`: the Lean, its plain reading,
   the traps checked, the tests, the refuter's verdict, and "Does this say
   what we mean?". Only after the user's yes: drop the pending mark and
   record the date as the claim's approval.
