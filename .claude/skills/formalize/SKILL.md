---
name: formalize
description: Formalize the paper proof of a blueprint node in Lean, step by step (Tao's recipe) — skeleton with sorry first, then one line per informal line, then fill the gaps one at a time, and report every deviation from the paper proof. Requires the node's statement to be approved by the user. E.g. `/formalize catch-up <node>`.
---

# Formalize a node

Arguments: the problem folder and the blueprint node. Recipe and pitfalls: `principles/lean.md` `[CC]`.

**Preconditions**: the node is at `statement approved` and its paper proof (its section in `blueprint.md`) at `proof survived`; every node it depends on is formalized or explicitly left as a `sorry`-free hypothesis in its statement. Otherwise stop and say which is missing.

1. **Definitions and notation** the proof needs, nothing more; reuse Mathlib and existing lemmas in the library `[Ilin]`.
2. **Skeleton**: every intermediate lemma stated, every proof `sorry`. Do not prove anything yet. Build.
3. **One Lean step per informal step**, each justified by `sorry`, keeping the Lean aligned with its section in `blueprint.md`. Build.
4. **Fill the `sorry`s one at a time**, building after each. Extract any repeated sub-step as its own lemma. Watch the known blind spots: flipped equations, ℕ vs ℝ casts and subtraction, off-by-one starts `[o4]` `[ByHand]`.
5. **Hypotheses**: if a lemma needs a hypothesis the statement lacks, stop: the statement changes, so it goes back through `audit-statement`. Never weaken or edit an approved statement to make a proof go through.
6. **Deviations** `[NSLost]`: list every place the Lean proof differs from the paper proof (a step repaired, an argument replaced, an extra case), and correct its section in `blueprint.md` to match. A green build checks the Lean statement only, not the paper.
7. **Verify** against the trust rules: `lake build --wfail`, and `#print axioms` on the node's theorem. Then mark the node `formalized` in `blueprint.md`, log it, and put the deviations list under "Awaiting review" for the user to read.
