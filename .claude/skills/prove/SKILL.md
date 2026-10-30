---
name: prove
description: Domain model and attack loop for a `prove` problem: ideas, claims, experiments. Run by "attack <problem>" when the problem's kind is prove.
---

# Prove

## Domain model
- **Idea**: a way to attack the problem. Kind (induction, invariant, finite
  reduction, …), source (ideator, literature, us), the claims it needs,
  including the claim that those claims imply the goal.
  Status: `new` → `alive` (survived its kill test) | `dead` (which claim
  failed) | `solved`.
- **Claim**: one precise statement. The claims it uses; evidence; what was
  tried and failed.
  Status: `open` → `refuted` (counterexample) | `proved` → `verified` (Lean).
  `approved` when the user confirmed its Lean statement says what we mean.
- **Experiment**: a computation that tests one claim. States beforehand which
  result changes the claim's status; its code is first checked against known
  values or an independent computation.

Relations: an idea needs claims, a claim uses claims (both many to many).
A refuted claim kills every idea that needs it and reopens every proved
claim whose proof uses it; an idea whose claims are all verified solves the
problem.

## Files
`templates/prove/` adds to `problems/<name>/`:
```
ideas/        _ideas.md (index), I1.md, I2.md, …
claims/       _claims.md (index), C1.md, C2.md, …
experiments/  _experiments.md (index), E1.md, E2.md, …
```

## Loop
1. Pick the most promising idea now, in light of `understanding.md`: new
   ideas get their cheapest kill test first, alive ones go deeper.
2. Work on one claim it needs: test it, prove it, find it in the
   literature, or verify it in Lean: while it is open, when Lean settles it
   faster than paper; otherwise once every claim of the idea is proved on
   paper (the goal goes through `audit` first).
3. Before a claim becomes `proved` or `refuted`, the `refuter` attacks the
   result. SURVIVES: the change goes through. REFUTED: the claim is
   `refuted`. FLAWED: it stays `open`, the flaw under Tried. UNCLEAR:
   settling it is the next step. A counterexample counts once rechecked
   with committed code (in Lean if the claim is stated there and the check
   is quick).
4. Record changed statuses with a journal line, and `state.md`.
5. The goal claim verified: stop and tell the user. Otherwise **NEVER STOP**:
   not to wait for anything under Running, not for context (compaction is
   automatic; `state.md` carries the loop), and after answering the user,
   go on with the loop. The user stops the loop.
