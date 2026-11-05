---
name: prove
description: Domain model and attack loop for a `prove` problem: ideas, claims, experiments. Run by "attack <problem>" when the problem's kind is prove.
---

# Prove

## Domain model

| File | What it holds, how it is used |
|---|---|
| `ideas/` | Idea: a way to attack the problem. Technique (its toolbox entry and name, e.g. `T301` generalize; `—` and a name when the toolbox has none), source (ideator, literature, us), the claims it needs, including the claim that those claims imply the goal. Status: `new` → `alive` (survived its kill test) \| `dead` (which claim failed) \| `solved`. |
| `claims/` | Claim: one precise statement. The claims it uses; evidence; what was tried and failed. Status: `open` → `refuted` (counterexample) \| `proved` → `verified` (Lean). `approved` when the user confirmed its Lean statement says what we mean. |
| `experiments/` | Experiment (CLAUDE.md, Files): here it tests one claim. |

Relations: an idea needs claims, a claim uses claims (both many to many).
A refuted claim kills every idea that needs it and reopens every proved
claim whose proof uses it; an idea whose claims are all verified solves the
problem.

## Files
`templates/prove/` adds to `problems/<name>/`:
```
ideas/        _ideas.md (index), I1.md, I2.md, …
claims/       _claims.md (index), C1.md, C2.md, …
```

## Start
The goal is claim C1. The researcher builds the base itself: the
problem's small cases computed by an engine checked against published
values; the first ideas, standard techniques first, each with its claims
and kill test, in `ideas/` and `claims/`. The `ideator` comes in when the
researcher has no next idea of its own; nothing waits on it.

## Loop
1. Pick the most promising idea now, in light of `understanding.md`: new
   ideas get their cheapest kill test first, alive ones go deeper.
2. Work on one claim it needs: test it, prove it, find it in the
   literature, or verify it in Lean: while it is open, when Lean settles it
   faster than paper; otherwise once every claim of the idea is proved on
   paper (the goal goes through `audit` first).
3. Before a claim becomes `proved` or `refuted`, the `refuter` attacks the
   result (CLAUDE.md, Roles); a flaw goes under Tried. A counterexample
   counts once rechecked with committed code (in Lean if the claim is
   stated there and the check is quick).
4. Record changed statuses with a journal line, and `state.md`.
5. The goal claim verified: it goes under "Needs the user" as a proposed
   Solution (CLAUDE.md, Files); stop and tell the user. Otherwise never stop
   (CLAUDE.md, Attack).
