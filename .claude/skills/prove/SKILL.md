---
name: prove
description: Files and attack loop for a `prove` problem: ideas, claims, experiments. Run by "attack <problem>" when the problem's kind is prove.
---

# Prove

## Files

A `prove` problem adds these (`templates/prove/`) to the shared ones
(CLAUDE.md, Files).

| File | What it holds, how it is used |
|---|---|
| `ideas/` | Idea: a way to attack the problem. Technique (its toolbox entry and name, e.g. `T301` generalize; `—` and a name when the toolbox has none), source (ideator, literature, us), the claims it needs, including the claim that those claims imply the goal. Status: `new` → `alive` (survived its kill test) \| `dead` (which claim failed) \| `solved`. |
| `claims/` | Claim: one precise statement; C1 is the goal, its statement `<Problem>.Goal`. The claims it uses; evidence; what was tried and failed. Status: `open` → `refuted` (counterexample) \| `proved` → `verified` (Lean). `approved` when the user confirmed its Lean statement says what we mean. |
| `experiments/` | Experiment (CLAUDE.md, Files): here it tests one claim. |

### Relations

- An idea needs claims, a claim uses claims (both many to many).
- A refuted claim kills every idea that needs it and reopens every proved
  claim whose proof uses it.
- An experiment found wrong reopens every claim it refuted, and every idea
  those claims killed.
- An idea whose claims are all verified solves the problem.

## Loop

1. **Pick** the most promising idea now, in light of `understanding.md`:
   - new ideas get their cheapest kill test first;
   - alive ones go deeper;
   - with no next idea of its own, the researcher brings in the `ideator`;
     nothing waits on it.
2. **Work** on one claim it needs: test it, prove it, find it in the
   literature, or verify it in Lean.
   - Verify it in Lean while it is open, when Lean settles it faster than
     paper; otherwise once every claim of the idea is proved on paper.
3. **Check** before a claim becomes `proved` or `refuted`: the `refuter`
   attacks it (CLAUDE.md, Roles); a flaw goes under Tried.
   - A counterexample refutes a claim once it is an Experiment's outcome
     (CLAUDE.md, Files); in Lean if the claim is stated there and the check
     is quick.
4. **Record** changed statuses with a journal line, and `state.md`.
5. **Lean proves `<Problem>.Goal` or its negation:** that theorem goes under
   "Needs the user" as a proposed Solution (CLAUDE.md, Files); tell the user
   (CLAUDE.md, Attack).
