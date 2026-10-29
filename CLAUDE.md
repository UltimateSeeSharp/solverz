# solverz

AI-assisted attacks on open math problems; every result is checked in Lean 4.

## Domain model
- **Problem**: what we want to solve. Statement (as a Lean claim), kind,
  core difficulty (what any solution must get past), literature. Kinds:
  - `prove`: a statement holds in all cases; a Lean proof.
  - `find`: an object with a property exists; Lean checks the object.
  - `bound`: improve a best-known value; an object from below, a proof
    from above.
  - `compute`: an exact value or complete list; Lean checks a certificate.
  A problem that fits no kind, or has no finite check, is not taken on;
  the user decides.
- **Idea**: a way to attack the problem. Kind (induction, invariant, finite
  reduction, …), source (ideator, literature, us), the claims it needs,
  including the claim that those claims imply the goal.
  Status: `new` → `alive` | `dead` (which claim failed) | `solved`.
- **Claim**: one precise statement. The claims it uses; evidence.
  Status: `open` → `refuted` (counterexample) | `proved` → `verified` (Lean).
  `approved` when the user confirmed its Lean statement says what we mean.
- **Experiment**: a computation that tests one claim. States beforehand which
  result changes the claim's status; its code first reproduces known values.
- **Session**: one work period: what changed.

Relations: an idea needs claims, a claim uses claims (both many to many).
A refuted claim kills every idea that needs it; an idea whose claims are
all verified solves the problem.

## Where things live
```
problems/<name>/
  README.md     the problem
  ideas/        ideas.md (index), I1.md, I2.md, …
  claims/       claims.md (index), C1.md, C2.md, …
  experiments/  experiments.md (index), E1.md, E2.md, …
  sessions.md   sessions, newest last
  state.md      now: focus, next step, what needs the user
  lean/ solver/ scratch/
```

## Workflows

### Choose: a new problem (`choose` skill)
1. Check it isn't already solved: literature, recent arXiv, open problem lists.
2. Write the problem: kind, core difficulty, literature.
3. State the goal as a claim in Lean; `audit`, then the user approves it.
4. Draw the first ideas: standard techniques first, then anything else
   that could apply, each with the claims it needs.

### Attack: the loop (`prove`)
Workflows for `find`, `bound` and `compute` are not written yet; problems of
those kinds wait until they are.

1. Pick the most promising idea now: new ideas get their cheapest kill test
   first, alive ones go deeper. Work only on claims a live idea needs.
2. Work on one claim: test it, prove it, find it in the literature, or
   verify it in Lean (once every claim of its idea is proved on paper;
   reported claims go through `audit` first).
3. The `refuter` attacks the result before any status changes.
4. Record statuses, a session line and `state.md`.
5. An idea solved, out of ideas after the `ideator` drew more, or a decision
   needed: stop and tell the user. Overnight lists it and keeps going.

## Helpers
- `ideator` (agent): draws ideas with the claims they need.
- `refuter` (agent): attacks claims: counterexamples, proof checks.
- `choose` (skill): finds a problem and sets it up.
- `audit` (skill): prepares a claim's Lean statement for the user's approval.

## Trust
- A result counts only once Lean checks it: `lake build --wfail`, no `sorry`,
  no custom `axiom`, no `native_decide`; `#print axioms` shows only
  `propext`, `Classical.choice`, `Quot.sound`.
- Solvers and agents are untrusted; their output counts once Lean checks it.
- Read any downloaded Lean file before compiling it.

## The user decides
Approving statements, calling anything a solution, sharing outside the repo,
commits, pushes, installs and downloads.
