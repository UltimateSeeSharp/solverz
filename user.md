# User

The user's open items and to-dos. Maintained by the user only: agents read it, never edit it.

## Now
- signed-difference-sets: the side agent checks the new structure and records last night's work on main; then `/solve signed-difference-sets`.
- catch-up: run the build after the BoCowgill move and the Goal rename (f5e4e7d, not yet built): one module per `lake build`, in import order, under the RAM watchdog. Start the catch-up researcher only after it passes.

## Publication
- signed-difference-sets: publish with Daniel M. Gordon (maintainer of the SDS database) as co-author.
  - First email: a two-sentence intro, the database corrections (each re-checked first) and the Lean-checked rows; no unverified claims.
  - Second email, once the Lean proofs are done: ask to co-author (me: computation, Lean, data, first draft; him: the maths write-up and literature). Not "mentor, proofread it".
  - No answer: follow up once after 2–3 weeks, then He or Wu; else results into his table with credit, or a solo arXiv note.
  - Paper mock-up: https://claude.ai/artifact/Tm4C7CST98Bb5ApnrHVoEC
- ORCID: done; add name variants ("David R. Schneider", "David Raphael Schneider") and link it to arXiv.
- Google Scholar: after the first arXiv preprint; confirm updates by email, since "David P Schneider" (a climate scientist, 117 articles) gets confused with me.

## Repo
- choose: copy `template/` plus each module's `template/`; kinds from `problems.md`; the setup of `solve` and of each module (`setup.md`); the README's Modules line; the worktree creation command (missing everywhere).
- Stop hook in `solve`'s frontmatter (`decision: block`; check the field names first).
- `solve`, Pick: aim at what blocks.
- Toolbox: new entries for explicit strategy, characterization, phase split, strategy transfer, turn restriction, one-start reduction, one-point extension, exhaustive backtracking.
- Toolbox sweep (techniques by tag, minus those used, with first moves): a repeatable step, or by hand?
- Roles: the ideator's duration, once `xhigh` is measured.
- A home for `lean-build.ps1` (the RAM watchdog; now only in the sds worktree's scratch).
- CLAUDE.md, ideas row: "— and a name" without backticks (researchers copy them).

## Migration
- Technique IDs for the "—" ideas once the toolbox has their entries (catch-up I3, I4, I8, I13, I19, I22, I27, I33; ramsey I3; sds I1).
- Memory: check every entry against the new model ("Agents write incrementally" is half built into the agents; "Worktrees are the researcher's only" still says `attack/`).
- catch-up state.md: "Merge solve/catch-up into main" is already done (06b295a).

## Not yet reviewed
audit, choose, maintain (with this session's lessons), the problem lists, toolbox and principles.md, the public README, memory.
