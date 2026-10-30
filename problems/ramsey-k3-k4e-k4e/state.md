# State

**Focus.** P3 (R4 running), then P4: local search on all 210 pairs.
**Next step.** A local-search engine for P4: simulated annealing on `violations` with incremental scoring, validated by reaching 0 at 20 points.
**Running.**
- refuter on R2 and R3 (started 2026-10-30 21:13; verdicts decide P2, P5 exhausted).
- R4 on the three 20-point families (started 2026-10-30 21:07; output in the session's task log, answers to `scratch/r4/`).

## Needs the user
- A SAT solver (Kissat) install, for P4 later; not needed for P1–P3.
