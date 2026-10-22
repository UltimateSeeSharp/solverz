# Lines of attack

Status: `main`, `active`, `shelved` (with reason), `dead` (killed by an obstruction).

## A1: Ranking function via LP (`shelved`)

- **Reduction.** If a function f(n) = log2(n) + (a correction from the low-bit structure, e.g. the length of the trailing-ones run) strictly decreases along T for every n > 1, every orbit reaches 1. Blueprint root: L1.
- **Metric.** Smallest n where the best LP candidate fails to decrease. Now: no candidate (2026-10-22).
- **Evidence.** None yet. Expected failure point: telling integers apart from 2-adic fakes (O2).
- **Spent / budget.** 0 / 0.
- **Kill criteria.** Every candidate's counterexamples include genuine integers, not only 2-adic fakes.
- **Next.** search: B1, if the problem is ever taken up.
