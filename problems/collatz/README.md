# Collatz

Idea log, failures included. Nothing here is trusted until it's proven in `lean/`.

**Status: shelved**, very unlikely to fall.

## Definitions

- Collatz map: even n ↦ n/2, odd n ↦ 3n+1. Conjecture: every n ≥ 1 reaches 1.
- Shortcut map T: even n ↦ n/2, odd n ↦ (3n+1)/2. Since 3n+1 is even for odd n, T merges the halving that always follows.

## Sanity tests any proof must pass

1. **It must not also "prove" 5n+1.** One odd step plus one even step multiplies n by about 3/2 · 1/2 = 3/4 < 1 for 3n+1, but by 5/2 · 1/2 = 5/4 > 1 for 5n+1. 5n+1 has other cycles (13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13), so an argument that also works for 5n+1 is wrong.
2. **It must use that integers have finitely many 1 bits.** In the 2-adic numbers, −1 = …111 (binary) is a fixed point of T: (3·(−1)+1)/2 = −1. −1 matches the residue 2^k − 1 for every k, so arguments that only look at low bits or residues fail.
3. **It must use something specific to 3 and 2.** Conway showed that generalized Collatz maps are undecidable.

## Climb lemma

If n = 2^a·m − 1 with m odd, T makes exactly a odd steps in a row, reaching 3^a·m − 1. One step: T(2^a·m − 1) = 3·2^(a−1)·m − 1.
Consequence: descent certificates need unbounded look-ahead, and the limit of these climbs is the 2-adic −1.

## Attack: ranking function via LP

Search with an LP for a ranking function f(n) = log2(n) + a correction from the low-bit structure (e.g. the length of the trailing-ones run) that strictly decreases along T.
If it fails, classify the solver's counterexamples: genuine integers vs 2-adic fakes with infinitely many 1 bits.
Prior work: Yolcu, Aaronson & Heule 2021 (SAT / rewriting termination; it worked for weaker variants).
Expected failure point: telling integers apart from 2-adic fakes.

## Log

- 2026-10-22: project set up; nothing tried yet.
