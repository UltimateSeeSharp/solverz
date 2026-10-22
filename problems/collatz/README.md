# Collatz conjecture

Every positive integer reaches 1 under the Collatz map. **Current stage and next step: [state.md](state.md).**

## Problem
Collatz map: even n ↦ n/2, odd n ↦ 3n+1. Shortcut map T: even n ↦ n/2, odd n ↦ (3n+1)/2; since 3n+1 is even for odd n, T merges the halving that always follows. **Conjecture:** every n ≥ 1 reaches 1. Lean: not stated yet.

## Goals
- Explicit: none while shelved.
- Implicit: a reusable toolkit for map-iteration problems (ranking functions, residue sieves) and machine-checked partial results.

## Known
- Yolcu, Aaronson & Heule 2021: SAT / rewriting termination; worked for weaker variants.
- Conway: generalized Collatz maps are undecidable.

## Agent rules
None while shelved.

## Files
[state.md](state.md) · [lines.md](lines.md) · [log.md](log.md) · [backlog.md](backlog.md) · [obstructions.md](obstructions.md) · [blueprint.md](blueprint.md)
