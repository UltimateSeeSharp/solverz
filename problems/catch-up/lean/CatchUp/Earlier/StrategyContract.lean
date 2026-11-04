/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/StrategyContract.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Reference

/-!
# Catch-Up exact-search and strategy-DAG contract

This research module specifies the data retained by the next exact Catch-Up solver. It intentionally
contains no claim that a certificate is valid and no parametric reduction theorem.

## Audit of the existing scripts

The existing memoized solver uses `(remainingMask, deficit)` as its cache key and stores the optimal
outcome and all optimal moves. That key is sufficient for a value measured from the current mover's
perspective, but a strategy for one fixed player must also record `toMove`. Moreover, storing only
optimal moves loses the non-optimal adversarial moves that a complete `CanAvoidLoss` strategy must
cover.

The contract below therefore requires an exact solved graph to retain every legal move. A derived
one-sided strategy stores one selected move at the strategy owner's nodes and every legal move at
the opponent's nodes. Lists, rather than hash maps, are used in exported data so that a future
independent checker need not trust the solver's cache representation.

The intended invariants are deliberately documented rather than encoded as proofs in this step:

* bit `i` of `remainingMask` represents counter `i + 1`;
* solved nodes and moves are exported in a deterministic order without duplicates;
* a solved nonterminal node contains every legal move exactly once;
* an owner branch contains one safe move;
* an opponent branch contains every legal move exactly once;
* every referenced child has a strictly smaller remaining mask cardinality and occurs in the DAG;
* a future checker recomputes legality, transitions, and terminal outcomes independently.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch

open CatchUp

/--
An absolute normalized state used as an exact-search key.

Bit `i` of `remainingMask` represents counter `i + 1`. The `deficit` is measured from `toMove`'s
perspective, exactly as in `CatchUp.GamePosition`.
-/
structure State where
  remainingMask : ℕ
  deficit : ℕ
  toMove : Player
deriving DecidableEq, Repr

/-- The explicit cache-key shape required of the fixed-player solver. -/
structure CacheKey where
  remainingMask : ℕ
  deficit : ℕ
  toMove : Player
deriving DecidableEq, BEq, Repr

/-- Hash a cache key without introducing an orphan `Hashable Player` instance. -/
protected def CacheKey.hash (key : CacheKey) : UInt64 :=
  let playerHash := match key.toMove with
    | .p1 => 0
    | .p2 => 1
  mixHash (hash key.remainingMask) <| mixHash (hash key.deficit) playerHash

instance : Hashable CacheKey := ⟨CacheKey.hash⟩

/-- Convert an exported state to the key used by a transposition table. -/
def State.cacheKey (state : State) : CacheKey :=
  ⟨state.remainingMask, state.deficit, state.toMove⟩

/--
The exact result of one legal move at a solved node.

`outcome` is measured from the parent state's current mover's perspective. A checker must recompute
`child` and `outcome` rather than trusting these annotations.
-/
structure MoveEvaluation where
  counter : ℕ
  child : State
  outcome : Outcome
deriving DecidableEq, Repr

/--
A node in the complete solved graph.

At a nonterminal node, `moves` contains every legal move exactly once, including non-optimal moves.
-/
structure SolvedNode where
  state : State
  outcome : Outcome
  moves : List MoveEvaluation
deriving DecidableEq, Repr

/-- The complete exact-search output for interval games of one fixed size. -/
structure SolverOutput where
  gameSize : ℕ
  openingRoots : List (ℕ × State)
  nodes : List SolvedNode
deriving DecidableEq, Repr

/--
The branching information retained at one node of a one-sided non-loss strategy.

The node's state determines which nonterminal constructor is permitted: `owner` when `toMove` is
the strategy owner, and `opponent` otherwise.
-/
inductive StrategyBranch
  | terminal
  | owner (counter : ℕ)
  | opponent (counters : List ℕ)
deriving DecidableEq, Repr

/-- One state and its prescribed or covered strategy branch. -/
structure StrategyNode where
  state : State
  branch : StrategyBranch
deriving DecidableEq, Repr

/--
A finite, serialization-friendly DAG intended to witness `CanAvoidLoss player root`.

The node list is untrusted certificate data. A future checker must establish uniqueness, coverage,
legal transitions, terminal safety, and strict progress.
-/
structure StrategyDAG where
  gameSize : ℕ
  player : Player
  root : State
  nodes : List StrategyNode
deriving DecidableEq, Repr

end CatchUpSearch
