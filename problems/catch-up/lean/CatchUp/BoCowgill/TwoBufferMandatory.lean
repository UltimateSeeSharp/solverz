/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TwoBufferMandatory.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.TwoBufferProtocol

/-!
# A certified full-instance two-buffer controller

This table is generated from the saved JSON policy. Its choices are data, not
assumptions: kernel evaluation checks every universal branch against the real
Catch-Up transitions and strict-win strategy filter. This proves the mandatory
finite instance only, not a parametric adjacent-hole translator.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TwoBuffer

/-- Explicit paired-state actions; ownership histories are preserved in the JSON certificate. -/
def policyEntries : List ((GamePosition × GamePosition) × Action) := [
  ((⟨⟨{2, 5, 6, 9, 10, 11}, 1⟩, .p1⟩, ⟨⟨{2, 5, 6, 7, 10, 11}, 1⟩, .p1⟩), .actualPick 2),
  ((⟨⟨{5, 6, 9, 10, 11}, 1⟩, .p2⟩, ⟨⟨{2, 5, 6, 7, 10, 11}, 1⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 6, 9, 10, 11}, 1⟩, .p2⟩, ⟨⟨{2, 6, 7, 10, 11}, 4⟩, .p2⟩), .shadowPick 2),
  ((⟨⟨{5, 6, 9, 10, 11}, 1⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualOpponent),
  ((⟨⟨{6, 9, 10, 11}, 4⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 11),
  ((⟨⟨{6, 9, 10}, 7⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .shadowPick 7),
  ((⟨⟨{6, 9, 10}, 7⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualOpponent),
  ((⟨⟨{9, 10}, 1⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{9, 10}, 1⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualOpponent),
  ((⟨⟨{10}, 8⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{6}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{9}, 9⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualPick 9),
  ((⟨⟨{}, 0⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 0⟩, .p2⟩, ⟨⟨{6}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{6, 10}, 2⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualPick 10),
  ((⟨⟨{6}, 8⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{6}, 8⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{6}, 8⟩, .p2⟩, ⟨⟨{6}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{6, 9}, 3⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualPick 9),
  ((⟨⟨{6}, 6⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{6}, 6⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualOpponent),
  ((⟨⟨{}, 0⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 0⟩, .p1⟩, ⟨⟨{6}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 9, 10, 11}, 5⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 9),
  ((⟨⟨{5, 10, 11}, 4⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .shadowPick 7),
  ((⟨⟨{5, 10, 11}, 4⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualOpponent),
  ((⟨⟨{10, 11}, 1⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualPick 11),
  ((⟨⟨{10}, 10⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 10⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualOpponent),
  ((⟨⟨{5, 11}, 6⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualPick 5),
  ((⟨⟨{11}, 1⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{11}, 1⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualPick 11),
  ((⟨⟨{}, 10⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 6),
  ((⟨⟨{}, 10⟩, .p2⟩, ⟨⟨{10}, 0⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 10}, 7⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualPick 5),
  ((⟨⟨{10}, 2⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 2⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualPick 10),
  ((⟨⟨{}, 8⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 6),
  ((⟨⟨{}, 8⟩, .p2⟩, ⟨⟨{10}, 0⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 6, 10, 11}, 8⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 5),
  ((⟨⟨{6, 10, 11}, 3⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 6),
  ((⟨⟨{10, 11}, 3⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .shadowPick 6),
  ((⟨⟨{10, 11}, 3⟩, .p2⟩, ⟨⟨{7, 10, 11}, 4⟩, .p1⟩), .actualOpponent),
  ((⟨⟨{11}, 7⟩, .p1⟩, ⟨⟨{7, 10, 11}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{11}, 7⟩, .p1⟩, ⟨⟨{10, 11}, 3⟩, .p2⟩), .actualPick 11),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{10, 11}, 3⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{11}, 7⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{11}, 7⟩, .p1⟩, ⟨⟨{7, 11}, 6⟩, .p2⟩), .actualPick 11),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{7, 11}, 6⟩, .p2⟩), .shadowPick 11),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{7}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{11}, 7⟩, .p1⟩, ⟨⟨{7, 10}, 7⟩, .p2⟩), .actualPick 11),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{7, 10}, 7⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 4⟩, .p2⟩, ⟨⟨{7}, 3⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 8⟩, .p1⟩, ⟨⟨{7, 10, 11}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 8⟩, .p1⟩, ⟨⟨{10, 11}, 3⟩, .p2⟩), .actualPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{10, 11}, 3⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{11}, 7⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 8⟩, .p1⟩, ⟨⟨{7, 11}, 6⟩, .p2⟩), .actualPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{7, 11}, 6⟩, .p2⟩), .shadowPick 11),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{7}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{10}, 8⟩, .p1⟩, ⟨⟨{7, 10}, 7⟩, .p2⟩), .actualPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{7, 10}, 7⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 2⟩, .p2⟩, ⟨⟨{7}, 3⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 6, 9, 11}, 9⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 5),
  ((⟨⟨{6, 9, 11}, 4⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 9),
  ((⟨⟨{6, 11}, 5⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .shadowPick 7),
  ((⟨⟨{6, 11}, 5⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualOpponent),
  ((⟨⟨{6}, 6⟩, .p1⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{6}, 6⟩, .p1⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .actualPick 6),
  ((⟨⟨{}, 0⟩, .p2⟩, ⟨⟨{6, 10}, 6⟩, .p2⟩), .shadowPick 10),
  ((⟨⟨{}, 0⟩, .p2⟩, ⟨⟨{6}, 4⟩, .p1⟩), .shadowStrategy),
  ((⟨⟨{5, 6, 9, 10}, 10⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 5),
  ((⟨⟨{6, 9, 10}, 5⟩, .p1⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .actualPick 9),
  ((⟨⟨{6, 10}, 4⟩, .p2⟩, ⟨⟨{6, 7, 10, 11}, 2⟩, .p2⟩), .shadowPick 7),
  ((⟨⟨{6, 10}, 4⟩, .p2⟩, ⟨⟨{6, 10, 11}, 5⟩, .p1⟩), .actualOpponent)]

/-- Table lookup with an invalid default, so unlisted nonterminal states fail the checker. -/
def policy (u v : GamePosition) : Action :=
  ((policyEntries.find? fun row ↦ decide (row.1 = (u,v))).map Prod.snd).getD (.actualPick 0)

/-- Kernel validation covers every actual adversary and every winning shadow-strategy reply. -/
theorem mandatory_policy_checked :
    runCheck policy 12 ⟨AdjacentHoleExchange.exchangeLeft, .p1⟩
      ⟨AdjacentHoleExchange.exchangeRight, .p1⟩ = true := by
  decide +kernel

/-- A uniform causal atomic-two-buffer protocol exists for the full mandatory instance. -/
theorem mandatory_protocol :
    Protocol ⟨AdjacentHoleExchange.exchangeLeft, .p1⟩
      ⟨AdjacentHoleExchange.exchangeRight, .p1⟩ :=
  run_check_sound _ _ _ _ mandatory_policy_checked

end CatchUp.TwoBuffer
