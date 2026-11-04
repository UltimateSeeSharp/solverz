/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateComplexityFixtures.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); its `run_cmd` axiom audit dropped (solverz checks axioms with `#print axioms`).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateComplexityCompression
public import CatchUp.Earlier.CertificateComplexity

/-!
# Small full and compressed certificate witnesses

Literal data extracted by the existing least-safe policy at N = 3, 4, 7, from the
actual interval root. Each full witness is a kernel-checked upper bound, not a
minimum. Compressed witnesses use the available-maximum theorem, not an oracle.
No numerical frontier is extended. The generator and independent replay are in
research/certificate_complexity_20260929/.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateComplexityFixtures

open CatchUp CertificateChecker CertificateComplexity CertificateComplexityCompression

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def full3p1 : StrategyDAG :=
  ⟨3, .p1, ⟨7, 0, .p1⟩,
    [⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p2⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .owner 2⟩,
      ⟨⟨4, 1, .p1⟩, .owner 3⟩,
      ⟨⟨6, 1, .p2⟩, .opponent [2, 3]⟩,
      ⟨⟨7, 0, .p1⟩, .owner 1⟩]⟩

theorem full3p1_initial : InitialCertificate 3 .p1 full3p1 := by
  unfold InitialCertificate
  decide

def compressed3p1 : StrategyDAG :=
  ⟨3, .p1, ⟨7, 0, .p1⟩,
    [⟨⟨0, 2, .p2⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .terminal⟩,
      ⟨⟨4, 1, .p1⟩, .owner 3⟩,
      ⟨⟨6, 1, .p2⟩, .opponent [2, 3]⟩,
      ⟨⟨7, 0, .p1⟩, .owner 1⟩]⟩

theorem compressed3p1_checked : checkPartialCertificate
    (maximumDeficitTarget 3 .p1) compressed3p1 = true := by decide

theorem compressed3p1_safe : CanAvoidLoss .p1
    (initialPosition 3) :=
  compressed_certificate_sound compressed3p1 compressed3p1_checked

def full3p2 : StrategyDAG :=
  ⟨3, .p2, ⟨7, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .opponent [2]⟩,
      ⟨⟨2, 2, .p2⟩, .owner 2⟩,
      ⟨⟨3, 3, .p2⟩, .owner 1⟩,
      ⟨⟨4, 1, .p2⟩, .owner 3⟩,
      ⟨⟨5, 2, .p2⟩, .owner 1⟩,
      ⟨⟨6, 1, .p2⟩, .owner 3⟩,
      ⟨⟨7, 0, .p1⟩, .opponent [1, 2, 3]⟩]⟩

theorem full3p2_initial : InitialCertificate 3 .p2 full3p2 := by
  unfold InitialCertificate
  decide

def compressed3p2 : StrategyDAG :=
  ⟨3, .p2, ⟨7, 0, .p1⟩,
    [⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .opponent [2]⟩,
      ⟨⟨2, 2, .p2⟩, .terminal⟩,
      ⟨⟨3, 3, .p2⟩, .owner 1⟩,
      ⟨⟨4, 1, .p2⟩, .owner 3⟩,
      ⟨⟨5, 2, .p2⟩, .owner 1⟩,
      ⟨⟨6, 1, .p2⟩, .owner 3⟩,
      ⟨⟨7, 0, .p1⟩, .opponent [1, 2, 3]⟩]⟩

theorem compressed3p2_checked : checkPartialCertificate
    (maximumDeficitTarget 3 .p2) compressed3p2 = true := by decide

theorem compressed3p2_safe : CanAvoidLoss .p2
    (initialPosition 3) :=
  compressed_certificate_sound compressed3p2 compressed3p2_checked

def full4p1 : StrategyDAG :=
  ⟨4, .p1, ⟨15, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 2, .p2⟩, .terminal⟩,
      ⟨⟨2, 2, .p2⟩, .opponent [2]⟩,
      ⟨⟨4, 1, .p1⟩, .owner 3⟩,
      ⟨⟨4, 3, .p2⟩, .opponent [3]⟩,
      ⟨⟨6, 3, .p1⟩, .owner 2⟩,
      ⟨⟨10, 2, .p1⟩, .owner 4⟩,
      ⟨⟨12, 1, .p1⟩, .owner 4⟩,
      ⟨⟨14, 1, .p2⟩, .opponent [2, 3, 4]⟩,
      ⟨⟨15, 0, .p1⟩, .owner 1⟩]⟩

theorem full4p1_initial : InitialCertificate 4 .p1 full4p1 := by
  unfold InitialCertificate
  decide

def compressed4p1 : StrategyDAG :=
  ⟨4, .p1, ⟨15, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨2, 2, .p2⟩, .opponent [2]⟩,
      ⟨⟨4, 3, .p2⟩, .opponent [3]⟩,
      ⟨⟨6, 3, .p1⟩, .terminal⟩,
      ⟨⟨10, 2, .p1⟩, .owner 4⟩,
      ⟨⟨12, 1, .p1⟩, .owner 4⟩,
      ⟨⟨14, 1, .p2⟩, .opponent [2, 3, 4]⟩,
      ⟨⟨15, 0, .p1⟩, .owner 1⟩]⟩

theorem compressed4p1_checked : checkPartialCertificate
    (maximumDeficitTarget 4 .p1) compressed4p1 = true := by decide

theorem compressed4p1_safe : CanAvoidLoss .p1
    (initialPosition 4) :=
  compressed_certificate_sound compressed4p1 compressed4p1_checked

def full4p2 : StrategyDAG :=
  ⟨4, .p2, ⟨15, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .opponent [2]⟩,
      ⟨⟨4, 1, .p2⟩, .owner 3⟩,
      ⟨⟨4, 3, .p1⟩, .opponent [3]⟩,
      ⟨⟨4, 3, .p2⟩, .owner 3⟩,
      ⟨⟨6, 3, .p2⟩, .owner 2⟩,
      ⟨⟨7, 4, .p2⟩, .owner 1⟩,
      ⟨⟨8, 2, .p2⟩, .owner 4⟩,
      ⟨⟨10, 2, .p2⟩, .owner 4⟩,
      ⟨⟨11, 3, .p2⟩, .owner 1⟩,
      ⟨⟨12, 1, .p1⟩, .opponent [3, 4]⟩,
      ⟨⟨12, 1, .p2⟩, .owner 4⟩,
      ⟨⟨13, 2, .p2⟩, .owner 1⟩,
      ⟨⟨14, 1, .p2⟩, .owner 2⟩,
      ⟨⟨15, 0, .p1⟩, .opponent [1, 2, 3, 4]⟩]⟩

theorem full4p2_initial : InitialCertificate 4 .p2 full4p2 := by
  unfold InitialCertificate
  decide

def compressed4p2 : StrategyDAG :=
  ⟨4, .p2, ⟨15, 0, .p1⟩,
    [⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨2, 2, .p1⟩, .opponent [2]⟩,
      ⟨⟨4, 3, .p1⟩, .opponent [3]⟩,
      ⟨⟨4, 3, .p2⟩, .terminal⟩,
      ⟨⟨6, 3, .p2⟩, .terminal⟩,
      ⟨⟨7, 4, .p2⟩, .owner 1⟩,
      ⟨⟨8, 2, .p2⟩, .owner 4⟩,
      ⟨⟨10, 2, .p2⟩, .owner 4⟩,
      ⟨⟨11, 3, .p2⟩, .owner 1⟩,
      ⟨⟨12, 1, .p1⟩, .opponent [3, 4]⟩,
      ⟨⟨12, 1, .p2⟩, .owner 4⟩,
      ⟨⟨13, 2, .p2⟩, .owner 1⟩,
      ⟨⟨14, 1, .p2⟩, .owner 2⟩,
      ⟨⟨15, 0, .p1⟩, .opponent [1, 2, 3, 4]⟩]⟩

theorem compressed4p2_checked : checkPartialCertificate
    (maximumDeficitTarget 4 .p2) compressed4p2 = true := by decide

theorem compressed4p2_safe : CanAvoidLoss .p2
    (initialPosition 4) :=
  compressed_certificate_sound compressed4p2 compressed4p2_checked

def full7p1 : StrategyDAG :=
  ⟨7, .p1, ⟨127, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p2⟩, .terminal⟩,
      ⟨⟨0, 4, .p2⟩, .terminal⟩,
      ⟨⟨0, 6, .p2⟩, .terminal⟩,
      ⟨⟨4, 3, .p2⟩, .opponent [3]⟩,
      ⟨⟨4, 5, .p2⟩, .terminal⟩,
      ⟨⟨8, 2, .p1⟩, .owner 4⟩,
      ⟨⟨8, 4, .p2⟩, .opponent [4]⟩,
      ⟨⟨16, 1, .p1⟩, .owner 5⟩,
      ⟨⟨16, 3, .p1⟩, .owner 5⟩,
      ⟨⟨16, 5, .p2⟩, .opponent [5]⟩,
      ⟨⟨20, 6, .p1⟩, .owner 3⟩,
      ⟨⟨24, 3, .p2⟩, .opponent [4, 5]⟩,
      ⟨⟨32, 2, .p1⟩, .owner 6⟩,
      ⟨⟨32, 4, .p1⟩, .owner 6⟩,
      ⟨⟨32, 6, .p1⟩, .owner 6⟩,
      ⟨⟨32, 6, .p2⟩, .opponent [6]⟩,
      ⟨⟨36, 3, .p1⟩, .owner 6⟩,
      ⟨⟨36, 5, .p1⟩, .owner 3⟩,
      ⟨⟨40, 2, .p1⟩, .owner 6⟩,
      ⟨⟨48, 1, .p1⟩, .owner 6⟩,
      ⟨⟨48, 3, .p2⟩, .opponent [5, 6]⟩,
      ⟨⟨56, 1, .p1⟩, .owner 4⟩,
      ⟨⟨56, 5, .p1⟩, .owner 4⟩,
      ⟨⟨56, 7, .p1⟩, .owner 5⟩,
      ⟨⟨60, 4, .p1⟩, .owner 3⟩,
      ⟨⟨62, 6, .p1⟩, .owner 2⟩,
      ⟨⟨64, 1, .p1⟩, .owner 7⟩,
      ⟨⟨64, 3, .p1⟩, .owner 7⟩,
      ⟨⟨64, 5, .p1⟩, .owner 7⟩,
      ⟨⟨68, 2, .p1⟩, .owner 7⟩,
      ⟨⟨68, 4, .p1⟩, .owner 3⟩,
      ⟨⟨80, 2, .p1⟩, .owner 7⟩,
      ⟨⟨84, 1, .p2⟩, .opponent [3, 5, 7]⟩,
      ⟨⟨88, 4, .p1⟩, .owner 7⟩,
      ⟨⟨88, 6, .p1⟩, .owner 4⟩,
      ⟨⟨92, 3, .p1⟩, .owner 4⟩,
      ⟨⟨94, 5, .p1⟩, .owner 2⟩,
      ⟨⟨96, 1, .p1⟩, .owner 7⟩,
      ⟨⟨96, 1, .p2⟩, .opponent [6, 7]⟩,
      ⟨⟨96, 3, .p2⟩, .opponent [6, 7]⟩,
      ⟨⟨100, 2, .p2⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨100, 4, .p2⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨104, 3, .p1⟩, .owner 4⟩,
      ⟨⟨104, 5, .p1⟩, .owner 4⟩,
      ⟨⟨108, 2, .p1⟩, .owner 4⟩,
      ⟨⟨110, 4, .p1⟩, .owner 2⟩,
      ⟨⟨112, 2, .p1⟩, .owner 5⟩,
      ⟨⟨112, 4, .p1⟩, .owner 5⟩,
      ⟨⟨116, 1, .p1⟩, .owner 5⟩,
      ⟨⟨118, 3, .p1⟩, .owner 2⟩,
      ⟨⟨120, 0, .p2⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p2⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨122, 2, .p1⟩, .owner 2⟩,
      ⟨⟨124, 1, .p1⟩, .owner 3⟩,
      ⟨⟨126, 1, .p2⟩, .opponent [2, 3, 4, 5, 6, 7]⟩,
      ⟨⟨127, 0, .p1⟩, .owner 1⟩]⟩

theorem full7p1_initial : InitialCertificate 7 .p1 full7p1 := by
  unfold InitialCertificate
  decide

def compressed7p1 : StrategyDAG :=
  ⟨7, .p1, ⟨127, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 2, .p2⟩, .terminal⟩,
      ⟨⟨0, 4, .p2⟩, .terminal⟩,
      ⟨⟨0, 6, .p2⟩, .terminal⟩,
      ⟨⟨4, 3, .p2⟩, .opponent [3]⟩,
      ⟨⟨4, 5, .p2⟩, .terminal⟩,
      ⟨⟨8, 2, .p1⟩, .owner 4⟩,
      ⟨⟨8, 4, .p2⟩, .opponent [4]⟩,
      ⟨⟨16, 1, .p1⟩, .owner 5⟩,
      ⟨⟨16, 3, .p1⟩, .owner 5⟩,
      ⟨⟨16, 5, .p2⟩, .opponent [5]⟩,
      ⟨⟨20, 6, .p1⟩, .owner 3⟩,
      ⟨⟨24, 3, .p2⟩, .opponent [4, 5]⟩,
      ⟨⟨32, 2, .p1⟩, .owner 6⟩,
      ⟨⟨32, 4, .p1⟩, .owner 6⟩,
      ⟨⟨32, 6, .p1⟩, .terminal⟩,
      ⟨⟨32, 6, .p2⟩, .opponent [6]⟩,
      ⟨⟨36, 3, .p1⟩, .owner 6⟩,
      ⟨⟨36, 5, .p1⟩, .owner 3⟩,
      ⟨⟨40, 2, .p1⟩, .owner 6⟩,
      ⟨⟨48, 1, .p1⟩, .owner 6⟩,
      ⟨⟨56, 5, .p1⟩, .owner 4⟩,
      ⟨⟨56, 7, .p1⟩, .owner 5⟩,
      ⟨⟨62, 6, .p1⟩, .terminal⟩,
      ⟨⟨64, 1, .p1⟩, .owner 7⟩,
      ⟨⟨64, 3, .p1⟩, .owner 7⟩,
      ⟨⟨64, 5, .p1⟩, .owner 7⟩,
      ⟨⟨68, 2, .p1⟩, .owner 7⟩,
      ⟨⟨68, 4, .p1⟩, .owner 3⟩,
      ⟨⟨80, 2, .p1⟩, .owner 7⟩,
      ⟨⟨84, 1, .p2⟩, .opponent [3, 5, 7]⟩,
      ⟨⟨88, 4, .p1⟩, .owner 7⟩,
      ⟨⟨88, 6, .p1⟩, .owner 4⟩,
      ⟨⟨92, 3, .p1⟩, .owner 4⟩,
      ⟨⟨94, 5, .p1⟩, .owner 2⟩,
      ⟨⟨96, 1, .p1⟩, .owner 7⟩,
      ⟨⟨96, 1, .p2⟩, .opponent [6, 7]⟩,
      ⟨⟨96, 3, .p2⟩, .opponent [6, 7]⟩,
      ⟨⟨100, 2, .p2⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨100, 4, .p2⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨104, 3, .p1⟩, .owner 4⟩,
      ⟨⟨104, 5, .p1⟩, .owner 4⟩,
      ⟨⟨108, 2, .p1⟩, .owner 4⟩,
      ⟨⟨110, 4, .p1⟩, .owner 2⟩,
      ⟨⟨112, 2, .p1⟩, .owner 5⟩,
      ⟨⟨112, 4, .p1⟩, .owner 5⟩,
      ⟨⟨116, 1, .p1⟩, .owner 5⟩,
      ⟨⟨118, 3, .p1⟩, .owner 2⟩,
      ⟨⟨120, 0, .p2⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p2⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨122, 2, .p1⟩, .owner 2⟩,
      ⟨⟨124, 1, .p1⟩, .owner 3⟩,
      ⟨⟨126, 1, .p2⟩, .opponent [2, 3, 4, 5, 6, 7]⟩,
      ⟨⟨127, 0, .p1⟩, .owner 1⟩]⟩

theorem compressed7p1_checked : checkPartialCertificate
    (maximumDeficitTarget 7 .p1) compressed7p1 = true := by decide

theorem compressed7p1_safe : CanAvoidLoss .p1
    (initialPosition 7) :=
  compressed_certificate_sound compressed7p1 compressed7p1_checked

def full7p2 : StrategyDAG :=
  ⟨7, .p2, ⟨127, 0, .p1⟩,
    [⟨⟨0, 0, .p1⟩, .terminal⟩,
      ⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨0, 4, .p1⟩, .terminal⟩,
      ⟨⟨0, 6, .p1⟩, .terminal⟩,
      ⟨⟨4, 3, .p1⟩, .opponent [3]⟩,
      ⟨⟨4, 5, .p1⟩, .terminal⟩,
      ⟨⟨8, 2, .p2⟩, .owner 4⟩,
      ⟨⟨8, 4, .p1⟩, .opponent [4]⟩,
      ⟨⟨8, 6, .p1⟩, .terminal⟩,
      ⟨⟨16, 1, .p2⟩, .owner 5⟩,
      ⟨⟨16, 3, .p2⟩, .owner 5⟩,
      ⟨⟨16, 5, .p1⟩, .opponent [5]⟩,
      ⟨⟨16, 5, .p2⟩, .owner 5⟩,
      ⟨⟨20, 6, .p2⟩, .owner 3⟩,
      ⟨⟨24, 1, .p2⟩, .owner 5⟩,
      ⟨⟨24, 3, .p1⟩, .opponent [4, 5]⟩,
      ⟨⟨32, 2, .p2⟩, .owner 6⟩,
      ⟨⟨32, 4, .p2⟩, .owner 6⟩,
      ⟨⟨32, 6, .p1⟩, .opponent [6]⟩,
      ⟨⟨32, 6, .p2⟩, .owner 6⟩,
      ⟨⟨36, 3, .p2⟩, .owner 6⟩,
      ⟨⟨36, 5, .p2⟩, .owner 3⟩,
      ⟨⟨40, 0, .p2⟩, .owner 6⟩,
      ⟨⟨40, 2, .p2⟩, .owner 6⟩,
      ⟨⟨48, 1, .p1⟩, .opponent [5, 6]⟩,
      ⟨⟨48, 1, .p2⟩, .owner 6⟩,
      ⟨⟨48, 3, .p1⟩, .opponent [5, 6]⟩,
      ⟨⟨56, 1, .p2⟩, .owner 4⟩,
      ⟨⟨56, 3, .p2⟩, .owner 4⟩,
      ⟨⟨56, 5, .p1⟩, .opponent [4, 5, 6]⟩,
      ⟨⟨56, 5, .p2⟩, .owner 4⟩,
      ⟨⟨56, 7, .p2⟩, .owner 5⟩,
      ⟨⟨60, 4, .p2⟩, .owner 3⟩,
      ⟨⟨60, 6, .p2⟩, .owner 3⟩,
      ⟨⟨62, 6, .p2⟩, .owner 2⟩,
      ⟨⟨63, 7, .p2⟩, .owner 1⟩,
      ⟨⟨64, 1, .p2⟩, .owner 7⟩,
      ⟨⟨64, 3, .p2⟩, .owner 7⟩,
      ⟨⟨64, 5, .p2⟩, .owner 7⟩,
      ⟨⟨68, 2, .p2⟩, .owner 7⟩,
      ⟨⟨68, 4, .p2⟩, .owner 3⟩,
      ⟨⟨80, 2, .p1⟩, .opponent [5, 7]⟩,
      ⟨⟨80, 2, .p2⟩, .owner 7⟩,
      ⟨⟨84, 1, .p1⟩, .opponent [3, 5, 7]⟩,
      ⟨⟨88, 2, .p2⟩, .owner 4⟩,
      ⟨⟨88, 4, .p2⟩, .owner 7⟩,
      ⟨⟨88, 6, .p2⟩, .owner 4⟩,
      ⟨⟨92, 3, .p2⟩, .owner 4⟩,
      ⟨⟨92, 5, .p2⟩, .owner 3⟩,
      ⟨⟨94, 5, .p2⟩, .owner 2⟩,
      ⟨⟨95, 6, .p2⟩, .owner 1⟩,
      ⟨⟨96, 1, .p1⟩, .opponent [6, 7]⟩,
      ⟨⟨96, 1, .p2⟩, .owner 7⟩,
      ⟨⟨96, 3, .p1⟩, .opponent [6, 7]⟩,
      ⟨⟨100, 2, .p1⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨100, 4, .p1⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨104, 1, .p2⟩, .owner 4⟩,
      ⟨⟨104, 3, .p2⟩, .owner 4⟩,
      ⟨⟨104, 5, .p2⟩, .owner 4⟩,
      ⟨⟨108, 2, .p2⟩, .owner 4⟩,
      ⟨⟨108, 4, .p2⟩, .owner 3⟩,
      ⟨⟨110, 4, .p2⟩, .owner 2⟩,
      ⟨⟨111, 5, .p2⟩, .owner 1⟩,
      ⟨⟨112, 2, .p2⟩, .owner 5⟩,
      ⟨⟨112, 4, .p2⟩, .owner 5⟩,
      ⟨⟨116, 1, .p2⟩, .owner 5⟩,
      ⟨⟨116, 3, .p2⟩, .owner 5⟩,
      ⟨⟨118, 3, .p2⟩, .owner 2⟩,
      ⟨⟨119, 4, .p2⟩, .owner 1⟩,
      ⟨⟨120, 0, .p1⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p1⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p2⟩, .owner 7⟩,
      ⟨⟨122, 2, .p2⟩, .owner 2⟩,
      ⟨⟨123, 3, .p2⟩, .owner 1⟩,
      ⟨⟨124, 1, .p1⟩, .opponent [3, 4, 5, 6, 7]⟩,
      ⟨⟨124, 1, .p2⟩, .owner 3⟩,
      ⟨⟨125, 2, .p2⟩, .owner 1⟩,
      ⟨⟨126, 1, .p2⟩, .owner 2⟩,
      ⟨⟨127, 0, .p1⟩, .opponent [1, 2, 3, 4, 5, 6, 7]⟩]⟩

theorem full7p2_initial : InitialCertificate 7 .p2 full7p2 := by
  unfold InitialCertificate
  decide

def compressed7p2 : StrategyDAG :=
  ⟨7, .p2, ⟨127, 0, .p1⟩,
    [⟨⟨0, 0, .p2⟩, .terminal⟩,
      ⟨⟨0, 2, .p1⟩, .terminal⟩,
      ⟨⟨0, 4, .p1⟩, .terminal⟩,
      ⟨⟨0, 6, .p1⟩, .terminal⟩,
      ⟨⟨4, 3, .p1⟩, .opponent [3]⟩,
      ⟨⟨4, 5, .p1⟩, .terminal⟩,
      ⟨⟨8, 2, .p2⟩, .owner 4⟩,
      ⟨⟨8, 4, .p1⟩, .opponent [4]⟩,
      ⟨⟨8, 6, .p1⟩, .terminal⟩,
      ⟨⟨16, 1, .p2⟩, .owner 5⟩,
      ⟨⟨16, 3, .p2⟩, .owner 5⟩,
      ⟨⟨16, 5, .p1⟩, .opponent [5]⟩,
      ⟨⟨16, 5, .p2⟩, .terminal⟩,
      ⟨⟨20, 6, .p2⟩, .owner 3⟩,
      ⟨⟨24, 1, .p2⟩, .owner 5⟩,
      ⟨⟨24, 3, .p1⟩, .opponent [4, 5]⟩,
      ⟨⟨32, 2, .p2⟩, .owner 6⟩,
      ⟨⟨32, 4, .p2⟩, .owner 6⟩,
      ⟨⟨32, 6, .p1⟩, .opponent [6]⟩,
      ⟨⟨32, 6, .p2⟩, .terminal⟩,
      ⟨⟨36, 3, .p2⟩, .owner 6⟩,
      ⟨⟨36, 5, .p2⟩, .owner 3⟩,
      ⟨⟨40, 0, .p2⟩, .owner 6⟩,
      ⟨⟨40, 2, .p2⟩, .owner 6⟩,
      ⟨⟨48, 1, .p1⟩, .opponent [5, 6]⟩,
      ⟨⟨48, 1, .p2⟩, .owner 6⟩,
      ⟨⟨56, 5, .p1⟩, .opponent [4, 5, 6]⟩,
      ⟨⟨56, 5, .p2⟩, .owner 4⟩,
      ⟨⟨56, 7, .p2⟩, .owner 5⟩,
      ⟨⟨60, 6, .p2⟩, .terminal⟩,
      ⟨⟨62, 6, .p2⟩, .terminal⟩,
      ⟨⟨63, 7, .p2⟩, .owner 1⟩,
      ⟨⟨64, 1, .p2⟩, .owner 7⟩,
      ⟨⟨64, 3, .p2⟩, .owner 7⟩,
      ⟨⟨64, 5, .p2⟩, .owner 7⟩,
      ⟨⟨68, 2, .p2⟩, .owner 7⟩,
      ⟨⟨68, 4, .p2⟩, .owner 3⟩,
      ⟨⟨80, 2, .p1⟩, .opponent [5, 7]⟩,
      ⟨⟨80, 2, .p2⟩, .owner 7⟩,
      ⟨⟨84, 1, .p1⟩, .opponent [3, 5, 7]⟩,
      ⟨⟨88, 2, .p2⟩, .owner 4⟩,
      ⟨⟨88, 4, .p2⟩, .owner 7⟩,
      ⟨⟨88, 6, .p2⟩, .owner 4⟩,
      ⟨⟨92, 3, .p2⟩, .owner 4⟩,
      ⟨⟨92, 5, .p2⟩, .owner 3⟩,
      ⟨⟨94, 5, .p2⟩, .owner 2⟩,
      ⟨⟨95, 6, .p2⟩, .owner 1⟩,
      ⟨⟨96, 1, .p1⟩, .opponent [6, 7]⟩,
      ⟨⟨96, 1, .p2⟩, .owner 7⟩,
      ⟨⟨96, 3, .p1⟩, .opponent [6, 7]⟩,
      ⟨⟨100, 2, .p1⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨100, 4, .p1⟩, .opponent [3, 6, 7]⟩,
      ⟨⟨104, 1, .p2⟩, .owner 4⟩,
      ⟨⟨104, 3, .p2⟩, .owner 4⟩,
      ⟨⟨104, 5, .p2⟩, .owner 4⟩,
      ⟨⟨108, 2, .p2⟩, .owner 4⟩,
      ⟨⟨108, 4, .p2⟩, .owner 3⟩,
      ⟨⟨110, 4, .p2⟩, .owner 2⟩,
      ⟨⟨111, 5, .p2⟩, .owner 1⟩,
      ⟨⟨112, 2, .p2⟩, .owner 5⟩,
      ⟨⟨112, 4, .p2⟩, .owner 5⟩,
      ⟨⟨116, 1, .p2⟩, .owner 5⟩,
      ⟨⟨116, 3, .p2⟩, .owner 5⟩,
      ⟨⟨118, 3, .p2⟩, .owner 2⟩,
      ⟨⟨119, 4, .p2⟩, .owner 1⟩,
      ⟨⟨120, 0, .p1⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p1⟩, .opponent [4, 5, 6, 7]⟩,
      ⟨⟨120, 2, .p2⟩, .owner 7⟩,
      ⟨⟨122, 2, .p2⟩, .owner 2⟩,
      ⟨⟨123, 3, .p2⟩, .owner 1⟩,
      ⟨⟨124, 1, .p1⟩, .opponent [3, 4, 5, 6, 7]⟩,
      ⟨⟨124, 1, .p2⟩, .owner 3⟩,
      ⟨⟨125, 2, .p2⟩, .owner 1⟩,
      ⟨⟨126, 1, .p2⟩, .owner 2⟩,
      ⟨⟨127, 0, .p1⟩, .opponent [1, 2, 3, 4, 5, 6, 7]⟩]⟩

theorem compressed7p2_checked : checkPartialCertificate
    (maximumDeficitTarget 7 .p2) compressed7p2 = true := by decide

theorem compressed7p2_safe : CanAvoidLoss .p2
    (initialPosition 7) :=
  compressed_certificate_sound compressed7p2 compressed7p2_checked

/-- Node counts of the literal witnesses; these are not claims of minimality. -/
theorem witness_node_counts :
    full3p1.nodes.length = 6 ∧
    compressed3p1.nodes.length = 5 ∧
    full3p2.nodes.length = 10 ∧
    compressed3p2.nodes.length = 9 ∧
    full4p1.nodes.length = 10 ∧
    compressed4p1.nodes.length = 8 ∧
    full4p2.nodes.length = 17 ∧
    compressed4p2.nodes.length = 15 ∧
    full7p1.nodes.length = 58 ∧
    compressed7p1.nodes.length = 54 ∧
    full7p2.nodes.length = 80 ∧
    compressed7p2.nodes.length = 75 := by decide

end CatchUpSearch.CertificateComplexityFixtures
