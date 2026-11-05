module

public import SignedDifferenceSets.Check
public import SignedDifferenceSets.Contraction

/-!
# N32: no (20, 17, 8) SDS in C₂ × C₁₀

Open in Gordon's table (`SDS(20,17,8,[2,10])`, 2026-11-05). Contract along
C₂ × C₁₀ → C₅ (F3): every fibre has 4 elements, so the coset sums `a` lie in [−4, 4],
have square sum 17 + 8 · 3 = 41 and autocorrelation 8 · 4 = 32 at every shift `g ≠ 0`;
`decide` finds no such vector.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N32

/-- The projection C₂ × C₁₀ → C₅. -/
def proj : ZMod 2 × ZMod 10 →+ ZMod 5 :=
  (ZMod.castHom (by norm_num : 5 ∣ 10) (ZMod 5)).toAddMonoidHom.comp
    (AddMonoidHom.snd (ZMod 2) (ZMod 10))

theorem fibre_card (h : ZMod 5) : (fibre proj h).card = 4 := by
  revert h; decide

/-- What contraction to C₅ demands of the coset sums. -/
def Contracted (a : ZMod 5 → ℤ) : Prop :=
  ∑ h, a h * a h = 41 ∧ ∀ g : ZMod 5, g ≠ 0 → ∑ h, a h * a (h + g) = 32

instance (a : ZMod 5 → ℤ) : Decidable (Contracted a) := by
  unfold Contracted; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates every sign pattern (or vector) in the kernel.
theorem no_vector : ∀ a0 ∈ Finset.Icc (-4 : ℤ) 4, ∀ a1 ∈ Finset.Icc (-4 : ℤ) 4,
    ∀ a2 ∈ Finset.Icc (-4 : ℤ) 4, ∀ a3 ∈ Finset.Icc (-4 : ℤ) 4,
    ∀ a4 ∈ Finset.Icc (-4 : ℤ) 4,
      ¬ Contracted (fun h : ZMod 5 => ![a0, a1, a2, a3, a4] h) := by
  decide

theorem eq_vec (a : ZMod 5 → ℤ) :
    a = fun h : ZMod 5 => ![a 0, a 1, a 2, a 3, a 4] h := by
  funext h
  fin_cases h <;> rfl

/-- N32: C₂ × C₁₀ has no signed difference set with parameters (20, 17, 8). -/
theorem not_hasSDS : ¬ HasSDS (ZMod 2 × ZMod 10) 17 8 := by
  rintro ⟨D, hD⟩
  have hb (h : ZMod 5) : contract proj D h ∈ Finset.Icc (-4 : ℤ) 4 := by
    have := abs_contract_le proj D h
    rw [fibre_card] at this
    exact Finset.mem_Icc.2 (abs_le.1 (by exact_mod_cast this))
  have hc : Contracted (contract proj D) := by
    refine ⟨?_, fun g hg => ?_⟩
    · rw [hD.contract_sq proj, fibre_card]; norm_num
    · rw [hD.contract_autocorr proj g hg, fibre_card]; norm_num
  rw [eq_vec (contract proj D)] at hc
  exact no_vector _ (hb 0) _ (hb 1) _ (hb 2) _ (hb 3) _ (hb 4) hc

end SignedDifferenceSets.Answer.N32
