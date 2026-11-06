module

public import CatchUp.BoCowgill.DenseLossGeneral
public import CatchUp.Small

/-!
# One start: the maximal opening

The level law (C28) with the opening `N` makes `{1..N}` a draw once `({1..N-1}, N)`, the mover
trailing by `N`, is a draw. Its no-loss half is C77 (b″) (`after_max_opening_nonloss`), so C1
needs only the no-win half from this one start (`conjecture_of_max_opening`, ideator fresh08).
-/

@[expose] public section

namespace CatchUp

/-- `{1..N} \ {N} = {1..N-1}`. -/
theorem Icc_erase_top (N : ℕ) : (Finset.Icc 1 N).erase N = Finset.Icc 1 (N - 1) := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

/-- The opening `N` never loses (C77 (b″)), in `valueAux` form. -/
theorem max_opening_ne_loss {N : ℕ} (hN : 3 ≤ N) :
    valueAux (Finset.Icc 1 (N - 1)) 0 N false ≠ .loss := by
  have h := DenseLossGeneral.after_max_opening_nonloss N hN
  have he := Position.value_eq_value_aux ((Finset.Icc 1 N).erase N) 0 N (Nat.zero_le _)
  rw [Nat.sub_zero, Icc_erase_top] at he
  rw [← he]
  change (⟨(Finset.Icc 1 N).erase N, N⟩ : Position).value ≠ .loss at h
  rwa [Icc_erase_top] at h

/-- **One start** (fresh08): if the mover trailing by `N` on `{1..N-1}` cannot win for every
even-total `N ≥ 13`, the conjecture holds. -/
theorem conjecture_of_max_opening
    (h : ∀ N : ℕ, 13 ≤ N → Even (N * (N + 1) / 2) →
      valueAux (Finset.Icc 1 (N - 1)) 0 N false ≠ .win) :
    Goal := by
  intro N hN
  by_cases h12 : N ≤ 12
  · exact conjecture_le_twelve N h12 hN
  rw [value, valueAux_true_eq_false]
  have hmem : N ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  apply level_law hmem
  rw [Icc_erase_top, Nat.zero_add]
  have hw := h N (by omega) hN
  have hl := max_opening_ne_loss (N := N) (by omega)
  revert hw hl
  cases valueAux (Finset.Icc 1 (N - 1)) 0 N false <;> simp

end CatchUp
