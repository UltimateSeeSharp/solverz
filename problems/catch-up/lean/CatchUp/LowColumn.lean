module

public import CatchUp.Small
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The low column of blocks gives the conjecture

C104: a block `{a..a + n - 1}` with `n ≥ 6` at a low height `a ≤ n/2` draws at every deficit
`d ≤ n - 1` of the draw parity. Its entries `(n, a, d) = (N, 1, 0)` for `N ≡ 0 (mod 4)` and
`(N - 1, 2, 1)` for `N ≡ 3 (mod 4)` are C27's two families, so C104 gives C1 for `N ≥ 13` and
`conjecture_le_twelve` the rest (`conjecture_of_low_column`).
-/

@[expose] public section

namespace CatchUp

/-- C104, the low column of blocks (I23), at base score 0. -/
def LowColumnConjecture : Prop :=
  ∀ n a d : ℕ, 6 ≤ n → 1 ≤ a → 2 * a ≤ n → d + 1 ≤ n →
    (d + ∑ x ∈ (Finset.range n).map (addLeftEmbedding a), x) % 2 = 0 →
    valueAux ((Finset.range n).map (addLeftEmbedding a)) 0 d false = .draw

/-- `{a..a + n - 1}` as a block of `n` offsets at height `a`. -/
theorem Icc_eq_block_map {a n : ℕ} (hn : 1 ≤ n) :
    Finset.Icc a (a + n - 1) = (Finset.range n).map (addLeftEmbedding a) := by
  ext y
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
  constructor
  · intro hy
    exact ⟨y - a, by omega, by omega⟩
  · rintro ⟨x, hx, rfl⟩
    omega

theorem sum_Icc_one_mul_two (N : ℕ) : (∑ x ∈ Finset.Icc 1 N, x) * 2 = N * (N + 1) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), add_mul, ih]
    ring

/-- **I23's reduction**: the low column (C104) gives the conjecture. -/
theorem conjecture_of_low_column (h : LowColumnConjecture) : Conjecture := by
  intro N hN
  by_cases h12 : N ≤ 12
  · exact conjecture_le_twelve N h12 hN
  rw [value, valueAux_true_eq_false]
  have hS := sum_Icc_one_mul_two N
  obtain ⟨t, ht⟩ := hN
  rcases (even_triangle_iff N).1 ⟨t, ht⟩ with h4 | h4
  · -- `{1..N}` at a tie: `(n, a, d) = (N, 1, 0)`.
    have hb := Icc_eq_block_map (a := 1) (n := N) (by omega)
    rw [show 1 + N - 1 = N by omega] at hb
    rw [hb]
    refine h N 1 0 (by omega) le_rfl (by omega) (by omega) ?_
    rw [← hb]
    have : ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) / 2 := by omega
    omega
  · -- The token `1` (C26), then `{2..N}` trailing by 1: `(n, a, d) = (N - 1, 2, 1)`.
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    refine token_lemma h1 (fun x hx => (Finset.mem_Icc.mp hx).1) ?_
    have he : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    have hs2 : ∑ x ∈ Finset.Icc 2 N, x + 1 = ∑ x ∈ Finset.Icc 1 N, x := by
      rw [← he, Finset.sum_erase_add _ _ h1]
    rw [he]
    have hb := Icc_eq_block_map (a := 2) (n := N - 1) (by omega)
    rw [show 2 + (N - 1) - 1 = N by omega] at hb
    rw [hb]
    refine h (N - 1) 2 1 (by omega) (by omega) (by omega) (by omega) ?_
    rw [← hb]
    omega

end CatchUp
