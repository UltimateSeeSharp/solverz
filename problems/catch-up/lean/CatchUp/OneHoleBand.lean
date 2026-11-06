module

public import CatchUp.OneHoleRounds
public import CatchUp.Small

/-!
# The one-hole band gives the conjecture

C110: odd blocks `{a..a + 2k}` without one number draw at every deficit `d ≤ k - 1` of the draw
parity. Its entry `a = 1` with the hole at the top is `{1..N}` at a tie (`N = 2k ≡ 0 mod 4`), and
with the hole at the bottom `{2..N}` trailing by 1 (`N = 2k + 1 ≡ 3 mod 4`), C27's two families;
so C110 for `k ≥ 3` gives C1 for `N ≥ 13`, and `conjecture_le_twelve` the rest. By C13 it is
enough to know C110 at the heights `a ≤ k(2k + 1) + k` (`oneHoleBand_of_bounded_heights`).
-/

@[expose] public section

namespace CatchUp

/-- C110, the one-hole band (I24), at base score 0. -/
def OneHoleBandConjecture : Prop :=
  ∀ k a o d : ℕ, 3 ≤ k → 1 ≤ a → o ≤ 2 * k → d + 1 ≤ k → (d + ∑ x ∈ oneHole k o, x) % 2 = 0 →
    valueAux ((oneHole k o).map (addLeftEmbedding a)) 0 d false = .draw

/-- `{1..2k}` is the odd block `{1..2k+1}` without its top. -/
theorem Icc_one_eq_oneHole_top (k : ℕ) :
    Finset.Icc 1 (2 * k) = (oneHole k (2 * k)).map (addLeftEmbedding 1) := by
  ext y
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_erase, Finset.mem_range,
    addLeftEmbedding_apply]
  constructor
  · intro hy
    exact ⟨y - 1, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    omega

/-- `{2..2k+1}` is the odd block `{1..2k+1}` without its bottom. -/
theorem Icc_two_eq_oneHole_bottom (k : ℕ) :
    Finset.Icc 2 (2 * k + 1) = (oneHole k 0).map (addLeftEmbedding 1) := by
  ext y
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_erase, Finset.mem_range,
    addLeftEmbedding_apply]
  constructor
  · intro hy
    exact ⟨y - 1, ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    omega

/-- **I24's reduction**: the one-hole band (C110) gives the conjecture. -/
theorem conjecture_of_one_hole_band (h : OneHoleBandConjecture) : Goal := by
  intro N hN
  by_cases h12 : N ≤ 12
  · exact conjecture_le_twelve N h12 hN
  rw [value, valueAux_true_eq_false]
  rcases (even_triangle_iff N).1 hN with h4 | h4
  · -- `N = 2k`, the hole at the top, a tie.
    have hS := sum_oneHole (k := N / 2) (o := 2 * (N / 2)) le_rfl
    have hb := Icc_one_eq_oneHole_top (N / 2)
    rw [show 2 * (N / 2) = N by omega] at hb hS
    rw [hb]
    refine h (N / 2) 1 N 0 (by omega) le_rfl (by omega) (by omega) ?_
    have hk : (N / 2 * (2 * (N / 2) + 1)) % 2 = 0 := by
      rw [Nat.mul_mod]
      have : N / 2 % 2 = 0 := by omega
      rw [this, zero_mul, Nat.zero_mod]
    rw [show 2 * (N / 2) = N by omega] at hk
    omega
  · -- `N = 2k + 1`, the token `1` (C26), then the hole at the bottom at deficit 1.
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    refine token_lemma h1 (fun x hx => (Finset.mem_Icc.mp hx).1) ?_
    have he : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [he]
    have hb := Icc_two_eq_oneHole_bottom ((N - 1) / 2)
    rw [show 2 * ((N - 1) / 2) + 1 = N by omega] at hb
    rw [hb]
    have hS := sum_oneHole (k := (N - 1) / 2) (o := 0) (Nat.zero_le _)
    refine h ((N - 1) / 2) 1 0 1 (by omega) le_rfl (Nat.zero_le _) (by omega) ?_
    have hk : ((N - 1) / 2 * (2 * ((N - 1) / 2) + 1)) % 2 = 1 := by
      rw [Nat.mul_mod]
      have : (N - 1) / 2 % 2 = 1 := by omega
      have h2 : (2 * ((N - 1) / 2) + 1) % 2 = 1 := by omega
      rw [this, h2]
    omega

/-- **C110 from bounded heights** (C13): above `a > d + Σ offsets` the value no longer depends on
`a` (`valueAux_map_add`), so C110 at the heights `a ≤ k(2k + 1) + k` gives it at every height. -/
theorem oneHoleBand_of_bounded_heights
    (h : ∀ k a o d : ℕ, 3 ≤ k → 1 ≤ a → a ≤ k * (2 * k + 1) + k → o ≤ 2 * k → d + 1 ≤ k →
      (d + ∑ x ∈ oneHole k o, x) % 2 = 0 →
      valueAux ((oneHole k o).map (addLeftEmbedding a)) 0 d false = .draw) :
    OneHoleBandConjecture := by
  intro k a o d hk ha ho hd hpar
  by_cases hlow : a ≤ k * (2 * k + 1) + k
  · exact h k a o d hk ha hlow ho hd hpar
  have hS := sum_oneHole (k := k) (o := o) ho
  have hev : Even (oneHole k o).card := ⟨k, by rw [card_oneHole ho]; omega⟩
  have h1 := valueAux_map_add (oneHole k o) hev a d (by omega) 0
  have h2 := valueAux_map_add (oneHole k o) hev (k * (2 * k + 1) + k) d (by omega) 0
  rw [Nat.zero_add] at h1 h2
  rw [h1, ← h2]
  exact h k _ o d hk (by omega) le_rfl ho hd hpar

end CatchUp
