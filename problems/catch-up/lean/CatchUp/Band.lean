module

public import CatchUp.Hyb2
public import CatchUp.Executable

/-!
# The draw band of blocks at every height, small blocks

Claim C86 for `p ≤ 4`: the block `{a..a+2p-1}` with the mover trailing by any `d ≤ p` of the
parity of `p` is a draw at every height `a ≥ 1`, except `{2, 3, 4, 5}` at deficit 2, a mover win
(`band_exception`). From `a ≥ 2p - 1` it is `block_row_draw_hyb2` (C24); below, the 29 remaining
positions are evaluated by the verified evaluator (`band_draw_le_four`). Corollary: a block with
one small number `d < a` of the band added draws at a tie (`block_add_small_draw_le_four`).
The whole claim, `BandConjecture`, implies the conjecture (`conjecture_of_band`, via C27).
-/

@[expose] public section

namespace CatchUp

/-- Any ordinary-turn position is the verified evaluator's normalized position. -/
theorem valueAux_eq_eval (R : Finset ℕ) (s d : ℕ) :
    valueAux R s (s + d) false = Position.eval ⟨R, d⟩ := by
  rw [← Position.eval_eq_value_aux R s (s + d) (by omega), Nat.add_sub_cancel_left]

/-- C47's exception: `{2, 3, 4, 5}` at deficit 2 is a mover win. -/
theorem band_exception (s : ℕ) :
    valueAux ((Finset.range (2 * 2)).map (addLeftEmbedding 2)) s (s + 2) false = .win := by
  rw [valueAux_eq_eval]
  decide +kernel

/-- **C86 for `p ≤ 4`**: blocks draw on the whole band at every height, but for `(2, 2, 2)`. -/
theorem band_draw_le_four {p a d : ℕ} (hp1 : 1 ≤ p) (hp4 : p ≤ 4) (ha : 1 ≤ a) (hd : d ≤ p)
    (hdp : d % 2 = p % 2) (hex : ¬(p = 2 ∧ a = 2 ∧ d = 2)) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + d) false = .draw := by
  by_cases hhigh : 2 * p - 1 ≤ a
  · exact block_row_draw_hyb2 hp1 hhigh hd hdp s
  · rw [valueAux_eq_eval]
    have hcases : (p = 2 ∧ a = 1 ∧ (d = 0 ∨ d = 2)) ∨ (p = 2 ∧ a = 2 ∧ d = 0) ∨
        (p = 3 ∧ (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) ∧ (d = 1 ∨ d = 3)) ∨
        (p = 4 ∧ (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) ∧ (d = 0 ∨ d = 2 ∨ d = 4)) := by
      omega
    rcases hcases with ⟨rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl | rfl | rfl | rfl, rfl | rfl⟩ |
      ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl, rfl | rfl | rfl⟩ <;> decide +kernel

/-- C86's corollary for `p ≤ 4`: a block with one small number `d < a` of the band added draws at
a tie (opening `d` reaches the band entry; the level law, C28). -/
theorem block_add_small_draw_le_four {p a d : ℕ} (hp1 : 1 ≤ p) (hp4 : p ≤ 4) (hda : d < a)
    (hd : d ≤ p) (hdp : d % 2 = p % 2) (s : ℕ) :
    valueAux (insert d ((Finset.range (2 * p)).map (addLeftEmbedding a))) s s false = .draw := by
  have hnot : d ∉ (Finset.range (2 * p)).map (addLeftEmbedding a) := by
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply, not_exists, not_and]
    intro x _ hx
    omega
  apply level_law (t := d) (Finset.mem_insert_self d _)
  rw [Finset.erase_insert hnot]
  exact band_draw_le_four hp1 hp4 (by omega) hd hdp (by omega) s

/-- C86, the draw band of blocks at every height (I17's root claim), at base score 0. -/
def BandConjecture : Prop :=
  ∀ p a d : ℕ, 1 ≤ p → 1 ≤ a → d ≤ p → d % 2 = p % 2 → ¬(p = 2 ∧ a = 2 ∧ d = 2) →
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) 0 d false = .draw

/-- An interval `{a..a + 2p - 1}` is the block of `2p` offsets at height `a`. -/
private theorem Icc_eq_block {a p : ℕ} (hp : 1 ≤ p) :
    Finset.Icc a (a + 2 * p - 1) = (Finset.range (2 * p)).map (addLeftEmbedding a) := by
  ext y
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
  constructor
  · intro hy
    exact ⟨y - a, by omega, by omega⟩
  · rintro ⟨x, hx, rfl⟩
    omega

/-- **I17's reduction**: the band at heights 1 and 2 (C27's two families) gives the conjecture. -/
theorem conjecture_of_band (h : BandConjecture) : Conjecture := by
  apply conjecture_of_two_families
  · intro N hN
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · rw [valueAux]
      simp
    · have hb := Icc_eq_block (a := 1) (p := N / 2) (by omega)
      rw [show 1 + 2 * (N / 2) - 1 = N by omega] at hb
      rw [hb]
      exact h (N / 2) 1 0 (by omega) le_rfl (Nat.zero_le _) (by omega) (by omega)
  · intro N hN
    have hb := Icc_eq_block (a := 2) (p := (N - 1) / 2) (by omega)
    rw [show 2 + 2 * ((N - 1) / 2) - 1 = N by omega] at hb
    rw [hb]
    exact h ((N - 1) / 2) 2 1 (by omega) (by omega) (by omega) (by omega) (by omega)

end CatchUp
