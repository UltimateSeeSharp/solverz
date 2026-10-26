module

public import CatchUp.Depth
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# High blocks draw

Blueprint L16 for blocks, through L23: the rounds game on `{0..2p-1}` at debt `p mod 2` is a draw
(`roundsValue_range_draw`), so by L13 the block `{a, …, a + 2p - 1}` with `a > p mod 2 + p(2p-1)` is
a draw for the player to move trailing by `p mod 2` (`block_draw_high`).
-/

@[expose] public section

namespace CatchUp

theorem sum_range_two_mul (p : ℕ) : ∑ o ∈ Finset.range (2 * p), o = p * (2 * p - 1) := by
  have h := Finset.sum_range_id_mul_two (2 * p)
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
  rw [h]
  ring

/-- The rounds game on `{0..2p-1}` at debt `p mod 2` is a draw: both players' AM+T guarantees
(L23) and parity. -/
theorem roundsValue_range_draw {p : ℕ} (hp : 1 ≤ p) :
    roundsValue (Finset.range (2 * p)) (p % 2) = .draw := by
  have hc : (Finset.range (2 * p)).card = 2 * p := Finset.card_range _
  have hev : Even (2 * p) := even_two_mul p
  obtain ⟨hZ, hY⟩ := depth_class_roundsMargin (2 * p) _ hc hev
  have h1 := hZ (p % 2) (kzc_range hp (d := p % 2) (by omega))
  have h2 := hY (p % 2) (kyc_range p (p % 2))
  have hpar := even_roundsMargin_add (2 * p) _ hc hev (p % 2)
  rw [← Nat.cast_sum, Int.even_iff] at hpar
  have hS2 : (∑ o ∈ Finset.range (2 * p), o) % 2 = p % 2 := by
    rw [sum_range_two_mul, Nat.mul_mod]
    have : (2 * p - 1) % 2 = 1 := by omega
    rw [this, mul_one, Nat.mod_mod]
  rw [roundsValue_eq_ofMargin (2 * p) _ hc hev]
  generalize ∑ o ∈ Finset.range (2 * p), o = S at hpar hS2
  generalize roundsMargin (Finset.range (2 * p)) (p % 2) = M at hpar h1 h2 ⊢
  have h0 : M = 0 := by omega
  rw [h0]
  simp [Outcome.ofMargin]

/-- **L16 for blocks, via L23.** The block `{a, …, a + 2p - 1}` placed above
`p mod 2 + p(2p-1)` is a draw for the player to move trailing by `p mod 2`. -/
theorem block_draw_high {p a : ℕ} (hp : 1 ≤ p) (ha : p % 2 + p * (2 * p - 1) < a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw := by
  have hev : Even (Finset.range (2 * p)).card := by rw [Finset.card_range]; exact even_two_mul p
  rw [valueAux_map_add _ hev a (p % 2) (by rw [sum_range_two_mul]; exact ha) s]
  exact roundsValue_range_draw hp

end CatchUp
