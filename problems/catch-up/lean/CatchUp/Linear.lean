module

public import CatchUp.Blocks
public import CatchUp.Matching
public import CatchUp.Transfer

/-!
# High blocks at linear height

Blueprint L21 for blocks, with AM+T in place of always-max. Z plays AM+T until the opponent, at a
round start, trails by more than the matching cost of the numbers left (L20); from then on Z
answers with matching partners. Before the switch L23's classes hold; after it the opponent stays
behind by more than the matching cost, with debt plus cost never growing. So every round start has
debt at most `3(2p - 1)` (`HZ`, `HY`), and L22 (`valueAux_transfer`) carries the guarantee to the
real game once `a > 3(2p - 1)` (`block_draw_linear`).
-/

@[expose] public section

namespace CatchUp

/-- The matching cost is at most the span. -/
theorem matchCost_le_span (n : ℕ) : ∀ T : Finset ℕ, T.card = n → ∀ L M : ℕ,
    (∀ x ∈ T, L ≤ x ∧ x ≤ M) → L ≤ M → matchCost T ≤ (M : ℤ) - L := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn L M hT hLM
  rw [matchCost]
  split_ifs with h h'
  · have ha := Finset.min'_mem T h
    have hb := Finset.min'_mem _ h'
    have hbT := Finset.mem_of_mem_erase hb
    have hlt : ((T.erase (T.min' h)).erase ((T.erase (T.min' h)).min' h')).card < n :=
      hn ▸ lt_of_lt_of_le (Finset.card_erase_lt_of_mem hb) Finset.card_erase_le
    have hIH := ih _ hlt _ rfl ((T.erase (T.min' h)).min' h') M (fun x hx => ⟨Finset.min'_le _ _
      (Finset.mem_of_mem_erase hx), (hT x (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hx))).2⟩) (hT _ hbT).2
    have h1 := (hT _ ha).1
    linarith
  · omega
  · omega

theorem matchCost_le_range {p : ℕ} (hp : 1 ≤ p) {T : Finset ℕ} (hT : T ⊆ Finset.range (2 * p)) :
    matchCost T ≤ 2 * p - 1 := by
  have := matchCost_le_span _ T rfl 0 (2 * p - 1) (fun x hx => ⟨Nat.zero_le _, by
    have := Finset.mem_range.mp (hT hx); omega⟩) (Nat.zero_le _)
  omega

/-- Z's round starts: Z moves trailing by `d`. -/
def HZ (p : ℕ) (T : Finset ℕ) (d : ℕ) : Prop :=
  T ⊆ Finset.range (2 * p) ∧ Even T.card ∧ (d + ∑ o ∈ T, o) % 2 = 0 ∧ KZc T d ∧ d ≤ 2 * p - 1

/-- The opponent's round starts: before the switch (L23's class), or after it. -/
def HY (p : ℕ) (T : Finset ℕ) (e : ℕ) : Prop :=
  T ⊆ Finset.range (2 * p) ∧ Even T.card ∧ (e + ∑ o ∈ T, o) % 2 = 0 ∧
    (((e : ℤ) ≤ matchCost T ∧ KYc T e ∧ e ≤ 2 * (2 * p - 1)) ∨
      (matchCost T < e ∧ (e : ℤ) + matchCost T ≤ 3 * (2 * p - 1)))

private theorem round_facts {T : Finset ℕ} (hev : Even T.card) {a b : ℕ} (ha : a ∈ T)
    (hb : b ∈ T.erase a) :
    ((T.erase a).erase b).card < T.card ∧ Even ((T.erase a).erase b).card ∧
      ∑ o ∈ (T.erase a).erase b, o + b + a = ∑ o ∈ T, o ∧
      (T.erase a).erase b ⊆ T := by
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb
  have hs1 := Finset.sum_erase_add T (fun o => o) ha
  have hs2 := Finset.sum_erase_add (T.erase a) (fun o => o) hb
  obtain ⟨k, hk⟩ := hev
  refine ⟨by omega, ⟨k - 1, by omega⟩, by omega, fun x hx =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩

theorem hz_step {p : ℕ} {T : Finset ℕ} {d : ℕ} (hK : HZ p T d) (h : T.Nonempty) :
    ∀ j ∈ T.erase (T.max' h),
      (T.max' h ≤ d + j → HZ p ((T.erase (T.max' h)).erase j) (d + j - T.max' h)) ∧
      (¬ T.max' h ≤ d + j → HY p ((T.erase (T.max' h)).erase j) (T.max' h - d - j)) := by
  intro j hj
  obtain ⟨hsub, hev, hpar, hKZ, hd⟩ := hK
  obtain ⟨-, hev2, hsum, hsub2⟩ := round_facts hev (Finset.max'_mem T h) hj
  obtain ⟨hc1, hc2⟩ := closeZ hev h hKZ hj
  have ht1 := Finset.mem_range.mp (hsub (Finset.max'_mem T h))
  have hjlt : j < T.max' h := lt_of_le_of_ne (Finset.le_max' T j (Finset.mem_of_mem_erase hj))
    (Finset.ne_of_mem_erase hj)
  have hsubR := hsub2.trans hsub
  have hcost := matchCost_le_range (by omega) hsubR
  have hcost0 := matchCost_nonneg _ ((T.erase (T.max' h)).erase j) rfl
  refine ⟨fun hc => ⟨hsubR, hev2, by omega, hc1 hc, by omega⟩,
    fun hc => ⟨hsubR, hev2, by omega, ?_⟩⟩
  by_cases hle : ((T.max' h - d - j : ℕ) : ℤ) ≤ matchCost ((T.erase (T.max' h)).erase j)
  · exact Or.inl ⟨hle, hc2 hc, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

theorem hy_step {p : ℕ} {T : Finset ℕ} {e : ℕ} (hK : HY p T e) :
    ∀ i ∈ T, ∃ j ∈ T.erase i,
      (i ≤ e + j → HY p ((T.erase i).erase j) (e + j - i)) ∧
      (¬ i ≤ e + j → HZ p ((T.erase i).erase j) (i - e - j)) := by
  intro i hi
  obtain ⟨hsub, hev, hpar, hcase⟩ := hK
  have hiR := Finset.mem_range.mp (hsub hi)
  rcases hcase with ⟨hle, hKY, he⟩ | ⟨hlt, he⟩
  · -- Before the switch: AM+T's answer.
    have hj := amtReply_mem (erase_nonempty_of_even hev hi) e i
    refine ⟨amtReply (T.erase i) e i, hj, ?_⟩
    obtain ⟨-, hev2, hsum, hsub2⟩ := round_facts hev hi hj
    obtain ⟨hc1, hc2⟩ := closeY hev hKY hi
    have hjR := Finset.mem_range.mp (hsub (Finset.mem_of_mem_erase hj))
    have hsubR := hsub2.trans hsub
    have hcost := matchCost_le_range (by omega) hsubR
    have hcostT := matchCost_le_range (by omega) hsub
    have hcost0 := matchCost_nonneg _ ((T.erase i).erase (amtReply (T.erase i) e i)) rfl
    refine ⟨fun hc => ⟨hsubR, hev2, by omega, ?_⟩, fun hc => ⟨hsubR, hev2, by omega, hc2 hc,
      by omega⟩⟩
    by_cases hle' : ((e + amtReply (T.erase i) e i - i : ℕ) : ℤ) ≤
        matchCost ((T.erase i).erase (amtReply (T.erase i) e i))
    · exact Or.inl ⟨hle', hc1 hc, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · -- After the switch: the matching partner.
    obtain ⟨j, hj, hjc⟩ := exists_partner T.card T rfl hev i hi
    refine ⟨j, hj, ?_⟩
    obtain ⟨-, hev2, hsum, hsub2⟩ := round_facts hev hi hj
    have hcost0 := matchCost_nonneg _ ((T.erase i).erase j) rfl
    have habs1 := le_abs_self ((i : ℤ) - j)
    have habs2 := neg_abs_le ((i : ℤ) - j)
    have hc : i ≤ e + j := by
      have : (i : ℤ) < e + j := by linarith
      omega
    refine ⟨fun _ => ⟨hsub2.trans hsub, hev2, by omega, Or.inr ⟨?_, ?_⟩⟩, fun h => absurd hc h⟩
    · push_cast [hc]; linarith
    · push_cast [hc]; linarith

/-- **L21 for blocks, Lean form.** The block `{a, …, a + 2p - 1}` with `a > 3(2p - 1)` is a draw
for the player to move trailing by `p mod 2`. -/
theorem block_draw_linear {p a : ℕ} (hp : 1 ≤ p) (ha : 3 * (2 * p - 1) < a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw := by
  have hT := valueAux_transfer a (HZ p) (HY p)
    (fun T d hK o ho => by
      have := Finset.mem_range.mp (hK.1 ho); have := hK.2.2.2.2; omega)
    (fun T e hK o ho => by
      have := Finset.mem_range.mp (hK.1 ho)
      rcases hK.2.2.2 with ⟨-, -, he⟩ | ⟨-, he⟩
      · omega
      · have := matchCost_nonneg _ T rfl; omega)
    (fun d hK => by
      have h1 := hK.2.2.2.1.1 (by simp)
      have h2 := hK.2.2.1
      simp at h2
      omega)
    (fun T d hK h => ⟨T.max' h, Finset.max'_mem T h, hz_step hK h⟩)
    (fun T e hK => hy_step hK)
    (2 * p) (Finset.range (2 * p)) (Finset.card_range _)
  have hev : Even (Finset.range (2 * p)).card := by rw [Finset.card_range]; exact even_two_mul p
  have hpar : (p % 2 + ∑ o ∈ Finset.range (2 * p), o) % 2 = 0 := by
    rw [sum_range_two_mul, Nat.add_mod, Nat.mul_mod]
    have : (2 * p - 1) % 2 = 1 := by omega
    rw [this, mul_one, Nat.mod_mod]
    omega
  have hcost : 1 ≤ matchCost (Finset.range (2 * p)) := by
    have h0 : 0 ∈ Finset.range (2 * p) := Finset.mem_range.mpr (by omega)
    have h1 : 1 ∈ Finset.range (2 * p) := Finset.mem_range.mpr (by omega)
    rw [matchCost_of_min h0 h1 (by norm_num) (fun x _ => by omega)]
    have := matchCost_nonneg _ (((Finset.range (2 * p)).erase 0).erase 1) rfl
    push_cast
    linarith
  have hZ := hT.1 (p % 2) ⟨subset_refl _, hev, hpar, kzc_range hp (by omega), by omega⟩ s
  have hY := hT.2 (p % 2) ⟨subset_refl _, hev, hpar, Or.inl ⟨by push_cast; omega,
    kyc_range p (p % 2), by omega⟩⟩ s
  revert hZ hY
  cases valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false <;> simp

end CatchUp
