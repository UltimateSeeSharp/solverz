module

public import CatchUp.GameMargin

/-!
# Controller games

C111: in the controller game one player, the controller, decides at every exact catch-up (a mover
strictly behind whose pick brings it level) whether the turn ends, as in Catch-Up, or the mover
takes one more number and then leads. `ctlMargin R a b c` is its minimax margin with `R` left, the
mover holding `a` and the opponent `b`, `c` saying whether the mover is the controller. The
controller can always choose the real rule, so Catch-Up's margin lies between the two controller
games (`ctlMargin_sandwich`), and if neither controller wins on `{1..N}`, Catch-Up draws there
(`conjecture_of_controller_games`, C111 with C112 as its hypothesis).
-/

@[expose] public section

namespace CatchUp

/-- The controller game's minimax margin (C111); `c`: the mover is the controller. -/
noncomputable def ctlMargin (R : Finset ℕ) (a b : ℕ) (c : Bool) : ℤ :=
  if h : R.Nonempty then
    R.attach.sup' (by simpa using h) fun x =>
      if a < b ∧ a + x.1 = b then
        (if c then max else min) (-ctlMargin (R.erase x.1) b (a + x.1) (!c))
          (if h' : (R.erase x.1).Nonempty then
            (R.erase x.1).attach.sup' (by simpa using h') fun y =>
              -ctlMargin ((R.erase x.1).erase y.1) b (a + x.1 + y.1) (!c)
          else 0)
      else if b ≤ a + x.1 then -ctlMargin (R.erase x.1) b (a + x.1) (!c)
      else ctlMargin (R.erase x.1) (a + x.1) b c
  else (a : ℤ) - b
termination_by R.card
decreasing_by
  · exact Finset.card_erase_lt_of_mem x.2
  · exact lt_trans (Finset.card_erase_lt_of_mem y.2) (Finset.card_erase_lt_of_mem x.2)
  · exact Finset.card_erase_lt_of_mem x.2
  · exact Finset.card_erase_lt_of_mem x.2

/-- **C111**: Catch-Up's margin lies between the controller game where the opponent controls and
the one where the mover controls. -/
theorem ctlMargin_sandwich (n : ℕ) : ∀ (R : Finset ℕ), R.card = n → ∀ a b : ℕ,
    ctlMargin R a b false ≤ margin R a b ∧ margin R a b ≤ ctlMargin R a b true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn a b
  subst hn
  by_cases h : R.Nonempty
  · rw [ctlMargin, dite_eq_left h, ctlMargin, dite_eq_left h, margin, dite_eq_left h]
    have key : ∀ x (hx : x ∈ R),
        ((if a < b ∧ a + x = b then
            min (-ctlMargin (R.erase x) b (a + x) true)
              (if h' : (R.erase x).Nonempty then
                (R.erase x).attach.sup' (by simpa using h') fun y =>
                  -ctlMargin ((R.erase x).erase y.1) b (a + x + y.1) true
              else 0)
          else if b ≤ a + x then -ctlMargin (R.erase x) b (a + x) true
          else ctlMargin (R.erase x) (a + x) b false) ≤
          (if b ≤ a + x then -margin (R.erase x) b (a + x)
            else margin (R.erase x) (a + x) b)) ∧
        ((if b ≤ a + x then -margin (R.erase x) b (a + x)
            else margin (R.erase x) (a + x) b) ≤
          (if a < b ∧ a + x = b then
            max (-ctlMargin (R.erase x) b (a + x) false)
              (if h' : (R.erase x).Nonempty then
                (R.erase x).attach.sup' (by simpa using h') fun y =>
                  -ctlMargin ((R.erase x).erase y.1) b (a + x + y.1) false
              else 0)
          else if b ≤ a + x then -ctlMargin (R.erase x) b (a + x) false
          else ctlMargin (R.erase x) (a + x) b true)) := by
      intro x hx
      have hlt : (R.erase x).card < R.card := Finset.card_erase_lt_of_mem hx
      by_cases hc : b ≤ a + x
      · obtain ⟨h1, h2⟩ := ih _ hlt (R.erase x) rfl b (a + x)
        constructor
        · split_ifs <;> first
            | linarith
            | exact le_trans (min_le_left _ _) (by linarith)
        · split_ifs <;> first
            | linarith
            | exact le_trans (by linarith) (le_max_left _ _)
      · obtain ⟨h1, h2⟩ := ih _ hlt (R.erase x) rfl (a + x) b
        constructor
        · split_ifs <;> first
            | (exfalso; omega)
            | linarith
        · split_ifs <;> first
            | (exfalso; omega)
            | linarith
    constructor
    · refine Finset.sup'_le _ _ fun x _ => ?_
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach R x))
      simpa using (key x.1 x.2).1
    · refine Finset.sup'_le _ _ fun x _ => ?_
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach R x))
      simpa using (key x.1 x.2).2
  · have h0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst h0
    rw [ctlMargin, dite_eq_right Finset.not_nonempty_empty, ctlMargin,
      dite_eq_right Finset.not_nonempty_empty, margin, dite_eq_right Finset.not_nonempty_empty]
    exact ⟨le_rfl, le_rfl⟩

/-- **I25's reduction** (C111): if on every `{1..N}` with an even total neither controller wins
(C112: player 1 does not win when it controls, player 2 does not win when it controls), the
conjecture holds. -/
theorem conjecture_of_controller_games
    (h : ∀ N : ℕ, Even (N * (N + 1) / 2) →
      ctlMargin (Finset.Icc 1 N) 0 0 true ≤ 0 ∧ 0 ≤ ctlMargin (Finset.Icc 1 N) 0 0 false) :
    Conjecture := by
  apply conjecture_of_margin_le_one
  intro N hN
  obtain ⟨h1, h2⟩ := h N hN
  obtain ⟨s1, s2⟩ := ctlMargin_sandwich _ (Finset.Icc 1 N) rfl 0 0
  rw [abs_le]
  constructor <;> linarith

end CatchUp
