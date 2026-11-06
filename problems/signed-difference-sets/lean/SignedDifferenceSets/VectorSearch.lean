module

public import SignedDifferenceSets.Loops

/-!
# Searching integer vectors (contraction, C3)

`noVector n add c Q t k s` searches every integer vector `w` of length `n` with `|wᵢ| ≤ c`,
`|w₀|` the largest, `Σ w = s`, `Σ w² = Q`, `Σ |w| ≤ k` with `k − Σ |w|` even, and
`Σᵢ wᵢ · w_{add i g} = t` for every shift `0 < g < n` (`add`: addition on the element
numbers). It is `true` when there is none (`noVector_sound`). It visits the same nodes as
the solver's `contraction::search`: coordinates in order, cut when the rest cannot reach
`Q` and `s`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- Every shift `0 < g < n` of `w` has correlation `t`. -/
def shiftsOK (n : ℕ) (add : ℕ → ℕ → ℕ) (t : ℤ) (w : List ℤ) : Bool :=
  allTo (fun g => g == 0 || sumTo (fun x => w.getD x 0 * w.getD (add x g) 0) n == t) n

/-- A complete vector `w` with sums `sum`, `sq`, `abs` meets the demands. -/
def leafOK (n : ℕ) (add : ℕ → ℕ → ℕ) (Q t k s : ℤ) (w : List ℤ) (sum sq abs : ℤ) : Bool :=
  sum == s && sq == Q && decide (abs ≤ k) && (k - abs) % 2 == 0 && shiftsOK n add t w

/-- `rem` more coordinates in `[−c, c]` cannot bring the sums `sum`, `sq` to `s`, `Q`. -/
def cut (c Q s : ℤ) (rem : ℕ) (sum sq : ℤ) : Bool :=
  decide (Q - sq < 0) || decide ((rem : ℤ) * (Q - sq) < (s - sum) * (s - sum)) ||
    decide ((rem : ℤ) * c < |s - sum|)

/-- No completion of the reversed prefix `pre` by `rem` coordinates in `[−top, top]` meets the
demands; `sum`, `sq`, `abs` are the prefix's `Σ w`, `Σ w²`, `Σ |w|`. -/
def go (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs => !leafOK n add Q t k s pre.reverse sum sq abs
  | rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        go n add c Q t k s top rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

/-- No vector meets the demands; the first coordinate, in `[−c, c]`, bounds the others. -/
def noVector (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) : Bool :=
  cut c Q s n 0 0 ||
    allRange (fun x => decide (Q < x * x) ||
      go n add c Q t k s |x| (n - 1) [x] x (x * x) |x|) (-c) (2 * c + 1).toNat

/-- The sum of squares of a list. -/
abbrev sqSum (w : List ℤ) : ℤ := (w.map fun y => y * y).sum

/-- The sum of absolute values of a list. -/
abbrev absSum (w : List ℤ) : ℤ := (w.map fun y => |y|).sum

theorem sqSum_nonneg (w : List ℤ) : 0 ≤ sqSum w := by
  induction w with
  | nil => simp [sqSum]
  | cons y w ih => simp only [sqSum, List.map_cons, List.sum_cons] at ih ⊢; nlinarith

theorem sum_mul_sum_le (w : List ℤ) : w.sum * w.sum ≤ w.length * sqSum w := by
  have h := Multiset.sq_sum_le_card_mul_sum_sq (w : Multiset ℤ)
  simp only [Multiset.sum_coe, Multiset.coe_card, Multiset.map_coe, sq] at h
  exact h

theorem abs_sum_le (w : List ℤ) {c : ℤ} (hc : ∀ y ∈ w, |y| ≤ c) :
    |w.sum| ≤ w.length * c := by
  induction w with
  | nil => simp
  | cons y w ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hc
    simp only [List.sum_cons, List.length_cons]
    push_cast
    have := ih hc.2
    calc |y + w.sum| ≤ |y| + |w.sum| := abs_add_le _ _
      _ ≤ c + w.length * c := add_le_add hc.1 this
      _ = (w.length + 1) * c := by ring

/-- `cut` never fires above a vector that meets the demands. -/
theorem cut_false {c Q s sum sq : ℤ} (w : List ℤ) (hc : ∀ y ∈ w, |y| ≤ c)
    (hs : sum + w.sum = s) (hq : sq + sqSum w = Q) : cut c Q s w.length sum sq = false := by
  have h1 := sqSum_nonneg w
  have h2 := sum_mul_sum_le w
  have h3 := abs_sum_le w hc
  have e1 : s - sum = w.sum := by linarith
  have e2 : Q - sq = sqSum w := by linarith
  simp only [cut, e1, e2, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact ⟨⟨h1, by linarith⟩, h3⟩

theorem go_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} :
    ∀ (w pre : List ℤ) (sum sq abs : ℤ),
      go n add c Q t k s top w.length pre sum sq abs = true →
      (∀ y ∈ w, |y| ≤ top) → (∀ y ∈ w, |y| ≤ c) →
      sum + w.sum = s → sq + sqSum w = Q → abs + absSum w ≤ k →
      (k - (abs + absSum w)) % 2 = 0 → shiftsOK n add t (pre.reverse ++ w) = true → False
  | [], pre, sum, sq, abs, h, _, _, hs, hq, ha, hp, hw => by
    simp only [List.sum_nil, add_zero, sqSum, absSum, List.map_nil, List.append_nil] at *
    simp [go, leafOK, hs, hq, ha, hp, hw] at h
  | x :: w, pre, sum, sq, abs, h, ht, hc, hs, hq, ha, hp, hw => by
    have hcut := cut_false (x :: w) hc hs hq
    simp only [List.length_cons, go] at h
    rw [List.length_cons] at hcut
    rw [hcut, Bool.false_or] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ht hc
    have hx := allRange_abs h ht.1
    simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
    have hsq : ¬ Q - sq < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
    simp only [hsq, decide_false, Bool.false_or] at hx
    exact go_sound w (x :: pre) (sum + x) (sq + x * x) (abs + |x|) hx ht.2 hc.2
      (by linarith) (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
      (by simp only [absSum]; rw [show abs + |x| + absSum w = abs + (|x| + absSum w) by ring]
          exact hp)
      (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hw)

/-- `noVector` is `true` only if no vector meets the demands. -/
theorem noVector_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ}
    (h : noVector n add c Q t k s = true) (x : ℤ) (w : List ℤ) (hn : (x :: w).length = n)
    (hx : |x| ≤ c) (htop : ∀ y ∈ w, |y| ≤ |x|) (hc : ∀ y ∈ w, |y| ≤ c)
    (hs : (x :: w).sum = s) (hq : sqSum (x :: w) = Q) (ha : absSum (x :: w) ≤ k)
    (hp : (k - absSum (x :: w)) % 2 = 0) (hw : shiftsOK n add t (x :: w) = true) : False := by
  have hcall : ∀ y ∈ x :: w, |y| ≤ c := by
    simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, hc⟩
  have hcut := cut_false (sum := 0) (sq := 0) (x :: w) hcall (by simpa using hs)
    (by simpa using hq)
  rw [hn] at hcut
  rw [noVector, hcut, Bool.false_or] at h
  have hr := allRange_abs h hx
  simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
  have hsq : ¬ Q < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
  simp only [hsq, decide_false, Bool.false_or] at hr
  have hlen : n - 1 = w.length := by simp at hn; omega
  rw [hlen] at hr
  exact go_sound w [x] x (x * x) |x| hr htop hc (by linarith) (by simp only [sqSum]; linarith)
    (by simp only [absSum]; linarith) (by simp only [absSum]; exact hp)
    (by simpa using hw)

/-! ### Splitting the search into separate kernel checks

The kernel keeps every reduction of one declaration in memory, about 0.1 MB per node of
the search. `noVectorTop` runs only the top levels and leaves each node at depth `d + 1`,
prefix `p`, to its own declaration `below … p = true`; `noVector_of_top` joins them. -/

/-- The search below the prefix `p` (coordinates in order; `|p₀|` bounds the rest). -/
def below (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (p : List ℤ) : Bool :=
  go n add c Q t k s |p.headD 0| (n - p.length) p.reverse p.sum (sqSum p) (absSum p)

/-- `go`'s top `d` levels; a node `d` levels down, reversed prefix `pre`, is left to `P`. -/
def goTop (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) (P : List (List ℤ)) :
    ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, _, pre, _, _, _ => P.contains pre.reverse
  | _ + 1, 0, pre, sum, sq, abs => !leafOK n add Q t k s pre.reverse sum sq abs
  | d + 1, rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        goTop n add c Q t k s top P d rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

/-- `noVector` with each node `d + 1` levels down left to `P`. -/
def noVectorTop (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (P : List (List ℤ)) (d : ℕ) :
    Bool :=
  cut c Q s n 0 0 ||
    allRange (fun x => decide (Q < x * x) ||
      goTop n add c Q t k s |x| P d (n - 1) [x] x (x * x) |x|) (-c) (2 * c + 1).toNat

theorem headD_reverse_cons {x : ℤ} {pre : List ℤ} (h : pre ≠ []) :
    (x :: pre).reverse.headD 0 = pre.reverse.headD 0 := by
  obtain ⟨y, l, hl⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 h)
  rw [List.reverse_cons, hl]
  rfl

theorem go_of_goTop {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {P : List (List ℤ)}
    (hP : ∀ p ∈ P, below n add c Q t k s p = true) :
    ∀ (d rem : ℕ) (pre : List ℤ) (sum sq abs : ℤ), pre ≠ [] →
      top = |pre.reverse.headD 0| → rem + pre.length = n → sum = pre.sum → sq = sqSum pre →
      abs = absSum pre → goTop n add c Q t k s top P d rem pre sum sq abs = true →
      go n add c Q t k s top rem pre sum sq abs = true
  | 0, rem, pre, sum, sq, abs, _, htop, hlen, hs, hq, ha, h => by
    simp only [goTop, List.contains_iff_mem] at h
    have hb := hP _ h
    simp only [below, List.reverse_reverse, List.length_reverse, sqSum, absSum,
      List.map_reverse, List.sum_reverse_int] at hb
    rw [htop, hs, hq, ha, show rem = n - pre.length by omega]
    exact hb
  | _ + 1, 0, pre, sum, sq, abs, _, _, _, _, _, _, h => by
    simpa only [goTop, go] using h
  | d + 1, rem + 1, pre, sum, sq, abs, hne, htop, hlen, hs, hq, ha, h => by
    simp only [goTop, Bool.or_eq_true, allRange_iff] at h
    simp only [go, Bool.or_eq_true, allRange_iff]
    rcases h with h | h
    · exact Or.inl h
    refine Or.inr fun x h1 h2 => ?_
    rcases h x h1 h2 with hx | hx
    · exact Or.inl hx
    refine Or.inr (go_of_goTop hP d rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|)
      (List.cons_ne_nil _ _) (by rw [headD_reverse_cons hne, htop]) ?_ ?_ ?_ ?_ hx)
    · simp only [List.length_cons]; omega
    · rw [List.sum_cons, hs]; ring
    · simp only [sqSum, List.map_cons, List.sum_cons] at hq ⊢; rw [hq]; ring
    · simp only [absSum, List.map_cons, List.sum_cons] at ha ⊢; rw [ha]; ring

/-- `noVector` from its top levels and the checks of the nodes they leave to `P`. -/
theorem noVector_of_top {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {P : List (List ℤ)} {d : ℕ}
    (hn : 0 < n) (htop : noVectorTop n add c Q t k s P d = true)
    (hP : ∀ p ∈ P, below n add c Q t k s p = true) : noVector n add c Q t k s = true := by
  simp only [noVectorTop, Bool.or_eq_true, allRange_iff] at htop
  simp only [noVector, Bool.or_eq_true, allRange_iff]
  rcases htop with h | h
  · exact Or.inl h
  refine Or.inr fun x h1 h2 => ?_
  rcases h x h1 h2 with hx | hx
  · exact Or.inl hx
  exact Or.inr (go_of_goTop hP d (n - 1) [x] x (x * x) |x| (List.cons_ne_nil _ _) (by simp)
    (by simp only [List.length_singleton]; omega) (by simp) (by simp [sqSum]) (by simp [absSum])
    hx)

end SignedDifferenceSets
