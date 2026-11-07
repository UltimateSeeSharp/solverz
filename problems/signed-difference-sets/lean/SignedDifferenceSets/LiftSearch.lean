module

public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.CosetSearch
public import SignedDifferenceSets.Symmetry

/-!
# Contraction, then lift (I16), checked by the kernel

Phase 1, `cover`: every integer vector on `H` that the coset sums of an SDS along `G → H` can be,
normalized as in `VectorSearch` (sum `s`, `|w₀|` largest), lies in a list `L` (`mem_of_cover`).
Phase 2, `liftCheck`: for one `Y`, no `f : G → {−1, 0, 1}` with coset sums `Y` and autocorrelation
`λ`. It assigns the cosets in the order `ord`, each by every pattern with sum `Y` there, keeps the
partial autocorrelation `Σₓ F x F (x + g)` of the assigned part `F` per shift as two counts, and
cuts when it is further from its target than the pairs not yet both assigned (`accOK`). A second
cut keeps only the lexicographically least of the images of `f` under affine maps of `G` that fix
every coset (`maps`, checked by `mapOK`). Values live in bit masks, all arithmetic in ℕ.
`not_hasSDS_of_lift` joins both phases on a row; both split into slices of nodes `d` levels down.
-/

@[expose] public section

namespace SignedDifferenceSets

namespace LiftSearch

/-! ### Lists the kernel evaluates -/

/-- `f a₀ ++ f a₁ ++ ⋯`. -/
def flatL {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ flatL f l

theorem mem_flatL {α β : Type} (f : α → List β) (b : β) :
    ∀ l, b ∈ flatL f l ↔ ∃ a ∈ l, b ∈ f a
  | [] => by simp [flatL]
  | a :: l => by simp [flatL, mem_flatL f b l]

theorem flatL_append {α β : Type} (f : α → List β) :
    ∀ l l', flatL f (l ++ l') = flatL f l ++ flatL f l'
  | [], _ => rfl
  | a :: l, l' => by simp [flatL, flatL_append f l l']

/-- The integers `lo, lo + 1, …` (`m` of them). -/
def rangeL (lo : ℤ) : ℕ → List ℤ
  | 0 => []
  | m + 1 => lo :: rangeL (lo + 1) m

theorem allRange_eq (p : ℤ → Bool) : ∀ lo m, allRange p lo m = (rangeL lo m).all p
  | _, 0 => rfl
  | lo, m + 1 => by simp [allRange, rangeL, allRange_eq p (lo + 1) m]

/-- The nodes `a, …, b − 1` of `P` pass `run`. -/
def sliceAll {α : Type} (P : List α) (run : α → Bool) (a b : ℕ) : Bool :=
  ((P.drop a).take (b - a)).all run

theorem all_of_sliceAll {α : Type} {P : List α} {run : α → Bool} :
    ∀ (cuts : List ℕ) (a : ℕ), CosetSearch.SlicesPass (sliceAll P run) (a :: cuts) →
      P.length ≤ CosetSearch.lastCut a cuts → ∀ n ∈ P.drop a, run n = true
  | [], a, _, hl, n, hn => by
    simp only [CosetSearch.lastCut] at hl
    rw [List.drop_eq_nil_of_le hl] at hn
    simp at hn
  | b :: cuts, a, h, hl, n, hn => by
    have h' : sliceAll P run a b = true ∧ CosetSearch.SlicesPass (sliceAll P run) (b :: cuts) := h
    rw [← List.take_append_drop (b - a) (P.drop a), List.mem_append, List.drop_drop] at hn
    rcases hn with hn | hn
    · exact List.all_eq_true.1 h'.1 n hn
    · exact all_of_sliceAll cuts b h'.2 hl n (List.drop_subset_drop_left P (by omega) hn)

/-! ### Phase 1: the coset-sum vectors, up to translation and negation -/

/-- `VectorSearch.go`, except that a vector meeting the demands passes when it is in `L`. -/
def coverGo (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s top : ℤ) (L : List (List ℤ)) :
    ℕ → List ℤ → ℤ → ℤ → ℤ → Bool
  | 0, pre, sum, sq, abs => !leafOK n add Q t k s pre.reverse sum sq abs || L.contains pre.reverse
  | rem + 1, pre, sum, sq, abs =>
    cut c Q s (rem + 1) sum sq ||
      allRange (fun x => decide (Q - sq < x * x) ||
        coverGo n add c Q t k s top L rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (-top) (2 * top + 1).toNat

theorem coverGo_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {L : List (List ℤ)} :
    ∀ (w pre : List ℤ) (sum sq abs : ℤ),
      coverGo n add c Q t k s top L w.length pre sum sq abs = true →
      (∀ y ∈ w, |y| ≤ top) → (∀ y ∈ w, |y| ≤ c) →
      sum + w.sum = s → sq + sqSum w = Q → abs + absSum w ≤ k →
      (k - (abs + absSum w)) % 2 = 0 → shiftsOK n add t (pre.reverse ++ w) = true →
      pre.reverse ++ w ∈ L
  | [], pre, sum, sq, abs, h, _, _, hs, hq, ha, hp, hw => by
    simp only [List.sum_nil, add_zero, sqSum, absSum, List.map_nil, List.append_nil] at *
    simpa [coverGo, leafOK, hs, hq, ha, hp, hw] using h
  | x :: w, pre, sum, sq, abs, h, ht, hc, hs, hq, ha, hp, hw => by
    have hcut := cut_false (x :: w) hc hs hq
    simp only [List.length_cons, coverGo] at h
    rw [List.length_cons] at hcut
    rw [hcut, Bool.false_or] at h
    simp only [List.mem_cons, forall_eq_or_imp] at ht hc
    have hx := allRange_abs h ht.1
    simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
    have hsq : ¬ Q - sq < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
    simp only [hsq, decide_false, Bool.false_or] at hx
    have := coverGo_sound w (x :: pre) (sum + x) (sq + x * x) (abs + |x|) hx ht.2 hc.2
      (by linarith) (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
      (by simp only [absSum]; rw [show abs + |x| + absSum w = abs + (|x| + absSum w) by ring]
          exact hp)
      (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hw)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using this

/-- `coverGo` from its first coordinate, which bounds the others. -/
def cover (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (L : List (List ℤ)) : Bool :=
  cut c Q s n 0 0 ||
    allRange (fun x => decide (Q < x * x) ||
      coverGo n add c Q t k s |x| L (n - 1) [x] x (x * x) |x|) (-c) (2 * c + 1).toNat

/-- `cover` passes only if every vector meeting the demands, `|x|` largest, is in `L`. -/
theorem cover_sound {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {L : List (List ℤ)}
    (h : cover n add c Q t k s L = true) (x : ℤ) (w : List ℤ) (hn : (x :: w).length = n)
    (hx : |x| ≤ c) (htop : ∀ y ∈ w, |y| ≤ |x|) (hc : ∀ y ∈ w, |y| ≤ c)
    (hs : (x :: w).sum = s) (hq : sqSum (x :: w) = Q) (ha : absSum (x :: w) ≤ k)
    (hp : (k - absSum (x :: w)) % 2 = 0) (hw : shiftsOK n add t (x :: w) = true) :
    x :: w ∈ L := by
  have hcall : ∀ y ∈ x :: w, |y| ≤ c := by
    simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, hc⟩
  have hcut := cut_false (sum := 0) (sq := 0) (x :: w) hcall (by simpa using hs)
    (by simpa using hq)
  rw [hn] at hcut
  rw [cover, hcut, Bool.false_or] at h
  have hr := allRange_abs h hx
  simp only [sqSum, absSum, List.map_cons, List.sum_cons] at hs hq ha hp
  have hsq : ¬ Q < x * x := by have := sqSum_nonneg w; simp only [sqSum] at this; linarith
  simp only [hsq, decide_false, Bool.false_or] at hr
  have hlen : n - 1 = w.length := by simp at hn; omega
  rw [hlen] at hr
  simpa using coverGo_sound w [x] x (x * x) |x| hr htop hc (by linarith)
    (by simp only [sqSum]; linarith) (by simp only [absSum]; linarith)
    (by simp only [absSum]; exact hp) (by simpa using hw)

/-- A node of `coverGo`: its arguments after `L`, with `top`. -/
structure VNode where
  /-- The bound on the coordinates left. -/
  top : ℤ
  /-- The coordinates left. -/
  rem : ℕ
  /-- The prefix, reversed. -/
  pre : List ℤ
  /-- Its sum. -/
  sum : ℤ
  /-- Its square sum. -/
  sq : ℤ
  /-- Its absolute sum. -/
  abs : ℤ

/-- `coverGo` from a node. -/
def VNode.run (n : ℕ) (add : ℕ → ℕ → ℕ) (c Q t k s : ℤ) (L : List (List ℤ)) (v : VNode) :
    Bool :=
  coverGo n add c Q t k s v.top L v.rem v.pre v.sum v.sq v.abs

/-- The nodes `d` levels below a node of `coverGo` that it does not cut. -/
def coverFront (c Q s top : ℤ) : ℕ → ℕ → List ℤ → ℤ → ℤ → ℤ → List VNode
  | 0, rem, pre, sum, sq, abs => [⟨top, rem, pre, sum, sq, abs⟩]
  | _ + 1, 0, pre, sum, sq, abs => [⟨top, 0, pre, sum, sq, abs⟩]
  | d + 1, rem + 1, pre, sum, sq, abs =>
    if cut c Q s (rem + 1) sum sq then [] else
      flatL (fun x => if Q - sq < x * x then [] else
          coverFront c Q s top d rem (x :: pre) (sum + x) (sq + x * x) (abs + |x|))
        (rangeL (-top) (2 * top + 1).toNat)

theorem coverGo_of_front {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s top : ℤ} {L : List (List ℤ)} :
    ∀ (d rem : ℕ) (pre : List ℤ) (sum sq abs : ℤ),
      (∀ v ∈ coverFront c Q s top d rem pre sum sq abs, v.run n add c Q t k s L = true) →
      coverGo n add c Q t k s top L rem pre sum sq abs = true
  | 0, _, _, _, _, _, h => h _ List.mem_cons_self
  | _ + 1, 0, _, _, _, _, h => h _ List.mem_cons_self
  | d + 1, rem + 1, pre, sum, sq, abs, h => by
    rw [coverGo, Bool.or_eq_true]
    by_cases hc : cut c Q s (rem + 1) sum sq = true
    · exact Or.inl hc
    refine Or.inr ?_
    rw [allRange_eq, List.all_eq_true]
    intro x hx
    by_cases hq : Q - sq < x * x
    · simp [hq]
    simp only [hq, decide_false, Bool.false_or]
    refine coverGo_of_front d rem _ _ _ _ fun v hv => h v ?_
    simp only [coverFront, hc, Bool.false_eq_true, ↓reduceIte, mem_flatL]
    exact ⟨x, hx, by simpa [hq] using hv⟩

/-- `cover`'s nodes `d + 1` levels down. -/
def coverNodes (n : ℕ) (c Q s : ℤ) (d : ℕ) : List VNode :=
  if cut c Q s n 0 0 then [] else
    flatL (fun x => if Q < x * x then [] else coverFront c Q s |x| d (n - 1) [x] x (x * x) |x|)
      (rangeL (-c) (2 * c + 1).toNat)

theorem cover_of_nodes {n : ℕ} {add : ℕ → ℕ → ℕ} {c Q t k s : ℤ} {L : List (List ℤ)} {d : ℕ}
    (h : ∀ v ∈ coverNodes n c Q s d, v.run n add c Q t k s L = true) :
    cover n add c Q t k s L = true := by
  rw [cover, Bool.or_eq_true]
  by_cases hc : cut c Q s n 0 0 = true
  · exact Or.inl hc
  refine Or.inr ?_
  rw [allRange_eq, List.all_eq_true]
  intro x hx
  by_cases hq : Q < x * x
  · simp [hq]
  simp only [hq, decide_false, Bool.false_or]
  refine coverGo_of_front d _ _ _ _ _ fun v hv => h v ?_
  simp only [coverNodes, hc, Bool.false_eq_true, ↓reduceIte, mem_flatL]
  exact ⟨x, hx, by simpa [hq] using hv⟩

section Group

variable {H : Type*} [AddCommGroup H] [Fintype H] [Indexed H] {c k : ℕ} {lam : ℤ} {b : H → ℤ}

/-- A vector meeting the demands, `Σ b = s` and `|b 0|` largest, is in `L` when `cover` passes. -/
theorem mem_of_cover {s : ℤ} {L : List (List ℤ)}
    (hn : cover (Indexed.size H) (Indexed.addIdx H) c (k + lam * ((c : ℤ) - 1)) (lam * c) k s L
      = true)
    (hb : Demands c k lam b) (hmax : ∀ h, |b h| ≤ |b 0|) (hs : ∑ h, b h = s) :
    List.ofFn (fun i => b (Indexed.equiv.symm i)) ∈ L := by
  set n := Indexed.size H
  set e : H ≃ Fin n := Indexed.equiv
  have hpos : 0 < n := (e 0).pos
  have he0 : e.symm ⟨0, hpos⟩ = 0 := e.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  set F : Fin n → ℤ := fun i => b (e.symm i)
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have hne : List.ofFn F ≠ [] := by
    intro h
    have := List.length_ofFn (f := F)
    rw [h] at this
    simp at this
    omega
  obtain ⟨x, w, hL⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = b 0 := by
    have := getD_ofFn F hpos
    rw [hL] at this
    simpa [F, he0] using this
  have hw : ∀ y ∈ w, ∃ h, b h = y := fun y hy => hmem y (hL ▸ List.mem_cons_of_mem x hy)
  rw [hL]
  refine cover_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
    (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hx ▸ hmax h
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hb.bound h
  · rw [← hL, ← hs]
    simpa using hsum id
  · rw [← hL, ← hb.sq]
    exact hsum fun y => y * y
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.abs
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.parity
  · rw [← hL, shiftsOK, allTo_iff]
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp
    set gH := e.symm ⟨g, hg⟩
    have hgH : (e gH : ℕ) = g := by simp [gH]
    have hgH0 : gH ≠ 0 := by
      intro h0
      have := hgH
      rw [h0, Indexed.equiv_zero] at this
      omega
    simp only [Bool.or_eq_true, beq_iff_eq]
    right
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := H)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

end Group

/-! ### Phase 2 on the numbers: a group's element numbers -/

/-- What a group's numbering gives the addition on `0, …, v − 1`. -/
structure NumGroup (v : ℕ) (add : ℕ → ℕ → ℕ) : Prop where
  pos : 0 < v
  lt : ∀ x y, x < v → y < v → add x y < v
  assoc : ∀ x y z, x < v → y < v → z < v → add (add x y) z = add x (add y z)
  comm : ∀ x y, x < v → y < v → add x y = add y x
  zero : ∀ x, x < v → add x 0 = x
  neg : ∀ g, g < v → ∃ y, y < v ∧ add y g = 0

theorem numGroup_of_indexed (G : Type*) [AddCommGroup G] [Indexed G] :
    NumGroup (Indexed.size G) (Indexed.addIdx G) := by
  have key : ∀ x y (hx : x < Indexed.size G) (hy : y < Indexed.size G),
      Indexed.addIdx G x y =
        (Indexed.equiv (Indexed.equiv.symm ⟨x, hx⟩ + Indexed.equiv.symm ⟨y, hy⟩ : G) : ℕ) := by
    intro x y hx hy
    rw [Indexed.equiv_add]
    simp
  have h0 : (Indexed.equiv.symm ⟨0, (Indexed.equiv (0 : G)).pos⟩ : G) = 0 :=
    Indexed.equiv.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  refine ⟨(Indexed.equiv (0 : G)).pos, fun x y hx hy => ?_, fun x y z hx hy hz => ?_,
    fun x y hx hy => ?_, fun x hx => ?_,
    fun g hg => ⟨Indexed.equiv (-Indexed.equiv.symm ⟨g, hg⟩ : G), (Indexed.equiv _).isLt, ?_⟩⟩
  · rw [key x y hx hy]; exact (Indexed.equiv _).isLt
  · rw [key x y hx hy, key _ z (Indexed.equiv _).isLt hz, key y z hy hz,
      key x _ hx (Indexed.equiv _).isLt]
    simp [add_assoc]
  · rw [key x y hx hy, key y x hy hx, add_comm]
  · rw [key x 0 hx (Indexed.equiv (0 : G)).pos, h0, add_zero]
    simp
  · rw [key _ g (Indexed.equiv _).isLt hg]
    simp [Indexed.equiv_zero]

variable {v : ℕ} {add : ℕ → ℕ → ℕ}

/-- The number of `−g`: the first `y < v` with `y + g = 0`. -/
def negN (v : ℕ) (add : ℕ → ℕ → ℕ) (g : ℕ) : ℕ :=
  ((List.range v).find? fun y => add y g == 0).getD 0

theorem NumGroup.negN_spec (hG : NumGroup v add) {g : ℕ} (hg : g < v) :
    negN v add g < v ∧ add (negN v add g) g = 0 := by
  unfold negN
  cases h : (List.range v).find? fun y => add y g == 0 with
  | none =>
    obtain ⟨y, hy, hy0⟩ := hG.neg g hg
    have := List.find?_eq_none.1 h y (List.mem_range.2 hy)
    simp [hy0] at this
  | some y =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [beq_iff_eq] at h1
    exact ⟨List.mem_range.1 h2, h1⟩

theorem NumGroup.add_negN (hG : NumGroup v add) {x g : ℕ} (hx : x < v) (hg : g < v) :
    add (add x g) (negN v add g) = x := by
  obtain ⟨hn, h0⟩ := hG.negN_spec hg
  rw [hG.assoc _ _ _ hx hg hn, hG.comm _ _ hg hn, h0, hG.zero _ hx]

theorem NumGroup.negN_add (hG : NumGroup v add) {x g : ℕ} (hx : x < v) (hg : g < v) :
    add (add x (negN v add g)) g = x := by
  obtain ⟨hn, h0⟩ := hG.negN_spec hg
  rw [hG.assoc _ _ _ hx hn hg, h0, hG.zero _ hx]

/-- Translation by `g` permutes `0, …, v − 1`. -/
theorem NumGroup.sum_shift (hG : NumGroup v add) {g : ℕ} (hg : g < v) (φ : ℕ → ℤ) :
    ∑ y ∈ Finset.range v, φ (add y g) = ∑ y ∈ Finset.range v, φ y := by
  have hn := (hG.negN_spec hg).1
  refine Finset.sum_nbij' (fun y => add y g) (fun y => add y (negN v add g)) ?_ ?_ ?_ ?_ ?_
  · intro y hy; rw [Finset.mem_range] at hy ⊢; exact hG.lt _ _ hy hg
  · intro y hy; rw [Finset.mem_range] at hy ⊢; exact hG.lt _ _ hy hn
  · intro y hy; exact hG.add_negN (Finset.mem_range.1 hy) hg
  · intro y hy; exact hG.negN_add (Finset.mem_range.1 hy) hg
  · intro y _; rfl

/-- `a − b = 0` only for `a = b`. -/
theorem NumGroup.eq_of_add_negN (hG : NumGroup v add) {a b : ℕ} (ha : a < v) (hb : b < v)
    (h : add a (negN v add b) = 0) : a = b := by
  obtain ⟨hn, h0⟩ := hG.negN_spec hb
  have : add (add a (negN v add b)) b = b := by rw [h, hG.comm _ _ (hG.pos) hb, hG.zero _ hb]
  rwa [hG.negN_add ha hb] at this

/-- The autocorrelation of `F'` from that of `F` at a shift `g`: the change `F' − F` against
`F' (y + g) + F (y − g)`. -/
theorem NumGroup.corr_update (hG : NumGroup v add) {g : ℕ} (hg : g < v) (F F' : ℕ → ℤ) :
    ∑ y ∈ Finset.range v, F' y * F' (add y g) =
      ∑ y ∈ Finset.range v, F y * F (add y g) +
        ∑ y ∈ Finset.range v, (F' y - F y) * (F' (add y g) + F (add y (negN v add g))) := by
  have h2 : ∑ y ∈ Finset.range v, F y * (F' (add y g) - F (add y g)) =
      ∑ y ∈ Finset.range v, (F' y - F y) * F (add y (negN v add g)) := by
    rw [← hG.sum_shift hg (fun y => (F' y - F y) * F (add y (negN v add g)))]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hG.add_negN (Finset.mem_range.1 hy) hg]
    ring
  have e : ∀ y, F' y * F' (add y g) = F y * F (add y g) + (F' y - F y) * F' (add y g) +
      F y * (F' (add y g) - F (add y g)) := fun y => by ring
  simp only [e, Finset.sum_add_distrib, h2, mul_add]
  ring

/-! ### Masks -/

/-- Bit `y` of `P`, as `0` or `1`. -/
def bit (P y : ℕ) : ℕ := Nat.mod (Nat.shiftRight P y) 2

theorem bit_eq (P y : ℕ) : bit P y = (P.testBit y).toNat := by
  rw [Nat.toNat_testBit]
  change (P >>> y) % 2 = _
  rw [Nat.shiftRight_eq_div_pow]

/-- The value `+1`, `−1` or `0` the masks mark at `y`. -/
def valM (P M y : ℕ) : ℤ := (bit P y : ℤ) - bit M y

/-- The mask of the elements of `xs` whose code in `p` is `b`. -/
def maskOf (b : ℕ) : List ℕ → List ℕ → ℕ
  | x :: xs, u :: p => Nat.lor (bif Nat.beq u b then 2 ^ x else 0) (maskOf b xs p)
  | _, _ => 0

/-- The code of a value: `1` for `+1`, `2` for `−1`, `0` otherwise. -/
def code (z : ℤ) : ℕ := if z = 1 then 1 else if z = -1 then 2 else 0

theorem testBit_maskOf (f : ℕ → ℤ) (b y : ℕ) : ∀ xs : List ℕ,
    (maskOf b xs (xs.map fun x => code (f x))).testBit y = decide (y ∈ xs ∧ code (f y) = b)
  | [] => by simp [maskOf]
  | x :: xs => by
    simp only [List.map_cons, maskOf]
    rw [show ∀ a c : ℕ, Nat.lor a c = a ||| c from fun _ _ => rfl, Nat.testBit_or,
      testBit_maskOf f b y xs]
    cases hb : Nat.beq (code (f x)) b
    · have : code (f x) ≠ b := Nat.ne_of_beq_eq_false hb
      by_cases hxy : x = y
      · subst hxy; simp [this]
      · simp [Nat.zero_testBit, Ne.symm hxy]
    · have : code (f x) = b := Nat.eq_of_beq_eq_true hb
      by_cases hxy : x = y
      · subst hxy; simp [this]
      · simp [hxy, Ne.symm hxy]

/-- Every list of codes with sum `y` (`1` counts `+1`, `2` counts `−1`). -/
def patsOf : ℕ → ℤ → List (List ℕ)
  | 0, y => if y = 0 then [[]] else []
  | l + 1, y => (patsOf l (y - 1)).map (List.cons 1) ++ (patsOf l y).map (List.cons 0) ++
      (patsOf l (y + 1)).map (List.cons 2)

/-- The sign of a code. -/
def sgn (u : ℕ) : ℤ := if u = 1 then 1 else if u = 2 then -1 else 0

/-- A value in `{−1, 0, 1}`. -/
def IsSign (z : ℤ) : Prop := z = 1 ∨ z = 0 ∨ z = -1

theorem sgn_code {z : ℤ} (h : IsSign z) : sgn (code z) = z := by
  rcases h with rfl | rfl | rfl <;> simp [sgn, code]

theorem mem_patsOf (f : ℕ → ℤ) : ∀ xs : List ℕ, (∀ x ∈ xs, IsSign (f x)) →
    xs.map (fun x => code (f x)) ∈ patsOf xs.length (xs.map f).sum
  | [], _ => by simp [patsOf]
  | x :: xs, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have ih := mem_patsOf f xs h.2
    simp only [List.map_cons, List.length_cons, List.sum_cons, patsOf, List.mem_append,
      List.mem_map, List.cons.injEq]
    rcases h.1 with h1 | h1 | h1
    · left; left; exact ⟨_, by rw [h1]; convert ih using 2; ring, by simp [code, h1], rfl⟩
    · left; right; exact ⟨_, by rw [h1]; convert ih using 2; ring, by simp [code, h1], rfl⟩
    · right; exact ⟨_, by rw [h1]; convert ih using 2; ring, by simp [code, h1], rfl⟩

/-! ### The search -/

/-- The elements of coset `a`: the numbers `x < v` with `q x = a`. -/
def cosL (v : ℕ) (q : ℕ → ℕ) (a : ℕ) : List ℕ := (List.range v).filter fun x => q x == a

theorem sum_cosL (v : ℕ) (q : ℕ → ℕ) (a : ℕ) (φ : ℕ → ℤ) :
    ((cosL v q a).map φ).sum = ∑ x ∈ Finset.range v, if q x = a then φ x else 0 := by
  unfold cosL
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : q v = a <;> simp [h]

theorem mem_cosL {v : ℕ} {q : ℕ → ℕ} {a x : ℕ} : x ∈ cosL v q a ↔ x < v ∧ q x = a := by
  simp [cosL]

/-- At one shift: for each entry of the pattern `p` coded `1` (`2`), its partners `x + g` under
the new masks `P'`, `M'` and `x − g` under the old ones add to the first (second) count when
marked `+`, to the second (first) when marked `−`. -/
def updG (P M P' M' : ℕ) : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → ℕ × ℕ
  | u :: p, yy :: pg, ab =>
    updG P M P' M' p pg
      (bif Nat.beq u 1 then
        (Nat.add (Nat.add ab.1 (bit P' yy.1)) (bit P yy.2),
          Nat.add (Nat.add ab.2 (bit M' yy.1)) (bit M yy.2))
      else bif Nat.beq u 2 then
        (Nat.add (Nat.add ab.1 (bit M' yy.1)) (bit M yy.2),
          Nat.add (Nat.add ab.2 (bit P' yy.1)) (bit P yy.2))
      else ab)
  | _, _, ab => ab

/-- `updG` at every shift. -/
def stepAcc (P M P' M' : ℕ) (p : List ℕ) :
    List (List (ℕ × ℕ)) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | pg :: part, ab :: acc => updG P M P' M' p pg ab :: stepAcc P M P' M' p part acc
  | _, _ => []

/-- Each shift's counts are within `r` of `λ = lp − lm`. -/
def restOK (lp lm : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | r :: R, ab :: acc =>
    Nat.ble (Nat.add ab.2 lp) (Nat.add (Nat.add ab.1 r) lm) &&
      Nat.ble (Nat.add ab.1 lm) (Nat.add (Nat.add ab.2 lp) r) && restOK lp lm R acc
  | _, _ => true

/-- Shift `0`'s counts are within `r` of `k`, the others within theirs of `λ = lp − lm`. -/
def accOK (k lp lm : ℕ) : List ℕ → List (ℕ × ℕ) → Bool
  | r :: R, ab :: acc =>
    Nat.ble (Nat.add ab.2 k) (Nat.add ab.1 r) && Nat.ble ab.1 (Nat.add (Nat.add ab.2 k) r) &&
      restOK lp lm R acc
  | _, _ => true

/-- `2` for `+`, `1` for `−`, `0` for unmarked. -/
def codeM (P M y : ℕ) : ℕ := Nat.add (Nat.mul 2 (bit P y)) (bit M y)

/-- The codes at `as` come before those at `zs`, lexicographically. -/
def lexLtM (P M : ℕ) : List ℕ → List ℕ → Bool
  | a :: as, z :: zs =>
    Nat.blt (codeM P M a) (codeM P M z) ||
      (Nat.beq (codeM P M a) (codeM P M z) && lexLtM P M as zs)
  | _, _ => false

/-- One coset's step: its elements, the patterns tried, per shift the partners `(x + g, x − g)`
of its elements, per shift the pairs not both assigned after it, the elements assigned after it
in order, and their images under each map tried here. -/
structure Step where
  /-- The coset's elements. -/
  xs : List ℕ
  /-- The patterns tried. -/
  pats : List (List ℕ)
  /-- Per shift, the partners of `xs`. -/
  part : List (List (ℕ × ℕ))
  /-- Per shift, the pairs not both assigned. -/
  R : List ℕ
  /-- The assigned elements, in order. -/
  zs : List ℕ
  /-- Their images under each map. -/
  imgs : List (List ℕ)

/-- The plus mask after pattern `p` on the step's coset. -/
def newP (P : ℕ) (st : Step) (p : List ℕ) : ℕ := Nat.lor P (maskOf 1 st.xs p)

/-- The minus mask after pattern `p` on the step's coset. -/
def newM (M : ℕ) (st : Step) (p : List ℕ) : ℕ := Nat.lor M (maskOf 2 st.xs p)

/-- The counts after pattern `p` on the step's coset. -/
def newAcc (P M : ℕ) (st : Step) (p : List ℕ) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  stepAcc P M (newP P st p) (newM M st p) p st.part acc

/-- Pattern `p` is cut: a shift's counts out of reach, or a map's image lexicographically less. -/
def cutAt (k lp lm : ℕ) (st : Step) (P M : ℕ) (acc : List (ℕ × ℕ)) (p : List ℕ) : Bool :=
  !accOK k lp lm st.R (newAcc P M st p acc) ||
    st.imgs.any fun im => lexLtM (newP P st p) (newM M st p) im st.zs

/-- The search over the steps `sts` from masks `P`, `M` and counts `acc`: `true` when every
pattern is cut. -/
def liftGo (k lp lm : ℕ) : List Step → ℕ → ℕ → List (ℕ × ℕ) → Bool
  | [], _, _, _ => false
  | st :: sts, P, M, acc =>
    st.pats.all fun p => cutAt k lp lm st P M acc p ||
      liftGo k lp lm sts (newP P st p) (newM M st p) (newAcc P M st p acc)

/-- The step at depth `t`: coset `ord[t]`, maps tried while `t < m`. -/
def mkStep (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (ord : List ℕ)
    (maps : List (List ℕ)) (m t : ℕ) : Step :=
  { xs := cosL v q (ord.getD t 0)
    pats := patsOf (cosL v q (ord.getD t 0)).length (Y.getD (ord.getD t 0) 0)
    part := (List.range v).map fun g =>
      (cosL v q (ord.getD t 0)).map fun x => (add x g, add x (negN v add g))
    R := (List.range v).map fun g => OrbitSearch.countTo (fun x =>
      !((ord.take (t + 1)).contains (q x) && (ord.take (t + 1)).contains (q (add x g)))) v
    zs := flatL (cosL v q) (ord.take (t + 1))
    imgs := if t < m then
      maps.map fun al => (flatL (cosL v q) (ord.take (t + 1))).map fun z => al.getD z 0 else [] }

/-- The search from the empty assignment over the steps of `ord`. -/
def liftCheck (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (ord : List ℕ)
    (maps : List (List ℕ)) (m k : ℕ) (lam : ℤ) : Bool :=
  liftGo k lam.toNat (-lam).toNat ((List.range ord.length).map (mkStep v add q Y ord maps m)) 0 0
    ((List.range v).map fun _ => (0, 0))

/-- A map `x ↦ al[x]` of `0, …, v − 1` into itself that fixes every coset, is one to one and
affine: `al (x + g) = al x + (al g − al 0)`. -/
def mapOK (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (al : List ℕ) : Bool :=
  allTo (fun x => Nat.blt (al.getD x 0) v && Nat.beq (q (al.getD x 0)) (q x) &&
    allTo (fun g => Nat.beq (al.getD (add x g) 0)
        (add (al.getD x 0) (add (al.getD g 0) (negN v add (al.getD 0 0)))) &&
      (!Nat.beq (al.getD x 0) (al.getD g 0) || Nat.beq x g)) v) v

/-! ### Soundness of the search -/

/-- `f` lifts `Y`: values in `{−1, 0, 1}` on `0, …, v − 1` (`0` beyond), coset sums `Y` along
`q`, autocorrelation `k` at shift `0` and `λ` at the others. -/
structure Sol (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (k : ℕ) (lam : ℤ)
    (f : ℕ → ℤ) : Prop where
  out : ∀ x, v ≤ x → f x = 0
  sign : ∀ x, IsSign (f x)
  cos : ∀ a, ∑ x ∈ Finset.range v, (if q x = a then f x else 0) = Y.getD a 0
  corr : ∀ g, g < v → ∑ x ∈ Finset.range v, f x * f (add x g) = if g = 0 then (k : ℤ) else lam

/-- `f` on the elements `A` marks below `v`, `0` elsewhere. -/
def restr (v : ℕ) (A : ℕ → Bool) (f : ℕ → ℤ) (y : ℕ) : ℤ := if y < v ∧ A y = true then f y else 0

/-- The masks `P`, `M` mark `f`'s `+1` and `−1` on the elements `A` marks below `v`. -/
def Enc (v : ℕ) (A : ℕ → Bool) (f : ℕ → ℤ) (P M : ℕ) : Prop :=
  ∀ y, P.testBit y = (decide (y < v) && A y && decide (f y = 1)) ∧
    M.testBit y = (decide (y < v) && A y && decide (f y = -1))

/-- Shift `g`'s counts, as an integer. -/
def accVal (acc : List (ℕ × ℕ)) (g : ℕ) : ℤ := ((acc.getD g (0, 0)).1 : ℤ) - (acc.getD g (0, 0)).2

/-- The counts hold the autocorrelation of `F` at every shift below `v`. -/
def AccInv (v : ℕ) (add : ℕ → ℕ → ℕ) (F : ℕ → ℤ) (acc : List (ℕ × ℕ)) : Prop :=
  acc.length = v ∧ ∀ g, g < v → accVal acc g = ∑ x ∈ Finset.range v, F x * F (add x g)

variable {q : ℕ → ℕ} {Y : List ℤ} {k : ℕ} {lam : ℤ} {f : ℕ → ℤ}

theorem valM_of_enc {A : ℕ → Bool} {P M : ℕ} (hs : ∀ y, IsSign (f y)) (h : Enc v A f P M)
    (y : ℕ) : valM P M y = restr v A f y := by
  have hP := (h y).1
  have hM := (h y).2
  simp only [valM, bit_eq, hP, hM, restr]
  by_cases hy : y < v ∧ A y = true
  · rw [ite_eq_left hy]
    rcases hs y with h1 | h1 | h1 <;> simp [hy.1, hy.2, h1]
  · rw [ite_eq_right hy]
    by_cases hv : y < v
    · have : A y = false := by simpa [hv] using hy
      simp [hv, this]
    · simp [hv]

/-- The code `codeM` reads: `2` for `+1`, `1` for `−1`, `0` otherwise. -/
def codeV (z : ℤ) : ℕ := if z = 1 then 2 else if z = -1 then 1 else 0

theorem codeV_lt (z : ℤ) : codeV z < 3 := by unfold codeV; split_ifs <;> omega

theorem codeM_of_enc {A : ℕ → Bool} {P M : ℕ} (h : Enc v A f P M) {y : ℕ} (hy : y < v)
    (hA : A y = true) : codeM P M y = codeV (f y) := by
  simp only [codeM, bit_eq, (h y).1, (h y).2, hy, hA, codeV, Nat.add_eq, Nat.mul_eq]
  by_cases h1 : f y = 1
  · simp [h1]
  · by_cases h2 : f y = -1 <;> simp [h1, h2]

theorem enc_step {A : ℕ → Bool} {P M : ℕ} (h : Enc v A f P M) (j : ℕ) :
    Enc v (fun y => A y || decide (q y = j)) f
      (Nat.lor P (maskOf 1 (cosL v q j) ((cosL v q j).map fun x => code (f x))))
      (Nat.lor M (maskOf 2 (cosL v q j) ((cosL v q j).map fun x => code (f x)))) := by
  intro y
  have e : ∀ a c : ℕ, Nat.lor a c = a ||| c := fun _ _ => rfl
  rw [e, e, Nat.testBit_or, Nat.testBit_or, testBit_maskOf, testBit_maskOf, (h y).1, (h y).2]
  have hm : y ∈ cosL v q j ↔ y < v ∧ q y = j := mem_cosL
  by_cases hv : y < v <;> by_cases hq : q y = j <;> by_cases h1 : f y = 1 <;>
    by_cases h2 : f y = -1 <;> simp [hm, hv, hq, h1, h2, code]

theorem updG_spec (P M P' M' : ℕ) : ∀ (p : List ℕ) (pg : List (ℕ × ℕ)) (ab : ℕ × ℕ),
    ((updG P M P' M' p pg ab).1 : ℤ) - (updG P M P' M' p pg ab).2 = (ab.1 : ℤ) - ab.2 +
      ((p.zip pg).map fun up => sgn up.1 * (valM P' M' up.2.1 + valM P M up.2.2)).sum
  | [], _, ab => by simp [updG]
  | _ :: _, [], ab => by simp [updG]
  | u :: p, yy :: pg, ab => by
    rw [updG, updG_spec P M P' M' p pg]
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    cases h1 : Nat.beq u 1
    · have h1' : u ≠ 1 := Nat.ne_of_beq_eq_false h1
      cases h2 : Nat.beq u 2
      · have h2' : u ≠ 2 := Nat.ne_of_beq_eq_false h2
        simp [sgn, h1', h2']
      · have h2' : u = 2 := Nat.eq_of_beq_eq_true h2
        simp only [Bool.cond_false, Bool.cond_true, Nat.add_eq, sgn, h2', valM]
        push_cast; ring
    · have h1' : u = 1 := Nat.eq_of_beq_eq_true h1
      simp only [Bool.cond_true, Nat.add_eq, sgn, h1', valM]
      push_cast; ring

theorem stepAcc_getD (P M P' M' : ℕ) (p : List ℕ) : ∀ (part : List (List (ℕ × ℕ)))
    (acc : List (ℕ × ℕ)) (g : ℕ), g < part.length → g < acc.length →
      (stepAcc P M P' M' p part acc).getD g (0, 0) =
        updG P M P' M' p (part.getD g []) (acc.getD g (0, 0))
  | [], _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h => absurd h (by simp)
  | pg :: part, ab :: acc, 0, _, _ => rfl
  | pg :: part, ab :: acc, g + 1, h1, h2 => by
    simp only [stepAcc, List.getD_cons_succ]
    exact stepAcc_getD P M P' M' p part acc g (by simpa using h1) (by simpa using h2)

theorem length_stepAcc (P M P' M' : ℕ) (p : List ℕ) : ∀ (part : List (List (ℕ × ℕ)))
    (acc : List (ℕ × ℕ)), (stepAcc P M P' M' p part acc).length = min part.length acc.length
  | [], _ => by simp [stepAcc]
  | _ :: _, [] => by simp [stepAcc]
  | pg :: part, ab :: acc => by
    simp [stepAcc, length_stepAcc P M P' M' p part acc, Nat.succ_min_succ]

theorem zip_map_map {α β γ δ : Type} (a : α → β) (b : α → γ) (h : β × γ → δ) :
    ∀ xs : List α, ((xs.map a).zip (xs.map b)).map h = xs.map fun x => h (a x, b x)
  | [] => rfl
  | x :: xs => by simp [zip_map_map a b h xs]

theorem restOK_of {lp lm : ℕ} : ∀ (R : List ℕ) (acc : List (ℕ × ℕ)),
    (∀ i, i < R.length → i < acc.length →
      |((lp : ℤ) - lm) - accVal acc i| ≤ (R.getD i 0 : ℤ)) → restOK lp lm R acc = true
  | [], _, _ => by simp [restOK]
  | _ :: _, [], _ => by simp [restOK]
  | r :: R, ab :: acc, h => by
    have h0 := h 0 (by simp) (by simp)
    simp only [accVal, List.getD_cons_zero] at h0
    simp only [restOK, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq]
    refine ⟨⟨?_, ?_⟩, restOK_of R acc fun i h1 h2 => ?_⟩
    · have := (abs_le.1 h0).2; omega
    · have := (abs_le.1 h0).1; omega
    · have := h (i + 1) (by simpa using h1) (by simpa using h2)
      simpa [accVal] using this

theorem accOK_of {k lp lm : ℕ} : ∀ (R : List ℕ) (acc : List (ℕ × ℕ)),
    (∀ i, i < R.length → i < acc.length →
      |(if i = 0 then (k : ℤ) else (lp : ℤ) - lm) - accVal acc i| ≤ (R.getD i 0 : ℤ)) →
    accOK k lp lm R acc = true
  | [], _, _ => by simp [accOK]
  | _ :: _, [], _ => by simp [accOK]
  | r :: R, ab :: acc, h => by
    have h0 := h 0 (by simp) (by simp)
    simp only [accVal, List.getD_cons_zero, ↓reduceIte] at h0
    simp only [accOK, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq]
    refine ⟨⟨?_, ?_⟩, restOK_of R acc fun i h1 h2 => ?_⟩
    · have := (abs_le.1 h0).2; omega
    · have := (abs_le.1 h0).1; omega
    · have := h (i + 1) (by simpa using h1) (by simpa using h2)
      simpa [accVal] using this

/-- The pairs `(x, x + g)` not both in `A` bound how far the autocorrelation of `f` on `A` is from
that of `f`. -/
theorem abs_corr_sub_le (hG : NumGroup v add) (hsol : Sol v add q Y k lam f) (A : ℕ → Bool)
    {g : ℕ} (hg : g < v) :
    |(if g = 0 then (k : ℤ) else lam) -
        ∑ x ∈ Finset.range v, restr v A f x * restr v A f (add x g)| ≤
      (OrbitSearch.countTo (fun x => !(A x && A (add x g))) v : ℤ) := by
  rw [← hsol.corr g hg, ← Finset.sum_sub_distrib, OrbitSearch.countTo_eq, Finset.card_filter]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hx' := Finset.mem_range.1 hx
  have hxg := hG.lt _ _ hx' hg
  by_cases hA : A x = true ∧ A (add x g) = true
  · simp [restr, hx', hxg, hA.1, hA.2]
  · have h0 : restr v A f x * restr v A f (add x g) = 0 := by
      by_cases h1 : A x = true
      · have : A (add x g) = false := by simpa [h1] using hA
        simp [restr, this]
      · simp [restr, h1]
    have h1 : (!(A x && A (add x g))) = true := by
      cases hx : A x <;> cases hy : A (add x g) <;> simp_all
    rw [h0, sub_zero, ite_eq_left h1]
    rcases hsol.sign x with h | h | h <;> rcases hsol.sign (add x g) with h' | h' | h' <;>
      simp [h, h']

/-! ### Keys: the lexicographic order on the assigned values -/

/-- The digits `l`, most significant first, in base 3. -/
def keyL : List ℕ → ℕ
  | [] => 0
  | d :: l => d * 3 ^ l.length + keyL l

theorem keyL_lt : ∀ l : List ℕ, (∀ d ∈ l, d < 3) → keyL l < 3 ^ l.length
  | [], _ => by simp [keyL]
  | d :: l, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have := keyL_lt l h.2
    have h1 : d * 3 ^ l.length ≤ 2 * 3 ^ l.length := Nat.mul_le_mul_right _ (by omega)
    simp only [keyL, List.length_cons, pow_succ]
    linarith

theorem keyL_append : ∀ a b : List ℕ, keyL (a ++ b) = keyL a * 3 ^ b.length + keyL b
  | [], _ => by simp [keyL]
  | d :: a, b => by
    simp only [List.cons_append, keyL, keyL_append a b, List.length_append, pow_add]
    ring

/-- Lexicographic `<` on digit lists. -/
def lexLt : List ℕ → List ℕ → Bool
  | a :: as, b :: bs => Nat.blt a b || (Nat.beq a b && lexLt as bs)
  | _, _ => false

theorem lexLtM_eq (P M : ℕ) : ∀ as zs : List ℕ,
    lexLtM P M as zs = lexLt (as.map (codeM P M)) (zs.map (codeM P M))
  | [], _ => by simp [lexLtM, lexLt]
  | _ :: _, [] => by simp [lexLtM, lexLt]
  | a :: as, z :: zs => by simp [lexLtM, lexLt, lexLtM_eq P M as zs]

theorem keyL_lt_of_lexLt : ∀ a b : List ℕ, a.length = b.length → (∀ d ∈ a, d < 3) →
    lexLt a b = true → keyL a < keyL b
  | [], _, _, _, h => by simp [lexLt] at h
  | _ :: _, [], _, _, h => by simp [lexLt] at h
  | x :: a, y :: b, hl, hd, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.mem_cons, forall_eq_or_imp] at hd
    simp only [lexLt, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, Nat.beq_eq] at h
    simp only [keyL, hl]
    rcases h with h | ⟨rfl, h⟩
    · have := keyL_lt a hd.2
      rw [hl] at this
      have h1 : (x + 1) * 3 ^ b.length ≤ y * 3 ^ b.length := Nat.mul_le_mul_right _ h
      linarith
    · have := keyL_lt_of_lexLt a b hl hd.2 h
      linarith

theorem keyL_append_lt {a b c d : List ℕ} (hab : keyL a < keyL b) (hl : c.length = d.length)
    (hc : ∀ x ∈ c, x < 3) : keyL (a ++ c) < keyL (b ++ d) := by
  rw [keyL_append, keyL_append, ← hl]
  have := keyL_lt c hc
  have h1 : (keyL a + 1) * 3 ^ c.length ≤ keyL b * 3 ^ c.length := Nat.mul_le_mul_right _ hab
  linarith

/-- The values of `f` in the order the search assigns them, as a base-3 number. -/
def key (v : ℕ) (q : ℕ → ℕ) (ord : List ℕ) (f : ℕ → ℤ) : ℕ :=
  keyL ((flatL (cosL v q) ord).map fun z => codeV (f z))

/-- `f` composed with `x ↦ al[x]` on `0, …, v − 1`. -/
def act (v : ℕ) (al : List ℕ) (f : ℕ → ℤ) (x : ℕ) : ℤ := if x < v then f (al.getD x 0) else 0

/-- What `mapOK` gives. -/
theorem mapOK_spec {al : List ℕ} (h : mapOK v add q al = true) {x : ℕ} (hx : x < v) :
    al.getD x 0 < v ∧ q (al.getD x 0) = q x ∧ ∀ g, g < v →
      al.getD (add x g) 0 = add (al.getD x 0) (add (al.getD g 0) (negN v add (al.getD 0 0))) ∧
      (al.getD x 0 = al.getD g 0 → x = g) := by
  unfold mapOK at h
  have := (allTo_iff _ _).1 h x hx
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allTo_iff, Bool.or_eq_true,
    Bool.not_eq_true'] at this
  refine ⟨this.1.1, this.1.2, fun g hg => ⟨(this.2 g hg).1, fun he => ?_⟩⟩
  rcases (this.2 g hg).2 with h1 | h1
  · exact absurd he (Nat.ne_of_beq_eq_false h1)
  · exact h1

theorem sum_perm {al : List ℕ} (h : mapOK v add q al = true)
    (φ : ℕ → ℤ) : ∑ x ∈ Finset.range v, φ (al.getD x 0) = ∑ x ∈ Finset.range v, φ x := by
  have hmap : Set.MapsTo (fun x => al.getD x 0) (Finset.range v) (Finset.range v) :=
    fun x hx => Finset.mem_coe.2 (Finset.mem_range.2
      (mapOK_spec h (Finset.mem_range.1 (Finset.mem_coe.1 hx))).1)
  have hinj : Set.InjOn (fun x => al.getD x 0) (Finset.range v) := fun x hx y hy he =>
    ((mapOK_spec h (Finset.mem_range.1 (Finset.mem_coe.1 hx))).2.2 y
      (Finset.mem_range.1 (Finset.mem_coe.1 hy))).2 he
  exact Finset.sum_nbij (fun x => al.getD x 0) (fun x hx => hmap hx) hinj
    (Finset.surjOn_of_injOn_of_card_le _ hmap hinj le_rfl) fun _ _ => rfl

theorem sol_act (hG : NumGroup v add) {al : List ℕ} (h : mapOK v add q al = true)
    (hsol : Sol v add q Y k lam f) : Sol v add q Y k lam (act v al f) where
  out x hx := by simp [act, Nat.not_lt.2 hx]
  sign x := by
    by_cases hx : x < v
    · simp only [act, hx, ↓reduceIte]; exact hsol.sign _
    · simp only [act, hx, ↓reduceIte]; exact Or.inr (Or.inl rfl)
  cos a := by
    rw [← hsol.cos a, ← sum_perm h (fun x => if q x = a then f x else 0)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    simp only [act, hx', ↓reduceIte, (mapOK_spec h hx').2.1]
  corr g hg := by
    have h0 := mapOK_spec h hG.pos
    have hσ : add (al.getD g 0) (negN v add (al.getD 0 0)) < v :=
      hG.lt _ _ (mapOK_spec h hg).1 (hG.negN_spec h0.1).1
    have e : ∀ x ∈ Finset.range v, act v al f x * act v al f (add x g) =
        (fun y => f y * f (add y (add (al.getD g 0) (negN v add (al.getD 0 0)))))
          (al.getD x 0) := by
      intro x hx
      have hx' := Finset.mem_range.1 hx
      simp only [act, hx', hG.lt _ _ hx' hg, ↓reduceIte, ((mapOK_spec h hx').2.2 g hg).1]
    rw [Finset.sum_congr rfl e,
      sum_perm h (fun y => f y * f (add y (add (al.getD g 0) (negN v add (al.getD 0 0)))))]
    rw [hsol.corr _ hσ]
    have hiff : add (al.getD g 0) (negN v add (al.getD 0 0)) = 0 ↔ g = 0 := by
      constructor
      · intro hs
        exact ((mapOK_spec h hg).2.2 0 hG.pos).2 (hG.eq_of_add_negN (mapOK_spec h hg).1 h0.1 hs)
      · rintro rfl
        rw [hG.comm _ _ h0.1 (hG.negN_spec h0.1).1, (hG.negN_spec h0.1).2]
    by_cases hg0 : g = 0
    · rw [ite_eq_left (hiff.2 hg0), ite_eq_left hg0]
    · rw [ite_eq_right (mt hiff.1 hg0), ite_eq_right hg0]

/-- The images of `f` under the maps, repeatedly. -/
inductive Reach (v : ℕ) (maps : List (List ℕ)) (f : ℕ → ℤ) : (ℕ → ℤ) → Prop
  | refl : Reach v maps f f
  | step {g : ℕ → ℤ} (al : List ℕ) : al ∈ maps → Reach v maps f g → Reach v maps f (act v al g)

theorem exists_min (maps : List (List ℕ)) (key : (ℕ → ℤ) → ℕ) (f : ℕ → ℤ) :
    ∃ g, Reach v maps f g ∧ ∀ g', Reach v maps f g' → key g ≤ key g' := by
  classical
  have h : ∃ n, ∃ g, Reach v maps f g ∧ key g = n := ⟨_, f, .refl, rfl⟩
  obtain ⟨g, hg, hk⟩ := Nat.find_spec h
  exact ⟨g, hg, fun g' hg' => hk ▸ Nat.find_min' h ⟨g', hg', rfl⟩⟩

theorem Reach.sol (hG : NumGroup v add) {maps : List (List ℕ)}
    (hm : ∀ al ∈ maps, mapOK v add q al = true) (hsol : Sol v add q Y k lam f) {g : ℕ → ℤ}
    (h : Reach v maps f g) : Sol v add q Y k lam g := by
  induction h with
  | refl => exact hsol
  | step al hal _ ih => exact sol_act hG (hm al hal) ih

/-! ### The search finds every least lift -/

/-- The cosets assigned before depth `t` mark `y`. -/
def asg (q : ℕ → ℕ) (ord : List ℕ) (t y : ℕ) : Bool := (ord.take t).contains (q y)

theorem asg_succ {ord : List ℕ} {t : ℕ} (ht : t < ord.length) (y : ℕ) :
    asg q ord (t + 1) y = (asg q ord t y || decide (q y = ord.getD t 0)) := by
  have e : ord.take (t + 1) = ord.take t ++ [ord.getD t 0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem ht, List.getD_eq_getElem _ _ ht]; rfl
  simp [asg, e]

theorem not_mem_take {ord : List ℕ} (h : ord.Nodup) {t : ℕ} (ht : t < ord.length) :
    ord.getD t 0 ∉ ord.take t := by
  rw [List.getD_eq_getElem _ _ ht]
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at he
  have := (List.Nodup.getElem_inj_iff h).1 he
  simp only [List.length_take] at hi
  omega

/-- `liftGo` does not cut the least of `f`'s images, so it does not pass. -/
theorem liftGo_false (hG : NumGroup v add) {ord : List ℕ} {maps : List (List ℕ)} {m : ℕ}
    (hsol : Sol v add q Y k lam f) (hord : ord.Nodup)
    (hmaps : ∀ al ∈ maps, mapOK v add q al = true)
    (hmin : ∀ al ∈ maps, key v q ord f ≤ key v q ord (act v al f)) :
    ∀ r t P M acc, t + r ≤ ord.length → Enc v (asg q ord t) f P M →
      AccInv v add (restr v (asg q ord t) f) acc →
      liftGo k lam.toNat (-lam).toNat ((List.range' t r).map (mkStep v add q Y ord maps m)) P M
        acc = false
  | 0, _, _, _, _, _, _, _ => rfl
  | r + 1, t, P, M, acc, hr, hP, hacc => by
    have ht : t < ord.length := by omega
    have hA : asg q ord (t + 1) = fun y => asg q ord t y || decide (q y = ord.getD t 0) :=
      funext (asg_succ ht)
    have hj : ∀ y, q y = ord.getD t 0 → asg q ord t y = false := by
      intro y hy
      simpa [asg, hy] using not_mem_take hord ht
    set st := mkStep v add q Y ord maps m t with hst
    have hP' : Enc v (asg q ord (t + 1)) f
        (newP P st ((cosL v q (ord.getD t 0)).map fun x => code (f x)))
        (newM M st ((cosL v q (ord.getD t 0)).map fun x => code (f x))) := by
      rw [hA]; exact enc_step hP _
    have hdiff : ∀ y, y < v → restr v (asg q ord (t + 1)) f y - restr v (asg q ord t) f y =
        if q y = ord.getD t 0 then f y else 0 := by
      intro y hy
      simp only [restr, hA, hy, true_and]
      by_cases hq : q y = ord.getD t 0
      · simp [hq, hj y hq]
      · simp only [List.getD_eq_getElem?_getD] at hq
        simp [hq]
    have hlp : st.part.length = v := by simp [hst, mkStep]
    have hacc' : AccInv v add (restr v (asg q ord (t + 1)) f)
        (newAcc P M st ((cosL v q (ord.getD t 0)).map fun x => code (f x)) acc) := by
      refine ⟨by simp [newAcc, length_stepAcc, hlp, hacc.1], fun g hg => ?_⟩
      have hgl : g < st.part.length := by rw [hlp]; exact hg
      have hga : g < acc.length := by rw [hacc.1]; exact hg
      rw [accVal, newAcc, stepAcc_getD _ _ _ _ _ _ _ _ hgl hga, updG_spec]
      change accVal acc g + _ = _
      rw [hacc.2 g hg, hG.corr_update hg (restr v (asg q ord t) f)
        (restr v (asg q ord (t + 1)) f)]
      congr 1
      have hpg : st.part.getD g [] =
          (cosL v q (ord.getD t 0)).map fun x => (add x g, add x (negN v add g)) := by
        simp [hst, mkStep, List.getD_eq_getElem?_getD, hg]
      rw [hpg, zip_map_map, sum_cosL]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hy' := Finset.mem_range.1 hy
      rw [hdiff y hy']
      by_cases hq : q y = ord.getD t 0
      · simp only [hq, ↓reduceIte, sgn_code (hsol.sign y), valM_of_enc hsol.sign hP',
          valM_of_enc hsol.sign hP]
      · simp only [List.getD_eq_getElem?_getD] at hq
        simp [hq]
    rw [List.range'_succ, List.map_cons, liftGo, List.all_eq_false]
    have hpm : ((cosL v q (ord.getD t 0)).map fun x => code (f x)) ∈ st.pats := by
      have := mem_patsOf f (cosL v q (ord.getD t 0)) fun x _ => hsol.sign x
      rwa [sum_cosL, hsol.cos] at this
    refine ⟨_, hpm, ?_⟩
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true]
    refine ⟨?_, liftGo_false hG hsol hord hmaps hmin r (t + 1) _ _ _ (by omega) hP' hacc'⟩
    simp only [cutAt, Bool.or_eq_false_iff, Bool.not_eq_false']
    refine ⟨accOK_of _ _ fun i hi1 hi2 => ?_, ?_⟩
    · have hR : st.R.length = v := by simp [hst, mkStep]
      have hi : i < v := hR ▸ hi1
      rw [Int.toNat_sub_toNat_neg, hacc'.2 i hi]
      have hRi : st.R.getD i 0 = OrbitSearch.countTo
          (fun x => !(asg q ord (t + 1) x && asg q ord (t + 1) (add x i))) v := by
        simp [hst, mkStep, List.getD_eq_getElem?_getD, hi, asg]
      rw [hRi]
      exact abs_corr_sub_le hG hsol _ hi
    · by_cases htm : t < m
      · rw [List.any_eq_false]
        intro im him hlt
        simp only [mkStep, htm, ↓reduceIte, List.mem_map] at him
        obtain ⟨al, hal, rfl⟩ := him
        have hzs : ∀ z ∈ flatL (cosL v q) (ord.take (t + 1)),
            z < v ∧ asg q ord (t + 1) z = true := by
          intro z hz
          obtain ⟨a, ha, hz⟩ := (mem_flatL _ _ _).1 hz
          obtain ⟨hzv, hqz⟩ := mem_cosL.1 hz
          exact ⟨hzv, by simp [asg, hqz, ha]⟩
        have e1 : ((flatL (cosL v q) (ord.take (t + 1))).map fun z => al.getD z 0).map
            (codeM (newP P st ((cosL v q (ord.getD t 0)).map fun x => code (f x)))
              (newM M st ((cosL v q (ord.getD t 0)).map fun x => code (f x)))) =
            (flatL (cosL v q) (ord.take (t + 1))).map fun z => codeV (act v al f z) := by
          rw [List.map_map]
          refine List.map_congr_left fun z hz => ?_
          have hs := mapOK_spec (hmaps al hal) (hzs z hz).1
          change codeM _ _ (al.getD z 0) = _
          rw [codeM_of_enc hP' hs.1 (by rw [asg, hs.2.1]; exact (hzs z hz).2)]
          simp [act, (hzs z hz).1]
        have e2 : st.zs.map
            (codeM (newP P st ((cosL v q (ord.getD t 0)).map fun x => code (f x)))
              (newM M st ((cosL v q (ord.getD t 0)).map fun x => code (f x)))) =
            (flatL (cosL v q) (ord.take (t + 1))).map fun z => codeV (f z) :=
          List.map_congr_left fun z hz => codeM_of_enc hP' (hzs z hz).1 (hzs z hz).2
        rw [lexLtM_eq, e1, e2] at hlt
        have hlt' := keyL_lt_of_lexLt _ _ (by simp) (by simp [codeV_lt]) hlt
        have hsplit : flatL (cosL v q) ord = flatL (cosL v q) (ord.take (t + 1)) ++
            flatL (cosL v q) (ord.drop (t + 1)) := by
          rw [← flatL_append, List.take_append_drop]
        have := hmin al hal
        simp only [key, hsplit, List.map_append] at this
        exact absurd this (Nat.not_le.2 (keyL_append_lt hlt' (by simp) (by simp [codeV_lt])))
      · simp [mkStep, htm]

/-- `liftCheck` passes only if `Y` has no lift. -/
theorem liftCheck_sound (hG : NumGroup v add) {ord : List ℕ} {maps : List (List ℕ)} {m : ℕ}
    (hord : ord.Nodup) (hmaps : ∀ al ∈ maps, mapOK v add q al = true)
    (h : liftCheck v add q Y ord maps m k lam = true) (hsol : Sol v add q Y k lam f) : False := by
  obtain ⟨g, hg, hmin⟩ := exists_min (v := v) maps (key v q ord) f
  have hsg := hg.sol hG hmaps hsol
  have := liftGo_false (m := m) hG hsg hord hmaps (fun al hal => hmin _ (.step al hal hg))
    ord.length 0 0 0 ((List.range v).map fun _ => (0, 0)) (by omega)
    (fun y => by simp [asg]) ⟨by simp, fun g hg => by simp [accVal, restr, asg]⟩
  rw [liftCheck, List.range_eq_range'] at h
  rw [h] at this
  exact absurd this (by decide)

/-! ### Splitting the search -/

/-- The nodes `d` levels below a node of `liftGo` that it does not cut: masks and counts. -/
def liftFront (k lp lm : ℕ) :
    ℕ → List Step → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ × List (ℕ × ℕ))
  | 0, _, P, M, acc => [(P, M, acc)]
  | _ + 1, [], P, M, acc => [(P, M, acc)]
  | d + 1, st :: sts, P, M, acc =>
    flatL (fun p => if cutAt k lp lm st P M acc p then [] else
      liftFront k lp lm d sts (newP P st p) (newM M st p) (newAcc P M st p acc)) st.pats

theorem liftGo_of_front {k lp lm : ℕ} : ∀ (d : ℕ) (sts : List Step) (P M : ℕ)
    (acc : List (ℕ × ℕ)), (∀ nd ∈ liftFront k lp lm d sts P M acc,
      liftGo k lp lm (sts.drop d) nd.1 nd.2.1 nd.2.2 = true) →
    liftGo k lp lm sts P M acc = true
  | 0, _, _, _, _, h => h _ List.mem_cons_self
  | _ + 1, [], _, _, _, h => by simp [liftFront, liftGo] at h
  | d + 1, st :: sts, P, M, acc, h => by
    rw [liftGo, List.all_eq_true]
    intro p hp
    by_cases hc : cutAt k lp lm st P M acc p = true
    · simp [hc]
    · rw [Bool.or_eq_true]
      refine Or.inr (liftGo_of_front d sts _ _ _ fun nd hnd => h nd ?_)
      simp only [liftFront, mem_flatL]
      exact ⟨p, hp, by simpa [hc] using hnd⟩

/-- `liftCheck`'s steps. -/
def liftSteps (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (ord : List ℕ)
    (maps : List (List ℕ)) (m : ℕ) : List Step :=
  (List.range ord.length).map (mkStep v add q Y ord maps m)

/-- `liftCheck`'s nodes `d` levels down. -/
def liftNodes (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (ord : List ℕ)
    (maps : List (List ℕ)) (m k : ℕ) (lam : ℤ) (d : ℕ) : List (ℕ × ℕ × List (ℕ × ℕ)) :=
  liftFront k lam.toNat (-lam).toNat d (liftSteps v add q Y ord maps m) 0 0
    ((List.range v).map fun _ => (0, 0))

/-- `liftCheck`'s search from a node `d` levels down. -/
def liftRun (v : ℕ) (add : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (Y : List ℤ) (ord : List ℕ)
    (maps : List (List ℕ)) (m k : ℕ) (lam : ℤ) (d : ℕ) (nd : ℕ × ℕ × List (ℕ × ℕ)) : Bool :=
  liftGo k lam.toNat (-lam).toNat ((liftSteps v add q Y ord maps m).drop d) nd.1 nd.2.1 nd.2.2

/-! ### Rows -/

/-- `ord` has no repeats. -/
def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodup_of_nodupB : ∀ l : List ℕ, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_of_nodupB l h.2⟩
    have := List.contains_iff_mem.2 hm
    rw [h.1] at this
    exact absurd this (by decide)

/-- The quotient `Grp ms → Grp ds` (`quot`) on `Indexed`'s numbers. -/
def qIdx : List ℕ → List ℕ → ℕ → ℕ
  | [_], [d], y => y % d
  | _ :: m' :: ms, d :: d' :: ds, y =>
    qIdx (m' :: ms) (d' :: ds) (y % (m' :: ms).prod) + (d' :: ds).prod * (y / (m' :: ms).prod % d)
  | _, _, _ => 0

theorem size_grp : ∀ (ms : List ℕ) (h : ∀ x ∈ ms, 0 < x),
    @Indexed.size (Grp ms) _ (Grp.indexed ms h) = ms.prod
  | [], _ => rfl
  | [m], _ => by change m = _; simp
  | m :: m' :: ms, h => by
    change m * @Indexed.size (Grp (m' :: ms)) _ (Grp.indexed (m' :: ms) _) = _
    rw [size_grp (m' :: ms)]
    exact List.prod_cons.symm

theorem qIdx_spec : ∀ (ms ds : List ℕ) (hdv : Dvds ds ms) (hm : ∀ x ∈ ms, 0 < x)
    (hd : ∀ x ∈ ds, 0 < x) (x : Grp ms),
    qIdx ms ds (@Indexed.equiv (Grp ms) _ (Grp.indexed ms hm) x : ℕ) =
      (@Indexed.equiv (Grp ds) _ (Grp.indexed ds hd) (quot ms ds hdv x) : ℕ)
  | [], [], _, _, _, _ => by
    change 0 = _
    exact (Nat.lt_one_iff.1 (Fin.isLt _)).symm
  | [m], [d], hdv, hm, hd, x => by
    have : NeZero m := ⟨(hm m List.mem_cons_self).ne'⟩
    have : NeZero d := ⟨(hd d List.mem_cons_self).ne'⟩
    change ZMod.val x % d = ZMod.val (ZMod.cast x : ZMod d)
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  | m :: m' :: ms, d :: d' :: ds, hdv, hm, hd, x => by
    have : NeZero m := ⟨(hm m List.mem_cons_self).ne'⟩
    have : NeZero d := ⟨(hd d List.mem_cons_self).ne'⟩
    have hm' : ∀ x ∈ m' :: ms, 0 < x := fun x hx => hm x (List.mem_cons_of_mem _ hx)
    have hd' : ∀ x ∈ d' :: ds, 0 < x := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have ih := qIdx_spec (m' :: ms) (d' :: ds) hdv.2 hm' hd' x.2
    have hlt := (@Indexed.equiv (Grp (m' :: ms)) _ (Grp.indexed _ hm') x.2).isLt
    have hpos : 0 < @Indexed.size (Grp (m' :: ms)) _ (Grp.indexed _ hm') := by omega
    change qIdx (m :: m' :: ms) (d :: d' :: ds)
        ((@Indexed.equiv (Grp (m' :: ms)) _ (Grp.indexed _ hm') x.2 : ℕ) +
          @Indexed.size (Grp (m' :: ms)) _ (Grp.indexed _ hm') * ZMod.val x.1) =
      (@Indexed.equiv (Grp (d' :: ds)) _ (Grp.indexed _ hd')
          (quot (m' :: ms) (d' :: ds) hdv.2 x.2) : ℕ) +
        @Indexed.size (Grp (d' :: ds)) _ (Grp.indexed _ hd') * ZMod.val (ZMod.cast x.1 : ZMod d)
    rw [qIdx, ← size_grp (m' :: ms) hm', ← size_grp (d' :: ds) hd', Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt,
      Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add, ih, ZMod.cast_eq_val,
      ZMod.val_natCast]
  | [], _ :: _, hdv, _, _, _ => hdv.elim
  | _ :: _, [], hdv, _, _, _ => hdv.elim
  | [_], _ :: _ :: _, hdv, _, _, _ => hdv.2.elim
  | _ :: _ :: _, [_], hdv, _, _, _ => hdv.2.elim

/-- Phase 2 on the row `Grp ms` over `Grp ds`: `ord` without repeats, `Y` no longer than `Grp ds`,
and the search passes. -/
def liftRow (ms ds : List ℕ) (Y : List ℤ) (ord : List ℕ) (maps : List (List ℕ)) (m k : ℕ)
    (lam : ℤ) : Bool :=
  onGrp ms fun v add => nodupB ord && Nat.ble Y.length ds.prod &&
    liftCheck v add (qIdx ms ds) Y ord maps m k lam

/-- The split phase 2's top: at most `N` nodes `d` levels down. -/
def liftTop (ms ds : List ℕ) (Y : List ℤ) (ord : List ℕ) (maps : List (List ℕ)) (m k : ℕ)
    (lam : ℤ) (d N : ℕ) : Bool :=
  onGrp ms fun v add => nodupB ord && Nat.ble Y.length ds.prod &&
    decide ((liftNodes v add (qIdx ms ds) Y ord maps m k lam d).length ≤ N)

/-- The split phase 2's nodes `a, …, b − 1`, `d` levels down, all pass. -/
def liftSlice (ms ds : List ℕ) (Y : List ℤ) (ord : List ℕ) (maps : List (List ℕ)) (m k : ℕ)
    (lam : ℤ) (d a b : ℕ) : Bool :=
  onGrp ms fun v add => sliceAll (liftNodes v add (qIdx ms ds) Y ord maps m k lam d)
    (liftRun v add (qIdx ms ds) Y ord maps m k lam d) a b

theorem liftRow_of_slices {ms ds : List ℕ} {Y : List ℤ} {ord : List ℕ} {maps : List (List ℕ)}
    {m k : ℕ} {lam : ℤ} {d : ℕ} (cuts : List ℕ)
    (htop : liftTop ms ds Y ord maps m k lam d (CosetSearch.lastCut 0 cuts) = true)
    (hsl : CosetSearch.SlicesPass (liftSlice ms ds Y ord maps m k lam d) (0 :: cuts)) :
    liftRow ms ds Y ord maps m k lam = true := by
  obtain ⟨hms, htop⟩ := onGrp_spec htop
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
  let v := @Indexed.size (Grp ms) _ (Grp.indexed ms hms)
  let add := @Indexed.addIdx (Grp ms) _ (Grp.indexed ms hms)
  have e : liftSlice ms ds Y ord maps m k lam d = fun a b =>
      sliceAll (liftNodes v add (qIdx ms ds) Y ord maps m k lam d)
        (liftRun v add (qIdx ms ds) Y ord maps m k lam d) a b := by
    funext a b
    simp only [liftSlice, onGrp, dite_eq_left hms]
    rfl
  rw [e] at hsl
  simp only [liftRow, onGrp, dite_eq_left hms, Bool.and_eq_true]
  refine ⟨htop.1, liftGo_of_front d _ _ _ _ fun nd hnd => ?_⟩
  exact all_of_sliceAll cuts 0 hsl htop.2 nd (by rwa [List.drop_zero])

/-- The maps pass `mapOK` on `Grp ms` over `Grp ds`. -/
def mapsRow (ms ds : List ℕ) (maps : List (List ℕ)) : Bool :=
  onGrp ms fun v add => maps.all (mapOK v add (qIdx ms ds))

theorem contract_translate {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H]
    [DecidableEq H] (φ : G →+ H) (D : G → SignType) (x₀ : G) (h : H) :
    contract φ (fun x => D (x + x₀)) h = contract φ D (h + φ x₀) := by
  unfold contract
  refine Finset.sum_nbij' (· + x₀) (· - x₀) ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;>
    simp_all [map_add, map_sub]

theorem contract_neg {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H]
    [DecidableEq H] (φ : G →+ H) (D : G → SignType) (h : H) :
    contract φ (fun x => -D x) h = -contract φ D h := by
  simp [contract, SignType.coe_neg, Finset.sum_neg_distrib]

/-- No SDS on `Grp ms` has coset sums `Y` along `quot` when `liftRow` passes. -/
theorem false_of_liftRow {ms ds : List ℕ} {k : ℕ} {lam : ℤ} {Y : List ℤ} {ord : List ℕ}
    {maps : List (List ℕ)} {m : ℕ} (hdv : Dvds ds ms) (hd : ∀ x ∈ ds, 0 < x)
    (hmaps : mapsRow ms ds maps = true) (h : liftRow ms ds Y ord maps m k lam = true)
    [Fintype (Grp ms)] (D : Grp ms → SignType) (hD : IsSDS k lam D)
    (hY : ∀ x : Grp ds,
      contract (quot ms ds hdv) D x = Y.getD (@Indexed.equiv _ _ (Grp.indexed ds hd) x : ℕ) 0) :
    False := by
  obtain ⟨hm, h⟩ := onGrp_spec h
  obtain ⟨_, hmaps⟩ := onGrp_spec hmaps
  let _ : Indexed (Grp ms) := Grp.indexed ms hm
  let _ : Indexed (Grp ds) := Grp.indexed ds hd
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hord, hlen⟩, h⟩ := h
  set v := Indexed.size (Grp ms)
  set f : ℕ → ℤ := fun y => if hy : y < v then (D (Indexed.equiv.symm ⟨y, hy⟩) : ℤ) else 0
    with hf
  have hfe : ∀ x : Grp ms, f (Indexed.equiv x : ℕ) = D x := fun x => by
    have hx : (Indexed.equiv x : ℕ) < v := (Indexed.equiv x).isLt
    simp [hf, hx]
  refine liftCheck_sound (numGroup_of_indexed (Grp ms)) (nodup_of_nodupB _ hord)
    (fun al hal => List.all_eq_true.1 hmaps al hal) h (f := f) ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [hf]
    split_ifs with h
    · exact absurd h (Nat.not_lt.2 hx)
    · rfl
  · intro x
    simp only [hf]
    split_ifs
    · rcases D (Indexed.equiv.symm ⟨x, _⟩) with _ | _ | _ <;> simp [IsSign]
    · simp [IsSign]
  · intro a
    rw [← sum_equiv (G := Grp ms) (fun i => if qIdx ms ds i = a then f i else 0)]
    simp only [hfe, qIdx_spec ms ds hdv hm hd]
    by_cases ha : a < Indexed.size (Grp ds)
    · set h0 : Grp ds := Indexed.equiv.symm ⟨a, ha⟩
      have ha0 : a = (Indexed.equiv h0 : ℕ) := by simp [h0]
      rw [ha0, ← hY h0, contract, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hq : quot ms ds hdv x = h0 <;> simp [hq, Fin.val_inj]
    · have hY0 : Y.getD a 0 = 0 := by
        rw [List.getD_eq_default]
        rw [size_grp] at ha
        omega
      rw [hY0]
      refine Finset.sum_eq_zero fun x _ => ite_eq_right fun he => ?_
      have := (Indexed.equiv (quot ms ds hdv x)).isLt
      omega
  · intro g hg
    rw [← sum_equiv (G := Grp ms) (fun i => f i * f (Indexed.addIdx (Grp ms) i g))]
    obtain ⟨g', rfl⟩ : ∃ g' : Grp ms, (Indexed.equiv g' : ℕ) = g :=
      ⟨Indexed.equiv.symm ⟨g, hg⟩, by simp⟩
    simp only [← Indexed.equiv_add, hfe]
    by_cases hg0 : g' = 0
    · subst hg0
      rw [Indexed.equiv_zero, ite_eq_left rfl, ← hD.sum_abs]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [add_zero]
      rcases D x with _ | _ | _ <;> simp
    · rw [ite_eq_right (equiv_ne_zero hg0)]
      exact hD.2 g' hg0

/-- Phase 1 on `Grp ds`. -/
def coverRow (ds : List ℕ) (c k : ℕ) (lam s : ℤ) (L : List (List ℤ)) : Bool :=
  onGrp ds fun n add => cover n add c (k + lam * ((c : ℤ) - 1)) (lam * c) k s L

/-- The split phase 1's top: at most `N` nodes `d + 1` levels down. -/
def coverTop (ds : List ℕ) (c k : ℕ) (lam s : ℤ) (d N : ℕ) : Bool :=
  onGrp ds fun n _ =>
    decide ((coverNodes n c (k + lam * ((c : ℤ) - 1)) s d).length ≤ N)

/-- The split phase 1's nodes `a, …, b − 1`, `d + 1` levels down, all pass. -/
def coverSlice (ds : List ℕ) (c k : ℕ) (lam s : ℤ) (L : List (List ℤ)) (d a b : ℕ) : Bool :=
  onGrp ds fun n add =>
    sliceAll (coverNodes n c (k + lam * ((c : ℤ) - 1)) s d)
      (VNode.run n add c (k + lam * ((c : ℤ) - 1)) (lam * c) k s L) a b

theorem coverRow_of_slices {ds : List ℕ} {c k : ℕ} {lam s : ℤ} {L : List (List ℤ)} {d : ℕ}
    (cuts : List ℕ) (htop : coverTop ds c k lam s d (CosetSearch.lastCut 0 cuts) = true)
    (hsl : CosetSearch.SlicesPass (coverSlice ds c k lam s L d) (0 :: cuts)) :
    coverRow ds c k lam s L = true := by
  obtain ⟨hds, htop⟩ := onGrp_spec htop
  simp only [decide_eq_true_eq] at htop
  let n := @Indexed.size (Grp ds) _ (Grp.indexed ds hds)
  let add := @Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)
  have e : coverSlice ds c k lam s L d = fun a b =>
      sliceAll (coverNodes n c (k + lam * ((c : ℤ) - 1)) s d)
        (VNode.run n add c (k + lam * ((c : ℤ) - 1)) (lam * c) k s L) a b := by
    funext a b
    simp only [coverSlice, onGrp, dite_eq_left hds]
    rfl
  rw [e] at hsl
  simp only [coverRow, onGrp, dite_eq_left hds]
  exact cover_of_nodes fun nd hnd => all_of_sliceAll cuts 0 hsl htop nd (by rwa [List.drop_zero])

/-- A row: `Grp ms` onto `Grp ds` by reduction, fibres of size `c`, `s² = k + λ (v − 1)` (C1). -/
def LiftRow (ms ds : List ℕ) (c k : ℕ) (lam s : ℤ) : Prop :=
  Dvds ds ms ∧ (∀ x ∈ ms, 0 < x) ∧ (∀ x ∈ ds, 0 < x) ∧ ms.prod = c * ds.prod ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1)

instance (ms ds : List ℕ) (c k : ℕ) (lam s : ℤ) : Decidable (LiftRow ms ds c k lam s) := by
  unfold LiftRow; infer_instance

/-- Phase 2 passes for every vector of the list (vector, coset order, depth of the map cut). -/
def LiftsOK (ms ds : List ℕ) (maps : List (List ℕ)) (k : ℕ) (lam : ℤ) :
    List (List ℤ × List ℕ × ℕ) → Prop
  | [] => True
  | (Y, ord, m) :: E => liftRow ms ds Y ord maps m k lam = true ∧ LiftsOK ms ds maps k lam E

theorem LiftsOK.mem {ms ds : List ℕ} {maps : List (List ℕ)} {k : ℕ} {lam : ℤ} :
    ∀ {E : List (List ℤ × List ℕ × ℕ)}, LiftsOK ms ds maps k lam E → ∀ Y ∈ E.map Prod.fst,
      ∃ ord m, liftRow ms ds Y ord maps m k lam = true
  | [], _, _, hY => by simp at hY
  | (Y', ord, m) :: E, h, Y, hY => by
    rcases List.mem_cons.1 hY with rfl | hY
    · exact ⟨ord, m, h.1⟩
    · exact LiftsOK.mem h.2 Y hY

/-- Contraction, then lift: no SDS on `Grp ms` when phase 1 lists the coset-sum vectors on
`Grp ds` (up to translation and negation) and phase 2 rules out a lift of each. -/
theorem not_hasSDS_of_lift {ms ds : List ℕ} {c k : ℕ} {lam s : ℤ} {maps : List (List ℕ)}
    (E : List (List ℤ × List ℕ × ℕ)) (hrow : LiftRow ms ds c k lam s)
    (hcov : coverRow ds c k lam s (E.map Prod.fst) = true) (hmaps : mapsRow ms ds maps = true)
    (hE : LiftsOK ms ds maps k lam E) (inst : Fintype (Grp ms)) :
    ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨hdv, hm, hd, hprod, hss⟩ := hrow
  obtain ⟨_, hcov⟩ := onGrp_spec hcov
  let _ : Fintype (Grp ds) := Grp.fintype ds hd
  let _ : Indexed (Grp ds) := Grp.indexed ds hd
  set φ := quot ms ds hdv
  have hφ := quot_surjective ms ds hdv
  have hcard : Fintype.card (Grp ms) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, Grp.card_eq, hprod]
  have hfib := card_fibre_eq hφ hcard
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card (Grp ms))
      rw [hcard, h0, zero_mul] at this
      omega
    · exact h0
  have hdem : ∀ D' : Grp ms → SignType, IsSDS k lam D' → Demands c k lam (contract φ D') :=
    fun D' hD' =>
    { bound := fun h => by
        have := abs_contract_le φ D' h
        rwa [hfib] at this
      sq := by rw [hD'.contract_sq φ, hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD'.contract_autocorr φ g hg, hfib]
      abs := hD'.sum_abs_contract_le φ
      parity := hD'.sum_abs_contract_parity φ }
  have key : ∀ D' : Grp ms → SignType, IsSDS k lam D' → ∑ h, contract φ D' h = s → False := by
    intro D' hD' hs'
    obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |contract φ D' h|)
      Finset.univ_nonempty
    obtain ⟨x₀, hx₀⟩ := hφ h₀
    have hD'' := hD'.translate x₀
    have hb : ∀ h, contract φ (fun x => D' (x + x₀)) h = contract φ D' (h + h₀) := fun h => by
      rw [contract_translate, hx₀]
    have hdem' := hdem _ hD''
    have hmem := mem_of_cover hcov hdem' (fun h => by
        rw [hb, hb, zero_add]; exact hmax _ (Finset.mem_univ _))
      (by rw [← hs']; exact Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun h => hb h)
    obtain ⟨ord, m, hl⟩ := hE.mem _ hmem
    refine false_of_liftRow hdv hd hmaps hl _ hD'' fun x => ?_
    change contract φ _ x = _
    rw [getD_ofFn _ (Indexed.equiv x).isLt]
    simp
  have hH1 : 1 ≤ Fintype.card (Grp ds) := Fintype.card_pos
  have hsq : (∑ h, contract φ D h) * (∑ h, contract φ D h) = s * s := by
    have hda := hdem D hD
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hda.sq, Finset.sum_congr rfl fun g hg => hda.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hss,
      nsmul_eq_mul, Nat.cast_sub hH1, Grp.card_eq, hprod]
    push_cast
    ring
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key D hD h1
  · refine key _ hD.neg ?_
    simp only [contract_neg, Finset.sum_neg_distrib, h1, neg_neg]

end LiftSearch

end SignedDifferenceSets
