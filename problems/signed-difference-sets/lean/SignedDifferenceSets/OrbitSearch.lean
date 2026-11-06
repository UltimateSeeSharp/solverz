module

public import SignedDifferenceSets.Index
public import SignedDifferenceSets.Loops
public import SignedDifferenceSets.Multiplier
public import SignedDifferenceSets.SelfConjugacyCheck
public import SignedDifferenceSets.Square
public import SignedDifferenceSets.Symmetry

/-!
# The orbit exhaust (I5, E10), checked by the kernel

An SDS `D` on `G` fixed by `x ↦ t x` (C9 supplies such a translate) is constant on the cycles
of `t`: one sign per cycle. `orbitCheck` numbers `G` by `Indexed`, labels the cycles
(`OrbitSearch.scan`, unverified: `labelsOK` checks the labels it returns) and runs through every
sign per class whose counts give `k` marked elements with sign sum `s`, pruned exactly by those
counts (`reachMask`); each choice must miss `λ` at some shift, evaluated from the class-pair
counts (`weights`). `false_of_orbitCheck`: if it holds, no such `D`. `orbitExhaust` is the
check on a row `Grp ms` (`orbitExhaust_sound`); `not_hasSDS_of_orbitRow` adds C9's and C1's
hypotheses, checked by trial division, for `¬ HasSDS`. Rows are checked by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

namespace OrbitSearch

/-! ### The search -/

/-- The number of `i < n` with `p i`. -/
def countTo (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => countTo p n + if p n then 1 else 0

/-- Field `i` of `L` read as `b`-bit fields. -/
def field (b L i : ℕ) : ℕ := (L >>> (b * i)) % 2 ^ b

/-- `2 h + bit · a` with the addition `add`. -/
def dblAdd (add : ℕ → ℕ → ℕ) (a bit h : ℕ) : ℕ :=
  if bit = 0 then add h h else add (add h h) a

/-- `t · a` with the addition `add`, by doubling; `fuel ≥ t` suffices. -/
def mulIdx (add : ℕ → ℕ → ℕ) (a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, t => if t = 0 then 0 else dblAdd add a (t % 2) (mulIdx add a fuel (t / 2))

/-- Marks the cycle of `x` under `sc` from `y`, `j` steps after `x`: label `x`, distance
`v − j`. `acc`: seen elements as bits, labels and distances as `b`-bit fields. -/
def walk (v b : ℕ) (sc : ℕ → ℕ) (x : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 0, _, _, acc => acc
  | fuel + 1, y, j, (seen, L, Ds) =>
    if sc y = x then (seen, L, Ds) else
      walk v b sc x fuel (sc y) (j + 1)
        (seen ||| (1 <<< sc y), L + (x <<< (b * sc y)), Ds + ((v - (j + 1)) <<< (b * sc y)))

/-- `walk` from each `x` on not yet seen (`x` itself: label `x`, distance `0`). -/
def scan (v b : ℕ) (sc : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | 0, _, acc => acc
  | n + 1, x, (seen, L, Ds) =>
    if seen.testBit x then scan v b sc n (x + 1) (seen, L, Ds) else
      scan v b sc n (x + 1) (walk v b sc x v x 0 (seen ||| (1 <<< x), L + (x <<< (b * x)), Ds))

/-- Each `y < v` is a root (distance `0`, its own label) or `sc` takes it, within its class, to
a smaller distance; so each class lies in one cycle of `sc` (`labelsOK_spec`). -/
def labelsOK (v : ℕ) (sc lab dist : ℕ → ℕ) : Bool :=
  allTo (fun y => (dist y == 0 && lab y == y) ||
    (decide (sc y < v) && lab (sc y) == lab y && decide (dist (sc y) < dist y))) v

/-- The roots: the `y < v` at distance `0`. -/
def roots (v : ℕ) (dist : ℕ → ℕ) : List ℕ := (List.range v).filter fun y => dist y == 0

/-- Each root with the size of its class. -/
def classes (v : ℕ) (lab dist : ℕ → ℕ) : List (ℕ × ℕ) :=
  (roots v dist).map fun c => (c, countTo (fun y => lab y == c) v)

/-- One more class, of size `z`: its sign `+`, `−` or `0` adds `z` to `p`, to `m` or nothing;
`(p, m)` is bit `p · W + m`. -/
def reachStep (W z S : ℕ) : ℕ := S ||| (S <<< (z * W)) ||| (S <<< z)

/-- The counts `(p, m)` of plus and minus elements some signs on `cls` reach, as bits. -/
def reachMask (W : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_, z) :: cls => reachStep W z (reachMask W cls)

/-- The `y < v` labelled `c`. -/
def members (v : ℕ) (lab : ℕ → ℕ) (c : ℕ) : List ℕ := (List.range v).filter fun y => lab y == c

/-- `W c c' = #{y < v : lab y = c, lab (y + g) = c'}` for the roots `c`, `c'` in `rs`. -/
def weights (v : ℕ) (add : ℕ → ℕ → ℕ) (lab : ℕ → ℕ) (rs : List ℕ) (g : ℕ) : List (List ℕ) :=
  rs.map fun c => rs.map fun c' => ((members v lab c).filter fun y => lab (add y g) == c').length

/-- `∑_{c, c'} W c c' σ c σ c'`, with the signs `sl` in the order of `W`'s rows and columns. -/
def corrW (W : List (List ℕ)) (sl : List ℤ) : ℤ :=
  (List.zipWith (fun (row : List ℕ) (a : ℤ) =>
    a * (List.zipWith (fun (w : ℕ) (b : ℤ) => (w : ℤ) * b) row sl).sum) W sl).sum

/-- Some shift (its weights in `Ws`) misses `λ` for the signs `sl` on the classes. -/
def leafKilled (Ws : List (List (List ℕ))) (lam : ℤ) (sl : List ℤ) : Bool :=
  Ws.any fun W => corrW W sl != lam

/-- Every sign choice on the classes `cls` (root, size) after the reversed signs `pre`, which
mark `p` plus and `m` minus elements, that completes to `P` plus and `M` minus is killed. -/
def signSearch (Ws : List (List (List ℕ))) (lam : ℤ) (P M B : ℕ) :
    List (ℕ × ℕ) → List ℤ → ℕ → ℕ → Bool
  | [], pre, p, m => !(p == P && m == M) || leafKilled Ws lam pre.reverse
  | (c, z) :: cls, pre, p, m =>
    !(decide (p ≤ P) && decide (m ≤ M) &&
        (reachMask B ((c, z) :: cls)).testBit ((P - p) * B + (M - m))) ||
      (signSearch Ws lam P M B cls (1 :: pre) (p + z) m &&
        signSearch Ws lam P M B cls (-1 :: pre) p (m + z) &&
        signSearch Ws lam P M B cls (0 :: pre) p m)

/-! ### Soundness on the numbers -/

theorem countTo_eq (p : ℕ → Bool) (n : ℕ) :
    countTo p n = ((Finset.range n).filter fun i => p i = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countTo, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

/-- The elements `τ` marks `e`, counted with the class sizes. -/
def cnt (τ : ℕ → ℤ) (e : ℤ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (c, z) :: cls => (if τ c = e then z else 0) + cnt τ e cls

theorem testBit_reachMask (W : ℕ) (τ : ℕ → ℤ) : ∀ cls : List (ℕ × ℕ),
    (reachMask W cls).testBit (cnt τ 1 cls * W + cnt τ (-1) cls) = true
  | [] => by simp [reachMask, cnt]
  | (c, z) :: cls => by
    have ih := testBit_reachMask W τ cls
    simp only [reachMask, reachStep, cnt]
    by_cases h1 : τ c = 1
    · have h2 : ¬ τ c = -1 := by rw [h1]; decide
      rw [ite_eq_left h1, ite_eq_right h2]
      have e : (z + cnt τ 1 cls) * W + (0 + cnt τ (-1) cls) =
          z * W + (cnt τ 1 cls * W + cnt τ (-1) cls) := by ring
      rw [e]
      simp [Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    · by_cases h2 : τ c = -1
      · rw [ite_eq_right h1, ite_eq_left h2]
        have e : (0 + cnt τ 1 cls) * W + (z + cnt τ (-1) cls) =
            z + (cnt τ 1 cls * W + cnt τ (-1) cls) := by ring
        rw [e]
        simp [Nat.testBit_or, Nat.testBit_shiftLeft, ih]
      · rw [ite_eq_right h1, ite_eq_right h2, zero_add, zero_add]
        simp [Nat.testBit_or, ih]

theorem signSearch_sound {Ws : List (List (List ℕ))} {lam : ℤ} {P M B : ℕ} {τ : ℕ → ℤ} :
    ∀ (cls : List (ℕ × ℕ)) (pre : List ℤ) (p m : ℕ),
    signSearch Ws lam P M B cls pre p m = true →
    (∀ c ∈ cls.map Prod.fst, τ c = 1 ∨ τ c = -1 ∨ τ c = 0) →
    p + cnt τ 1 cls = P → m + cnt τ (-1) cls = M →
    leafKilled Ws lam (pre.reverse ++ cls.map fun cz => τ cz.1) = true
  | [], pre, p, m, h, _, hp, hm => by
    simp only [cnt, add_zero] at hp hm
    simpa [signSearch, hp, hm] using h
  | (c, z) :: cls, pre, p, m, h, hτ, hp, hm => by
    have hP : P - p = cnt τ 1 ((c, z) :: cls) := by omega
    have hM : M - m = cnt τ (-1) ((c, z) :: cls) := by omega
    have hr := testBit_reachMask B τ ((c, z) :: cls)
    rw [← hP, ← hM] at hr
    simp only [signSearch, hr, show p ≤ P by omega, show m ≤ M by omega, decide_true, Bool.and_self,
      Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h0⟩ := h
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hτ
    simp only [cnt] at hp hm
    have hext (e : ℤ) (he : τ c = e) : (e :: pre).reverse ++ cls.map (fun cz => τ cz.1) =
        pre.reverse ++ ((c, z) :: cls).map fun cz => τ cz.1 := by
      simp [he]
    rcases hτ.1 with hc | hc | hc
    · have hn : ¬ τ c = -1 := by rw [hc]; decide
      rw [ite_eq_left hc] at hp
      rw [ite_eq_right hn] at hm
      rw [← hext 1 hc]
      exact signSearch_sound cls _ _ _ h1 hτ.2 (by omega) (by omega)
    · have hn : ¬ τ c = 1 := by rw [hc]; decide
      rw [ite_eq_right hn] at hp
      rw [ite_eq_left hc] at hm
      rw [← hext (-1) hc]
      exact signSearch_sound cls _ _ _ h2 hτ.2 (by omega) (by omega)
    · have hn1 : ¬ τ c = 1 := by rw [hc]; decide
      have hn2 : ¬ τ c = -1 := by rw [hc]; decide
      rw [ite_eq_right hn1] at hp
      rw [ite_eq_right hn2] at hm
      rw [← hext 0 hc]
      exact signSearch_sound cls _ _ _ h0 hτ.2 (by omega) (by omega)

theorem length_filter_range (p : ℕ → Bool) : ∀ n,
    ((List.range n).filter p).length = countTo p n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p n, countTo]
    cases h : p n <;> simp [List.filter, h]

theorem corrW_map {rs : List ℕ} (hrs : rs.Nodup) (w : ℕ → ℕ → ℕ) (f : ℕ → ℤ) :
    corrW (rs.map fun c => rs.map fun c' => w c c') (rs.map f) =
      ∑ c ∈ rs.toFinset, ∑ c' ∈ rs.toFinset, f c * ((w c c' : ℤ) * f c') := by
  simp only [corrW, List.zipWith_map, List.zipWith_self]
  rw [← List.sum_toFinset _ hrs]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← List.sum_toFinset _ hrs, Finset.mul_sum]

/-- The weights give the correlation at `g` of any `f` constant on the classes. -/
theorem corrW_weights {v : ℕ} {add : ℕ → ℕ → ℕ} {lab : ℕ → ℕ} {rs : List ℕ} {g : ℕ}
    (hrs : rs.Nodup) (hlab : ∀ y < v, lab y ∈ rs) (hadd : ∀ y < v, lab (add y g) ∈ rs)
    (f : ℕ → ℤ) :
    corrW (weights v add lab rs g) (rs.map f) =
      ∑ y ∈ Finset.range v, f (lab y) * f (lab (add y g)) := by
  have hcnt (c c' : ℕ) :
      ((((members v lab c).filter fun y => lab (add y g) == c').length : ℕ) : ℤ) =
        ∑ y ∈ Finset.range v, if lab y = c ∧ lab (add y g) = c' then 1 else 0 := by
    rw [members, List.filter_filter, length_filter_range, countTo_eq, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h1 : lab y = c <;> by_cases h2 : lab (add y g) = c' <;> simp [h1, h2]
  rw [weights, corrW_map hrs]
  calc
    _ = ∑ c ∈ rs.toFinset, ∑ c' ∈ rs.toFinset, ∑ y ∈ Finset.range v,
          if lab y = c ∧ lab (add y g) = c' then f c * f c' else 0 := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      rw [hcnt, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    _ = ∑ c ∈ rs.toFinset, ∑ y ∈ Finset.range v, ∑ c' ∈ rs.toFinset,
          if lab y = c ∧ lab (add y g) = c' then f c * f c' else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y ∈ Finset.range v, ∑ c ∈ rs.toFinset, ∑ c' ∈ rs.toFinset,
          if lab y = c ∧ lab (add y g) = c' then f c * f c' else 0 := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hy' := Finset.mem_range.1 hy
      calc
        _ = ∑ c ∈ rs.toFinset, if lab y = c then
              ∑ c' ∈ rs.toFinset, (if lab (add y g) = c' then f c * f c' else 0) else 0 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases h : lab y = c <;> simp [h]
        _ = _ := by
          rw [Finset.sum_ite_eq_of_mem _ _ _ (List.mem_toFinset.2 (hlab y hy')),
            Finset.sum_ite_eq_of_mem _ _ _ (List.mem_toFinset.2 (hadd y hy'))]

/-- After `labelsOK`, each label is a root, and `f` fixed by `sc` takes its root's value. -/
theorem labelsOK_spec {v : ℕ} {sc lab dist : ℕ → ℕ} (h : labelsOK v sc lab dist = true)
    {f : ℕ → ℤ} (hinv : ∀ y < v, f (sc y) = f y) :
    ∀ y < v, lab y < v ∧ dist (lab y) = 0 ∧ f y = f (lab y) := by
  suffices H : ∀ n y, dist y = n → y < v → lab y < v ∧ dist (lab y) = 0 ∧ f y = f (lab y) from
    fun y hy => H _ y rfl hy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hn hy
    have hy' := (allTo_iff _ _).1 h y hy
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy'
    rcases hy' with ⟨hd, hl⟩ | ⟨⟨hsc, hl⟩, hd⟩
    · rw [hl]
      exact ⟨hy, hn ▸ hd, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ih _ (hn ▸ hd) (sc y) rfl hsc
      rw [hl] at h1 h2 h3
      exact ⟨h1, h2, by rw [← hinv y hy, h3]⟩

theorem cnt_map (τ : ℕ → ℤ) (e : ℤ) (sz : ℕ → ℕ) : ∀ l : List ℕ,
    cnt τ e (l.map fun c => (c, sz c)) = (l.map fun c => if τ c = e then sz c else 0).sum
  | [] => rfl
  | c :: l => by simp [cnt, cnt_map τ e sz l]

/-- The search over the classes of `labelsOK`'s labels, with `P` plus and `M` minus elements. -/
theorem search_sound {v : ℕ} {add : ℕ → ℕ → ℕ} {sc lab dist : ℕ → ℕ} {lam : ℤ} {P M B : ℕ}
    (hl : labelsOK v sc lab dist = true)
    (hg : signSearch (((roots v dist).filter (· != 0)).map (weights v add lab (roots v dist)))
      lam P M B (classes v lab dist) [] 0 0 = true)
    (f : ℕ → ℤ) (hf : ∀ y < v, f y = 1 ∨ f y = -1 ∨ f y = 0) (hinv : ∀ y < v, f (sc y) = f y)
    (hP : ((Finset.range v).filter fun y => f y = 1).card = P)
    (hM : ((Finset.range v).filter fun y => f y = -1).card = M)
    (hadd : ∀ y g, y < v → g < v → add y g < v)
    (hcorr : ∀ g, 0 < g → g < v → ∑ y ∈ Finset.range v, f y * f (add y g) = lam) : False := by
  have hlab := labelsOK_spec hl hinv
  have hroot : ∀ y < v, lab y ∈ roots v dist := fun y hy => by
    simp only [roots, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨(hlab y hy).1, (hlab y hy).2.1⟩
  have hkeys : (classes v lab dist).map Prod.fst = roots v dist := by
    simp [classes, List.map_map, Function.comp_def]
  have hnodup : (roots v dist).Nodup := List.nodup_range.filter _
  have hcnt (e : ℤ) :
      cnt f e (classes v lab dist) = ((Finset.range v).filter fun y => f y = e).card := by
    have hmaps : Set.MapsTo lab ↑((Finset.range v).filter fun y => f y = e)
        ↑(roots v dist).toFinset := fun y hy => by
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy
      exact List.mem_toFinset.2 (hroot y hy.1)
    rw [classes, cnt_map, ← List.sum_toFinset _ hnodup, Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [countTo_eq, Finset.filter_filter]
    split_ifs with hce
    · congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, beq_iff_eq]
      constructor
      · rintro ⟨hy, hyc⟩
        exact ⟨hy, by rw [(hlab y hy).2.2, hyc, hce], hyc⟩
      · rintro ⟨hy, -, hyc⟩
        exact ⟨hy, hyc⟩
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro y hy ⟨hfe, hyc⟩
      apply hce
      rw [← hyc, ← (hlab y (Finset.mem_range.1 hy)).2.2]
      exact hfe
  have hk := signSearch_sound (τ := f) _ _ _ _ hg
    (by
      rw [hkeys]
      intro c hc
      simp only [roots, List.mem_filter, List.mem_range] at hc
      exact hf c hc.1)
    (by rw [zero_add, hcnt, hP]) (by rw [zero_add, hcnt, hM])
  have hsl : ([] : List ℤ).reverse ++ (classes v lab dist).map (fun cz => f cz.1) =
      (roots v dist).map f := by
    rw [List.reverse_nil, List.nil_append, ← hkeys, List.map_map]
    rfl
  rw [hsl] at hk
  simp only [leafKilled, List.any_eq_true, List.mem_map, bne_iff_ne, ne_eq] at hk
  obtain ⟨_, ⟨g, hgm, rfl⟩, hne⟩ := hk
  have hgv : g < v ∧ g ≠ 0 := by
    simp only [roots, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hgm
    exact ⟨hgm.1.1, hgm.2⟩
  apply hne
  rw [corrW_weights hnodup hroot (fun y hy => hroot _ (hadd y g hy hgv.1)) f,
    ← hcorr g (Nat.pos_of_ne_zero hgv.2) hgv.1]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_range] at hy
  rw [← (hlab y hy).2.2, ← (hlab _ (hadd y g hy hgv.1)).2.2]

end OrbitSearch

open OrbitSearch

/-- The orbit exhaust on the numbers `0, …, v − 1` with addition `add`: `true` when no `f`
fixed by `t`, with signs, `k` marked, sign sum `s` and correlation `λ` at every shift exists
(`orbitCheck_sound`). -/
def orbitCheck (v : ℕ) (add : ℕ → ℕ → ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Bool :=
  let sc := fun y => mulIdx add y t t
  let b := Nat.log2 v + 1
  match scan v b sc v 0 (0, 0, 0) with
  | (_, L, Ds) =>
    let P := (((k : ℤ) + s) / 2).toNat
    let rs := roots v (field b Ds)
    labelsOK v sc (field b L) (field b Ds) &&
      signSearch ((rs.filter (· != 0)).map (weights v add (field b L) rs)) lam P (k - P)
        (v + 1) (classes v (field b L) (field b Ds)) [] 0 0

/-- `orbitCheck` is `true` only if no `f` on `0, …, v − 1` fixed by `t` (through `mulIdx`) has
signs, `k` nonzero values, sum `s` and correlation `λ` at every shift `0 < g < v`. -/
theorem orbitCheck_sound {v : ℕ} {add : ℕ → ℕ → ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : orbitCheck v add k lam t s = true) (f : ℕ → ℤ)
    (hf : ∀ y < v, f y = 1 ∨ f y = -1 ∨ f y = 0)
    (hinv : ∀ y < v, f (mulIdx add y t t) = f y)
    (hk : ((Finset.range v).filter fun y => f y ≠ 0).card = k)
    (hs : ∑ y ∈ Finset.range v, f y = s)
    (hadd : ∀ y g, y < v → g < v → add y g < v)
    (hcorr : ∀ g, 0 < g → g < v → ∑ y ∈ Finset.range v, f y * f (add y g) = lam) : False := by
  have hterm : ∀ y ∈ Finset.range v,
      f y = (if f y = 1 then 1 else 0 : ℤ) - (if f y = -1 then 1 else 0) ∧
        (if f y ≠ 0 then 1 else 0 : ℤ) =
          (if f y = 1 then 1 else 0) + (if f y = -1 then 1 else 0) := by
    intro y hy
    rcases hf y (Finset.mem_range.1 hy) with h | h | h <;> simp [h]
  have hk' : (k : ℤ) = (((Finset.range v).filter fun y => f y = 1).card : ℤ) +
      (((Finset.range v).filter fun y => f y = -1).card : ℤ) := by
    rw [← hk, Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.natCast_card_filter,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y hy => (hterm y hy).2
  have hs' : s = (((Finset.range v).filter fun y => f y = 1).card : ℤ) -
      (((Finset.range v).filter fun y => f y = -1).card : ℤ) := by
    rw [← hs, Finset.natCast_card_filter, Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y hy => (hterm y hy).1
  have hP : (((k : ℤ) + s) / 2).toNat = ((Finset.range v).filter fun y => f y = 1).card := by
    have : ((k : ℤ) + s) / 2 = (((Finset.range v).filter fun y => f y = 1).card : ℤ) := by
      rw [hk', hs']
      omega
    rw [this, Int.toNat_natCast]
  have hM : k - (((k : ℤ) + s) / 2).toNat = ((Finset.range v).filter fun y => f y = -1).card := by
    rw [hP]
    omega
  simp only [orbitCheck] at h
  generalize scan _ _ _ _ _ _ = res at h
  obtain ⟨_, L, Ds⟩ := res
  simp only [Bool.and_eq_true] at h
  exact search_sound h.1 h.2 f hf hinv hP.symm hM.symm hadd hcorr

/-! ### Soundness on a group -/

section Group

variable {G : Type*} [AddCommGroup G] [Indexed G]

/-- `t · x` on `Indexed`'s numbers. -/
theorem Indexed.equiv_nsmul (x : G) : ∀ fuel t : ℕ, t ≤ fuel →
    (Indexed.equiv (t • x) : ℕ) = mulIdx (Indexed.addIdx G) (Indexed.equiv x) fuel t
  | 0, t, ht => by
    obtain rfl : t = 0 := by omega
    rw [zero_nsmul, Indexed.equiv_zero]
    rfl
  | fuel + 1, t, ht => by
    rw [mulIdx]
    split_ifs with h0
    · rw [h0, zero_nsmul, Indexed.equiv_zero]
    · have ih := Indexed.equiv_nsmul x fuel (t / 2) (by omega)
      have hx : t • x = (t / 2) • x + (t / 2) • x + (t % 2) • x := by
        rw [← add_nsmul, ← add_nsmul]
        congr 1
        omega
      rw [hx, dblAdd]
      split_ifs with hb
      · rw [hb, zero_nsmul, add_zero, Indexed.equiv_add, ih]
      · rw [show t % 2 = 1 by omega, one_nsmul, Indexed.equiv_add, Indexed.equiv_add, ih]

variable [Fintype G]

/-- If `orbitCheck` holds on `G`'s numbers, no SDS (|G|, k, λ) on `G` is fixed by `x ↦ t x`
with sign sum `s`. -/
theorem false_of_orbitCheck {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : orbitCheck (Indexed.size G) (Indexed.addIdx G) k lam t s = true) {D : G → SignType}
    (hD : IsSDS k lam D) (ht : ∀ x, D (t • x) = D x) (hs : ∑ x, (D x : ℤ) = s) : False := by
  classical
  let f : ℕ → ℤ := fun y =>
    if hy : y < Indexed.size G then (D (Indexed.equiv.symm ⟨y, hy⟩) : ℤ) else 0
  have hfe (x : G) : f (Indexed.equiv x) = D x := by simp [f]
  have hsurj (y : ℕ) (hy : y < Indexed.size G) : ∃ x : G, (Indexed.equiv x : ℕ) = y :=
    ⟨Indexed.equiv.symm ⟨y, hy⟩, by simp⟩
  have hcast (a : SignType) : ((a : ℤ) ≠ 0) = (a ≠ 0) := by cases a <;> simp
  refine orbitCheck_sound h f (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ (fun y g hy hg => ?_)
    (fun g hg0 hg => ?_)
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [hfe]
    cases D x <;> simp
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [← Indexed.equiv_nsmul x t t le_rfl, hfe, hfe, ht]
  · rw [← hD.1]
    have h1 := sum_equiv (G := G) fun y => if f y ≠ 0 then (1 : ℤ) else 0
    simp only [hfe, hcast] at h1
    rw [← Finset.natCast_card_filter, ← Finset.natCast_card_filter] at h1
    exact_mod_cast h1.symm
  · rw [← hs, ← sum_equiv (G := G) f]
    simp only [hfe]
  · obtain ⟨x, rfl⟩ := hsurj y hy
    obtain ⟨x', rfl⟩ := hsurj g hg
    rw [← Indexed.equiv_add]
    exact (Indexed.equiv _).isLt
  · obtain ⟨gG, rfl⟩ := hsurj g hg
    have hne : gG ≠ 0 := by
      rintro rfl
      rw [Indexed.equiv_zero] at hg0
      omega
    rw [← hD.2 gG hne,
      ← sum_equiv (G := G) fun y => f y * f (Indexed.addIdx G y (Indexed.equiv gG))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Indexed.equiv_add, hfe, hfe]

end Group

/-! ### Rows -/

/-- `Grp ms` numbered by `Indexed`, built by the same recursion as `Grp`. -/
@[instance_reducible]
def Grp.indexed : (ms : List ℕ) → (∀ m ∈ ms, 0 < m) → Indexed (Grp ms)
  | [], _ => inferInstanceAs (Indexed (ZMod 1))
  | [m], h =>
    have : NeZero m := ⟨(h m List.mem_cons_self).ne'⟩
    inferInstanceAs (Indexed (ZMod m))
  | m :: m' :: ms, h =>
    have : NeZero m := ⟨(h m List.mem_cons_self).ne'⟩
    let _ : Indexed (Grp (m' :: ms)) :=
      Grp.indexed (m' :: ms) fun x hx => h x (List.mem_cons_of_mem _ hx)
    inferInstanceAs (Indexed (ZMod m × Grp (m' :: ms)))

/-- The orbit exhaust on the row `Grp ms` (every factor positive) with multiplier `t` and sign
sum `s`. -/
def orbitExhaust (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Bool :=
  if h : ∀ m ∈ ms, 0 < m then
    orbitCheck (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
      (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) k lam t s
  else false

/-- The orbit exhaust is sound: if it holds, no SDS on `Grp ms` is fixed by `x ↦ t x` and has
sign sum `s`. -/
theorem orbitExhaust_sound {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : orbitExhaust ms k lam t s = true) (inst : Fintype (Grp ms)) :
    ¬ ∃ D : Grp ms → SignType, IsSDS k lam D ∧ (∀ x, D (t • x) = D x) ∧
      ∑ x, (D x : ℤ) = s := by
  rintro ⟨D, hD, ht, hs⟩
  unfold orbitExhaust at h
  split_ifs at h with hms
  exact @false_of_orbitCheck _ _ (Grp.indexed ms hms) _ _ _ _ _ h _ hD ht hs

theorem zmod_nsmul_eq_of_mod {a b m : ℕ} (h : a % m = b % m) (x : ZMod m) : a • x = b • x := by
  rw [nsmul_eq_mul, nsmul_eq_mul, (ZMod.natCast_eq_natCast_iff' a b m).2 h]

/-- `a • x = b • x` on `Grp ms` when `a ≡ b` modulo every factor. -/
theorem Grp.nsmul_eq_of_mod {a b : ℕ} :
    (ms : List ℕ) → (∀ m ∈ ms, a % m = b % m) → ∀ x : Grp ms, a • x = b • x
  | [], _, _ => Subsingleton.elim (α := ZMod 1) _ _
  | [m], h, x => zmod_nsmul_eq_of_mod (h m List.mem_cons_self) (x : ZMod m)
  | m :: m' :: ms, h, x =>
    Prod.ext (zmod_nsmul_eq_of_mod (h m List.mem_cons_self) (x.1 : ZMod m))
      (Grp.nsmul_eq_of_mod (m' :: ms) (fun d hd => h d (List.mem_cons_of_mem _ hd)) x.2)

theorem isPrimeTD_of_prime {p : ℕ} (hp : p.Prime) : IsPrimeTD p :=
  ⟨hp.two_le, fun d hd h2 hpd => by
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hpd) with h | h
    · omega
    · exact absurd (List.mem_range.1 hd) (by omega)⟩

/-- A row `Grp ms`, `k`, `λ` with multiplier `t` and sign sum `s` meets C9's hypotheses
(`n = k − λ` positive, squarefree and prime to `v`; `t` prime to `v` and `≡ p^f` on every
factor for each prime `p ∣ n`) and C1's (`s² = k + λ (v − 1)`), and the orbit exhaust for `s`
holds. All by trial division, for `decide +kernel`. -/
def OrbitRow (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  0 < (k : ℤ) - lam ∧
    (∀ d ∈ List.range (((k : ℤ) - lam).toNat + 1), 2 ≤ d →
      ((k : ℤ) - lam).toNat % (d * d) ≠ 0) ∧
    Nat.Coprime ms.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ms.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → ∃ f ∈ List.range ms.prod, ∀ m ∈ ms, t % m = p ^ f % m) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1) ∧ orbitExhaust ms k lam t s = true

instance (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Decidable (OrbitRow ms k lam t s) := by
  unfold OrbitRow; infer_instance

/-- A row meeting `OrbitRow` has no SDS: C9 gives a translate fixed by `t`, its sign sum is
`±s` (C1), and the negation (C2) turns `−s` into `s`. -/
theorem not_hasSDS_of_orbitRow {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : OrbitRow ms k lam t s) (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨hn, hsqf, hcop, htv, hpf, hs, hex⟩ := h
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  have hpos : 0 < ((k : ℤ) - lam).toNat := by omega
  have hcard : Fintype.card (Grp ms) = ms.prod := Grp.card_eq ms
  have hsq : Squarefree ((k : ℤ) - lam) := by
    rw [hnz, Int.squarefree_natCast]
    intro x hx
    rw [Nat.isUnit_iff]
    by_contra hx1
    rcases Nat.lt_or_ge x 2 with hx2 | hx2
    · obtain rfl : x = 0 := by omega
      rw [zero_mul, zero_dvd_iff] at hx
      omega
    · have hle : x ≤ ((k : ℤ) - lam).toNat :=
        (Nat.le_mul_self x).trans (Nat.le_of_dvd hpos hx)
      exact hsqf x (List.mem_range.2 (by omega)) hx2 (Nat.mod_eq_zero_of_dvd hx)
  have hcopZ : IsCoprime (Fintype.card (Grp ms) : ℤ) ((k : ℤ) - lam) := by
    rw [hcard, hnz]
    exact Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨a, ha⟩ := hD.exists_translate_fixed hsq hcopZ
  have hfix := ha t (by rw [hcard]; exact htv) fun p hp hpn => by
    rw [hnz, Int.natCast_dvd_natCast] at hpn
    obtain ⟨f, -, hf⟩ := hpf p (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn)))
      (Nat.mod_eq_zero_of_dvd hpn) (isPrimeTD_of_prime hp)
    exact ⟨f, Grp.nsmul_eq_of_mod ms hf⟩
  have hD' := hD.translate a
  have hsum := hD'.sum_sq
  rw [hcard] at hsum
  have hss : (∑ x, (D (x + a) : ℤ)) * (∑ x, (D (x + a) : ℤ)) = s * s := by
    rw [← sq, hsum, hs]
  rcases mul_self_eq_mul_self_iff.1 hss with h1 | h1
  · exact orbitExhaust_sound hex inst ⟨_, hD', hfix, h1⟩
  · refine orbitExhaust_sound hex inst ⟨_, hD'.neg, fun x => congrArg Neg.neg (hfix x), ?_⟩
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

/-! ### Tests -/

-- N1147, (79, 40, 2) in C₇₉: `t = 2` generates C9's M (the squares), `s = 14`; 3 orbits.
example : orbitExhaust [79] 40 2 2 14 = true := by decide +kernel

/-- N1147 through C9. -/
example : ¬ HasSDS (ZMod 79) 40 2 :=
  not_hasSDS_of_orbitRow (ms := [79]) (t := 2) (s := 14) (by decide +kernel) _

-- N6 exists (Paley and zero, (11, 6, 1)): `t = 5`, `s = 4`, so the exhaust must fail.
example : orbitExhaust [11] 6 1 5 4 = false := by decide +kernel

-- N24 exists ((19, 10, 3), Paley and zero): `t = 7`, `s = 8`.
example : orbitExhaust [19] 10 3 7 8 = false := by decide +kernel

-- N2 exists ((9, 8, −1) in C₃ × C₃): with `t = 1` every set is fixed; `s = 0`.
example : orbitExhaust [3, 3] 8 (-1) 1 0 = false := by decide +kernel

-- N30, (20, 11, 2) in C₂ × C₁₀ (E10: none): `t = 3`, `s = 7`; 72 sign choices reach the leaves.
example : orbitExhaust [2, 10] 11 2 3 7 = true := by decide +kernel

end SignedDifferenceSets
