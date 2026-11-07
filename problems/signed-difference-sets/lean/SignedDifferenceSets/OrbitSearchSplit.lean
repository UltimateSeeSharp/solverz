module

public import SignedDifferenceSets.OrbitSearchWitt

/-!
# The orbit exhaust split over several declarations (I5, I16)

`signSearchN` is `OrbitSearch.signSearch` with signs coded in ℕ and its leaf test in ℕ
(`signSearch_of_signSearchN`). `signFrontier` lists the nodes `d` levels below one of its nodes
that its count test keeps, in the order it visits them; `signSearchN` holds at the node when it
holds at each of them (`signSearchN_of_frontier`). On a row `Grp ms`, `orbitTop` checks the
labels and bounds the frontier's length, `orbitSlice` runs the search from the frontier's nodes
`a, …, b − 1`, and `orbitExhaust_of_slices` joins a top and slices `[0, c₁), [c₁, c₂), …`
(`SlicesHold`, built with `.cons` and `.single`) into `orbitExhaust`. `OrbitRowHyps` and
`OrbitRowHyps'` are `OrbitRow` and `OrbitRow'` without the exhaust; `not_hasSDS_of_orbitSlices`
and `not_hasSDS_of_orbitSlices'` take the exhaust separately. Rows are checked by
`decide +kernel` (`solver/orbitsplit.py` writes them).
-/

@[expose] public section

namespace SignedDifferenceSets

namespace OrbitSearch

/-! ### The search with signs coded in ℕ

`signSearchN` is `signSearch` with the signs coded `1` (`+`), `2` (`−`), `0` and its leaf test
in ℕ (`leafKilledN`), so the kernel adds with GMP instead of unfolding `Int`: the correlation
`Σ W c c' σ c σ c'` is the weight of the pairs with equal signs minus the weight of the pairs
with opposite signs (`corrW_decode`). `signSearch_of_signSearchN` transfers it back. -/

/-- A sign coded in ℕ: `1` is `+`, `2` is `−`, anything else `0`. -/
def decodeSign (u : ℕ) : ℤ := if u = 1 then 1 else if u = 2 then -1 else 0

/-- `Σ w` over the weights `row` whose code in `sl` is `e`. Each weight goes through `Nat.mul`,
so the kernel's `Nat` extension puts the shared entry `w` in normal form through its cache
instead of recomputing it at every leaf. -/
def dotCode (e : ℕ) : List ℕ → List ℕ → ℕ
  | w :: row, u :: sl =>
    Nat.add (Nat.mul w (bif Nat.beq u e then 1 else 0)) (dotCode e row sl)
  | _, _ => 0

/-- Over the rows of `W` and the codes `as`: `dotCode e₁` of the rows coded `1`, `dotCode e₂` of
the rows coded `2`, against the codes `sl`. -/
def corrCode (e₁ e₂ : ℕ) (sl : List ℕ) : List (List ℕ) → List ℕ → ℕ
  | row :: W, a :: as =>
    Nat.add (bif Nat.beq a 1 then dotCode e₁ row sl else
        bif Nat.beq a 2 then dotCode e₂ row sl else 0)
      (corrCode e₁ e₂ sl W as)
  | _, _ => 0

/-- Some shift (its weights in `Ws`) misses `λ = lp − lm` for the coded signs `sl`. -/
def leafKilledN (Ws : List (List (List ℕ))) (lp lm : ℕ) (sl : List ℕ) : Bool :=
  Ws.any fun W =>
    !Nat.beq (Nat.add (corrCode 1 2 sl W sl) lm) (Nat.add (corrCode 2 1 sl W sl) lp)

/-- `signSearch` with coded signs and `λ = lp − lm`. -/
def signSearchN (Ws : List (List (List ℕ))) (lp lm P M B : ℕ) :
    List (ℕ × ℕ) → List ℕ → ℕ → ℕ → Bool
  | [], pre, p, m => !(p == P && m == M) || leafKilledN Ws lp lm pre.reverse
  | (c, z) :: cls, pre, p, m =>
    !(decide (p ≤ P) && decide (m ≤ M) &&
        (reachMask B ((c, z) :: cls)).testBit ((P - p) * B + (M - m))) ||
      (signSearchN Ws lp lm P M B cls (1 :: pre) (p + z) m &&
        signSearchN Ws lp lm P M B cls (2 :: pre) p (m + z) &&
        signSearchN Ws lp lm P M B cls (0 :: pre) p m)

theorem dotCode_cons (e w u : ℕ) (row sl : List ℕ) :
    dotCode e (w :: row) (u :: sl) = (if u = e then w else 0) + dotCode e row sl := by
  change Nat.add (Nat.mul w (bif Nat.beq u e then 1 else 0)) (dotCode e row sl) = _
  cases h : Nat.beq u e
  · rw [ite_eq_right (Nat.ne_of_beq_eq_false h)]
    simp
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true h)]
    simp

theorem corrCode_cons (e₁ e₂ : ℕ) (sl row : List ℕ) (W : List (List ℕ)) (a : ℕ)
    (as : List ℕ) : corrCode e₁ e₂ sl (row :: W) (a :: as) =
      (if a = 1 then dotCode e₁ row sl else if a = 2 then dotCode e₂ row sl else 0) +
        corrCode e₁ e₂ sl W as := by
  change Nat.add (bif Nat.beq a 1 then dotCode e₁ row sl else
      bif Nat.beq a 2 then dotCode e₂ row sl else 0) (corrCode e₁ e₂ sl W as) = _
  cases h1 : Nat.beq a 1
  · rw [ite_eq_right (Nat.ne_of_beq_eq_false h1)]
    cases h2 : Nat.beq a 2
    · rw [ite_eq_right (Nat.ne_of_beq_eq_false h2)]
      rfl
    · rw [ite_eq_left (Nat.eq_of_beq_eq_true h2)]
      rfl
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true h1)]
    rfl

theorem sum_zipWith_decode : ∀ row sl : List ℕ,
    (List.zipWith (fun (w : ℕ) (b : ℤ) => (w : ℤ) * b) row (sl.map decodeSign)).sum =
      (dotCode 1 row sl : ℤ) - dotCode 2 row sl
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: row, u :: sl => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
    rw [sum_zipWith_decode row sl, dotCode_cons, dotCode_cons]
    unfold decodeSign
    split_ifs <;> omega

theorem corrW_decode_aux (sl : List ℕ) : ∀ (W : List (List ℕ)) (as : List ℕ),
    (List.zipWith (fun (row : List ℕ) (a : ℤ) =>
        a * (List.zipWith (fun (w : ℕ) (b : ℤ) => (w : ℤ) * b) row (sl.map decodeSign)).sum)
        W (as.map decodeSign)).sum =
      (corrCode 1 2 sl W as : ℤ) - corrCode 2 1 sl W as
  | [], _ => rfl
  | _ :: _, [] => rfl
  | row :: W, a :: as => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
    rw [corrW_decode_aux sl W as, sum_zipWith_decode, corrCode_cons, corrCode_cons]
    unfold decodeSign
    split_ifs <;> push_cast <;> ring

/-- The correlation of decoded signs: equal-sign weight minus opposite-sign weight. -/
theorem corrW_decode (W : List (List ℕ)) (sl : List ℕ) :
    corrW W (sl.map decodeSign) = (corrCode 1 2 sl W sl : ℤ) - corrCode 2 1 sl W sl :=
  corrW_decode_aux sl W sl

theorem leafKilled_of_leafKilledN {Ws : List (List (List ℕ))} {lp lm : ℕ} {lam : ℤ}
    (hl : lam = (lp : ℤ) - lm) {sl : List ℕ} (h : leafKilledN Ws lp lm sl = true) :
    leafKilled Ws lam (sl.map decodeSign) = true := by
  unfold leafKilledN at h
  unfold leafKilled
  simp only [List.any_eq_true] at h ⊢
  obtain ⟨W, hW, hne⟩ := h
  refine ⟨W, hW, ?_⟩
  have hne' : corrCode 1 2 sl W sl + lm ≠ corrCode 2 1 sl W sl + lp := by
    intro heq
    rw [show Nat.add (corrCode 1 2 sl W sl) lm = Nat.add (corrCode 2 1 sl W sl) lp from heq,
      Nat.beq_refl] at hne
    exact absurd hne (by decide)
  rw [bne_iff_ne, corrW_decode, hl]
  omega

theorem decodeSign_one : decodeSign 1 = 1 := by simp [decodeSign]

theorem decodeSign_two : decodeSign 2 = -1 := by simp [decodeSign]

theorem decodeSign_zero : decodeSign 0 = 0 := by simp [decodeSign]

/-- `signSearchN` holding at a node gives `signSearch` at the decoded node. -/
theorem signSearch_of_signSearchN {Ws : List (List (List ℕ))} {lp lm : ℕ} {lam : ℤ}
    (hl : lam = (lp : ℤ) - lm) {P M B : ℕ} :
    ∀ (cls : List (ℕ × ℕ)) (pre : List ℕ) (p m : ℕ),
      signSearchN Ws lp lm P M B cls pre p m = true →
      signSearch Ws lam P M B cls (pre.map decodeSign) p m = true
  | [], pre, p, m, h => by
    rw [signSearchN] at h
    rw [signSearch, ← List.map_reverse]
    cases hc : (p == P && m == M)
    · rfl
    · rw [hc, Bool.not_true, Bool.false_or] at h
      rw [Bool.not_true, Bool.false_or]
      exact leafKilled_of_leafKilledN hl h
  | (c, z) :: cls, pre, p, m, h => by
    rw [signSearchN] at h
    rw [signSearch]
    cases hk : (decide (p ≤ P) && decide (m ≤ M) &&
        (reachMask B ((c, z) :: cls)).testBit ((P - p) * B + (M - m)))
    · rfl
    · rw [hk, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true]
      obtain ⟨⟨h1, h2⟩, h0⟩ := h
      have e1 := signSearch_of_signSearchN hl cls _ _ _ h1
      have e2 := signSearch_of_signSearchN hl cls _ _ _ h2
      have e0 := signSearch_of_signSearchN hl cls _ _ _ h0
      rw [List.map_cons, decodeSign_one] at e1
      rw [List.map_cons, decodeSign_two] at e2
      rw [List.map_cons, decodeSign_zero] at e0
      exact ⟨⟨e1, e2⟩, e0⟩

/-! ### Splitting `signSearchN` at a depth -/

/-- A node of `signSearchN`: its arguments after `Ws lp lm P M B`. -/
structure SignNode where
  /-- The classes left (root, size). -/
  cls : List (ℕ × ℕ)
  /-- The coded signs chosen, reversed. -/
  pre : List ℕ
  /-- The plus elements marked. -/
  p : ℕ
  /-- The minus elements marked. -/
  m : ℕ

/-- `signSearchN` from the node `n`. -/
def SignNode.run (Ws : List (List (List ℕ))) (lp lm P M B : ℕ) (n : SignNode) : Bool :=
  signSearchN Ws lp lm P M B n.cls n.pre n.p n.m

/-- The nodes `d` levels below `signSearchN`'s node that its count test keeps, in the order it
visits them; a complete choice above that depth is one of them. -/
def signFrontier (P M B : ℕ) :
    ℕ → List (ℕ × ℕ) → List ℕ → ℕ → ℕ → List SignNode
  | 0, cls, pre, p, m => [⟨cls, pre, p, m⟩]
  | _ + 1, [], pre, p, m => [⟨[], pre, p, m⟩]
  | d + 1, (c, z) :: cls, pre, p, m =>
    bif decide (p ≤ P) && decide (m ≤ M) &&
        (reachMask B ((c, z) :: cls)).testBit ((P - p) * B + (M - m)) then
      signFrontier P M B d cls (1 :: pre) (p + z) m ++
        signFrontier P M B d cls (2 :: pre) p (m + z) ++
        signFrontier P M B d cls (0 :: pre) p m
    else []

/-- `signSearchN` holds at a node when it holds at every node of its frontier. -/
theorem signSearchN_of_frontier {Ws : List (List (List ℕ))} {lp lm P M B : ℕ} :
    ∀ (d : ℕ) (cls : List (ℕ × ℕ)) (pre : List ℕ) (p m : ℕ),
      (∀ n ∈ signFrontier P M B d cls pre p m, n.run Ws lp lm P M B = true) →
      signSearchN Ws lp lm P M B cls pre p m = true
  | 0, _, _, _, _, h => h _ List.mem_cons_self
  | _ + 1, [], _, _, _, h => h _ List.mem_cons_self
  | d + 1, (c, z) :: cls, pre, p, m, h => by
    rw [signSearchN]
    cases hk : (decide (p ≤ P) && decide (m ≤ M) &&
        (reachMask B ((c, z) :: cls)).testBit ((P - p) * B + (M - m)))
    · rfl
    · simp only [signFrontier, hk, Bool.cond_true, List.mem_append] at h
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
      exact ⟨⟨signSearchN_of_frontier d cls _ _ _ fun n hn => h n (Or.inl (Or.inl hn)),
        signSearchN_of_frontier d cls _ _ _ fun n hn => h n (Or.inl (Or.inr hn))⟩,
        signSearchN_of_frontier d cls _ _ _ fun n hn => h n (Or.inr hn)⟩

/-- The items `a, …, b − 1` of `P` pass `run`. -/
def sliceHolds {α : Type} (P : List α) (run : α → Bool) (a b : ℕ) : Bool :=
  ((P.drop a).take (b - a)).all run

/-- `f a b = true` for all consecutive cuts `a`, `b`. -/
def SlicesHold (f : ℕ → ℕ → Bool) : List ℕ → Prop
  | a :: b :: cuts => f a b = true ∧ SlicesHold f (b :: cuts)
  | _ => True

theorem SlicesHold.cons {f : ℕ → ℕ → Bool} {a b : ℕ} {cuts : List ℕ} (h : f a b = true)
    (h' : SlicesHold f (b :: cuts)) : SlicesHold f (a :: b :: cuts) :=
  show f a b = true ∧ SlicesHold f (b :: cuts) from ⟨h, h'⟩

theorem SlicesHold.single {f : ℕ → ℕ → Bool} {a : ℕ} : SlicesHold f [a] :=
  show True from trivial

/-- The last of `a :: cuts`. -/
def endCut : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, b :: cuts => endCut b cuts

/-- Slices from `a` up to a last cut past the end cover every item from `a` on. -/
theorem all_of_slicesHold {α : Type} {P : List α} {run : α → Bool} :
    ∀ (cuts : List ℕ) (a : ℕ), SlicesHold (sliceHolds P run) (a :: cuts) →
      P.length ≤ endCut a cuts → ∀ n ∈ P.drop a, run n = true
  | [], a, _, hl, n, hn => by
    simp only [endCut] at hl
    rw [List.drop_eq_nil_of_le hl] at hn
    simp at hn
  | b :: cuts, a, h, hl, n, hn => by
    have h' : sliceHolds P run a b = true ∧ SlicesHold (sliceHolds P run) (b :: cuts) := h
    rw [← List.take_append_drop (b - a) (P.drop a), List.mem_append, List.drop_drop] at hn
    rcases hn with hn | hn
    · exact List.all_eq_true.1 h'.1 n hn
    · exact all_of_slicesHold cuts b h'.2 hl n (List.drop_subset_drop_left P (by omega) hn)

end OrbitSearch

open OrbitSearch

/-! ### `orbitCheck` from its frontier -/

/-- `orbitCheck`'s labels and distances as bit fields (`OrbitSearch.scan`). -/
def orbitScan (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ × ℕ :=
  (scan v (Nat.log2 v + 1) (fun y => mulIdx add y t t) v 0 (0, 0, 0)).2

/-- Each number's label: the smallest element of its cycle. -/
def orbitLab (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ → ℕ :=
  field (Nat.log2 v + 1) (orbitScan v add t).1

/-- Each number's distance to its label along the cycle. -/
def orbitDist (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : ℕ → ℕ :=
  field (Nat.log2 v + 1) (orbitScan v add t).2

/-- The plus elements of a set with `k` marked and sign sum `s`. -/
def orbitPlus (k : ℕ) (s : ℤ) : ℕ := (((k : ℤ) + s) / 2).toNat

/-- One shift per nonzero root, with its weights. -/
def orbitWs (v : ℕ) (add : ℕ → ℕ → ℕ) (t : ℕ) : List (List (List ℕ)) :=
  ((roots v (orbitDist v add t)).filter (· != 0)).map
    (weights v add (orbitLab v add t) (roots v (orbitDist v add t)))

/-- `orbitCheck`'s nodes `d` levels down. -/
def orbitNodes (v : ℕ) (add : ℕ → ℕ → ℕ) (k t : ℕ) (s : ℤ) (d : ℕ) : List SignNode :=
  signFrontier (orbitPlus k s) (k - orbitPlus k s) (v + 1) d
    (classes v (orbitLab v add t) (orbitDist v add t)) [] 0 0

/-- `orbitCheck`'s search from a node, with coded signs and `λ = lp − lm`. -/
def orbitRun (v : ℕ) (add : ℕ → ℕ → ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (n : SignNode) :
    Bool :=
  n.run (orbitWs v add t) lam.toNat (-lam).toNat (orbitPlus k s) (k - orbitPlus k s) (v + 1)

theorem orbitCheck_eq (v : ℕ) (add : ℕ → ℕ → ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    orbitCheck v add k lam t s =
      (labelsOK v (fun y => mulIdx add y t t) (orbitLab v add t) (orbitDist v add t) &&
        signSearch (orbitWs v add t) lam (orbitPlus k s) (k - orbitPlus k s) (v + 1)
          (classes v (orbitLab v add t) (orbitDist v add t)) [] 0 0) := by
  simp only [orbitCheck]
  unfold orbitWs orbitLab orbitDist orbitScan orbitPlus
  generalize scan v (Nat.log2 v + 1) (fun y => mulIdx add y t t) v 0 (0, 0, 0) = res
  obtain ⟨_, L, Ds⟩ := res
  rfl

theorem orbitCheck_of_nodes {v : ℕ} {add : ℕ → ℕ → ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {d : ℕ} (hl : labelsOK v (fun y => mulIdx add y t t) (orbitLab v add t) (orbitDist v add t) =
      true)
    (h : ∀ n ∈ orbitNodes v add k t s d, orbitRun v add k lam t s n = true) :
    orbitCheck v add k lam t s = true := by
  rw [orbitCheck_eq, hl, Bool.true_and]
  exact signSearch_of_signSearchN (Int.toNat_sub_toNat_neg lam).symm _ [] 0 0
    (signSearchN_of_frontier d _ _ _ _ h)

/-! ### Rows -/

/-- The split orbit exhaust's top on the row `Grp ms`: the labels pass `labelsOK` and at most
`N` nodes lie `d` levels down. -/
def orbitTop (ms : List ℕ) (k t : ℕ) (s : ℤ) (d N : ℕ) : Bool :=
  if h : ∀ m ∈ ms, 0 < m then
    labelsOK (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
        (fun y => mulIdx (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) y t t)
        (orbitLab (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
          (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) t)
        (orbitDist (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
          (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) t) &&
      decide ((orbitNodes (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
        (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) k t s d).length ≤ N)
  else false

/-- The split orbit exhaust's nodes `a, …, b − 1`, `d` levels down, all pass. -/
def orbitSlice (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (d a b : ℕ) : Bool :=
  if h : ∀ m ∈ ms, 0 < m then
    sliceHolds (orbitNodes (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
        (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) k t s d)
      (orbitRun (@Indexed.size (Grp ms) _ (Grp.indexed ms h))
        (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms h)) k lam t s) a b
  else false

/-- The orbit exhaust from its top and slices `[0, c₁), [c₁, c₂), …` of the nodes `d` levels
down. -/
theorem orbitExhaust_of_slices {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ} {d : ℕ}
    (cuts : List ℕ) (htop : orbitTop ms k t s d (endCut 0 cuts) = true)
    (hsl : SlicesHold (orbitSlice ms k lam t s d) (0 :: cuts)) :
    orbitExhaust ms k lam t s = true := by
  unfold orbitTop at htop
  split_ifs at htop with hms
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
  have e : orbitSlice ms k lam t s d = fun a b =>
      sliceHolds (orbitNodes (@Indexed.size (Grp ms) _ (Grp.indexed ms hms))
          (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms hms)) k t s d)
        (orbitRun (@Indexed.size (Grp ms) _ (Grp.indexed ms hms))
          (@Indexed.addIdx (Grp ms) _ (Grp.indexed ms hms)) k lam t s) a b := by
    funext a b
    simp only [orbitSlice, dite_eq_left hms]
  rw [e] at hsl
  simp only [orbitExhaust, dite_eq_left hms]
  exact orbitCheck_of_nodes htop.1 fun n hn =>
    all_of_slicesHold cuts 0 hsl htop.2 n (by rwa [List.drop_zero])

/-- `OrbitRow` without the orbit exhaust: C9's hypotheses for squarefree `n` and C1's. -/
def OrbitRowHyps (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  0 < (k : ℤ) - lam ∧
    (∀ d ∈ List.range (((k : ℤ) - lam).toNat + 1), 2 ≤ d →
      ((k : ℤ) - lam).toNat % (d * d) ≠ 0) ∧
    Nat.Coprime ms.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ms.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → ∃ f ∈ List.range ms.prod, ∀ m ∈ ms, t % m = p ^ f % m) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1)

instance (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    Decidable (OrbitRowHyps ms k lam t s) := by
  unfold OrbitRowHyps; infer_instance

/-- `OrbitRow'` without the orbit exhaust: C9's hypotheses for every `n` and C1's. -/
def OrbitRowHyps' (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  0 < (k : ℤ) - lam ∧
    Nat.Coprime ms.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ms.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → ∃ f ∈ List.range ms.prod, ∀ m ∈ ms, t % m = p ^ f % m) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1)

instance (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    Decidable (OrbitRowHyps' ms k lam t s) := by
  unfold OrbitRowHyps'; infer_instance

/-- A row meeting `OrbitRowHyps` (squarefree `n`, C15) whose orbit exhaust holds has no SDS. -/
theorem not_hasSDS_of_orbitSlices {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : OrbitRowHyps ms k lam t s) (hex : orbitExhaust ms k lam t s = true)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam :=
  let ⟨h1, h2, h3, h4, h5, h6⟩ := h
  not_hasSDS_of_orbitRow ⟨h1, h2, h3, h4, h5, h6, hex⟩ inst

/-- A row meeting `OrbitRowHyps'` (every `n`, C9 through I13) whose orbit exhaust holds has no
SDS. -/
theorem not_hasSDS_of_orbitSlices' {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : OrbitRowHyps' ms k lam t s) (hex : orbitExhaust ms k lam t s = true)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam :=
  let ⟨h1, h2, h3, h4, h5⟩ := h
  not_hasSDS_of_orbitRow' ⟨h1, h2, h3, h4, h5, hex⟩ inst

end SignedDifferenceSets
