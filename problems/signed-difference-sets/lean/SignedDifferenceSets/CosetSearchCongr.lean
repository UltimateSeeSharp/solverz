module

public import SignedDifferenceSets.CosetSearchSelfConj

/-!
# The coset search with C5's congruence as a filter (I18)

For a prime `p` self-conjugate on `H` with `p^(2j) ∣ n`, C5 makes the coset sums agree mod
`q = p^j`; so do their shifted values `u = x + c`. `valSearchR … q res` is `valSearch` trying
only values `u ≡ res (mod q)`; a row (`CosetRowCongr`: `CosetRowSelfConj` and such `p`, `j`)
holds when the search passes for every residue `res < q` (`not_hasSDS_of_cosetRowCongr`, the
proof of `not_hasSDS_of_cosetRowSelfConj` with the residue of the fixed translate). The
definitions and proofs copy `CosetSearch.lean`'s with the filter added.
-/

@[expose] public section

namespace SignedDifferenceSets

namespace CosetSearch

open OrbitSearch

/-- `keepN` and the filter `u ≡ res (mod q)` on the shifted value `u`. -/
def keepR (C QN ST z rem su sq q res u : ℕ) : Bool :=
  keepN C QN ST z rem su sq u && Nat.beq (u % q) res

/-- `valSearch` trying only shifted values `u ≡ res (mod q)`. -/
def valSearchR (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) (q res : ℕ) :
    List (ℕ × ℕ) → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], _, pre, su, sq, ab, mm =>
    !leafOK QN k ST su sq ab mm || leafKilledN Ws T C pre.reverse
  | (_, z) :: cls, rem, pre, su, sq, ab, mm =>
    allNat (fun u => !keepR C QN ST z rem su sq q res u ||
        valSearchR Ws C QN k ST T q res cls (Nat.sub rem z) (u :: pre)
          (Nat.add su (Nat.mul z u)) (Nat.add sq (Nat.mul z (Nat.mul (ndist C u) (ndist C u))))
          (Nat.add ab (Nat.mul z (ndist C u))) (Nat.add mm (Nat.mul z (mmN C u))))
      (spanN C ST z rem su).1 (spanN C ST z rem su).2

theorem valSearchR_cons (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) (q res r z : ℕ)
    (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ) :
    valSearchR Ws C QN k ST T q res ((r, z) :: cls) rem pre su sq ab mm =
      allNat (fun u => !keepR C QN ST z rem su sq q res u ||
          valSearchR Ws C QN k ST T q res cls (rem - z) (u :: pre) (su + z * u)
            (sq + z * (ndist C u * ndist C u)) (ab + z * ndist C u) (mm + z * mmN C u))
        (spanN C ST z rem su).1 (spanN C ST z rem su).2 := rfl

/-- `valSearchR` is sound: a choice `τ` on the classes with shifted values `≡ res (mod q)` that
meets the demands is killed at some shift. -/
theorem valSearchR_sound {Ws : List (List (List ℕ))} {C QN k ST : ℕ} {T : ℤ} {q res : ℕ}
    (τ : ℕ → ℤ) :
    ∀ (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ),
      valSearchR Ws C QN k ST T q res cls rem pre su sq ab mm = true →
      rem = wsumN (fun _ => 1) cls → (∀ cz ∈ cls, |τ cz.1| ≤ C) →
      (∀ cz ∈ cls, shiftVal C (τ cz.1) % q = res) →
      su + wsumN (fun r => shiftVal C (τ r)) cls = ST →
      sq + wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls = QN →
      ab + wsumN (fun r => (τ r).natAbs) cls ≤ k →
      (k - (ab + wsumN (fun r => (τ r).natAbs) cls)) % 2 = 0 →
      k ≤ mm + wsumN (fun r => mmN C (shiftVal C (τ r))) cls →
      leafKilled Ws T (unshift C (pre.reverse ++ cls.map fun cz => shiftVal C (τ cz.1))) = true
  | [], _, pre, su, sq, ab, mm, h, _, _, _, hs, hq, ha, hp, hm => by
    simp only [wsumN, add_zero] at hs hq ha hp hm
    have hl : leafOK QN k ST su sq ab mm = true := by
      simp only [leafOK, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
      exact ⟨⟨⟨⟨hs, hq⟩, ha⟩, hm⟩, hp⟩
    simp only [valSearchR, hl, Bool.not_true, Bool.false_or] at h
    simpa using leafKilled_of_leafKilledN h
  | (r, z) :: cls, rem, pre, su, sq, ab, mm, h, hr, hc, hρ, hs, hq, ha, hp, hm => by
    simp only [List.mem_cons, forall_eq_or_imp] at hc hρ
    simp only [wsumN, mul_one] at hr hs hq ha hp hm
    have hnd := ndist_shiftVal hc.1
    have hu2 := shiftVal_le hc.1
    have hW := wsumN_shift_le τ cls hc.2
    have hcs := rest_cs τ cls hc.2
    have hR : rem - z = wsumN (fun _ => 1) cls := by omega
    have e1 : ST - (su + z * shiftVal C (τ r)) = wsumN (fun r => shiftVal C (τ r)) cls := by
      omega
    have e2 : QN - (sq + z * ((τ r).natAbs * (τ r).natAbs)) =
        wsumN (fun r => (τ r).natAbs * (τ r).natAbs) cls := by
      omega
    have hkeep : keepR C QN ST z rem su sq q res (shiftVal C (τ r)) = true := by
      simp only [keepR, keepN_eq, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, hnd, hR, e1, e2]
      exact ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hcs⟩, hρ.1⟩
    have hspan : (spanN C ST z rem su).1 ≤ shiftVal C (τ r) ∧
        shiftVal C (τ r) < (spanN C ST z rem su).1 + (spanN C ST z rem su).2 := by
      rw [spanN_eq]
      split_ifs with hz
      · exact ⟨Nat.zero_le _, by omega⟩
      · have hz' : 0 < z := Nat.pos_of_ne_zero hz
        have h1 : (ST - su - 2 * C * (rem - z) + z - 1) / z ≤ shiftVal C (τ r) := by
          refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hz').2 ?_)
          have e : (shiftVal C (τ r)).succ * z = z * shiftVal C (τ r) + z := by
            rw [Nat.succ_mul, Nat.mul_comm]
          rw [e, hR]
          omega
        have h2 : shiftVal C (τ r) ≤ (ST - su) / z := by
          rw [Nat.le_div_iff_mul_le hz', mul_comm]
          omega
        dsimp only
        exact ⟨h1, by omega⟩
    simp only [valSearchR_cons, allNat_iff] at h
    have hx := h _ hspan.1 hspan.2
    rw [hkeep, Bool.not_true, Bool.false_or] at hx
    have ih := valSearchR_sound τ cls _ _ _ _ _ _ hx hR hc.2 hρ.2 (by omega)
      (by rw [hnd]; omega) (by rw [hnd]; omega) (by rw [hnd]; omega) (by omega)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_cons]
      using ih

/-- `valSearchR` from the node `n`. -/
def Node.runR (Ws : List (List (List ℕ))) (C QN k ST : ℕ) (T : ℤ) (q res : ℕ) (n : Node) :
    Bool :=
  valSearchR Ws C QN k ST T q res n.cls n.rem n.pre n.su n.sq n.ab n.mm

/-- The nodes `d` levels below `valSearchR`'s node that it does not cut, in its order. -/
def frontierR (C QN ST q res : ℕ) :
    ℕ → List (ℕ × ℕ) → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → List Node
  | 0, cls, rem, pre, su, sq, ab, mm => [⟨cls, rem, pre, su, sq, ab, mm⟩]
  | _ + 1, [], rem, pre, su, sq, ab, mm => [⟨[], rem, pre, su, sq, ab, mm⟩]
  | d + 1, (_, z) :: cls, rem, pre, su, sq, ab, mm =>
    flatNat (fun u => if keepR C QN ST z rem su sq q res u then
        frontierR C QN ST q res d cls (rem - z) (u :: pre) (su + z * u)
          (sq + z * (ndist C u * ndist C u)) (ab + z * ndist C u) (mm + z * mmN C u)
      else [])
      (spanN C ST z rem su).1 (spanN C ST z rem su).2

/-- `valSearchR` holds at a node when it holds at every node of its frontier. -/
theorem valSearchR_of_frontier {Ws : List (List (List ℕ))} {C QN k ST : ℕ} {T : ℤ}
    {q res : ℕ} :
    ∀ (d : ℕ) (cls : List (ℕ × ℕ)) (rem : ℕ) (pre : List ℕ) (su sq ab mm : ℕ),
      (∀ n ∈ frontierR C QN ST q res d cls rem pre su sq ab mm,
        n.runR Ws C QN k ST T q res = true) →
      valSearchR Ws C QN k ST T q res cls rem pre su sq ab mm = true
  | 0, _, _, _, _, _, _, _, h => h _ List.mem_cons_self
  | _ + 1, [], _, _, _, _, _, _, h => h _ List.mem_cons_self
  | d + 1, (r, z) :: cls, rem, pre, su, sq, ab, mm, h => by
    simp only [valSearchR_cons, allNat_iff]
    intro u h1 h2
    cases hk : keepR C QN ST z rem su sq q res u
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      refine valSearchR_of_frontier d cls _ _ _ _ _ _ fun n hn => h n ?_
      simp only [frontierR, mem_flatNat]
      exact ⟨u, h1, h2, by simpa only [hk, ↓reduceIte] using hn⟩

/-- `cosetCheck` trying only shifted values `≡ res (mod q)`. -/
def cosetCheckR (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res : ℕ) :
    Bool :=
  cycLabelsOK v add t &&
    valSearchR (shiftWs v add t) c (k + lam * (c - 1)).toNat k (s + c * v).toNat (lam * c) q res
      (sortedCls v add t) (wsumN (fun _ => 1) (sortedCls v add t)) [] 0 0 0 0

/-- `cosetCheckR`'s nodes `d` levels down. -/
def cosetNodesR (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res d : ℕ) :
    List Node :=
  frontierR c (k + lam * (c - 1)).toNat (s + c * v).toNat q res d (sortedCls v add t)
    (wsumN (fun _ => 1) (sortedCls v add t)) [] 0 0 0 0

/-- `cosetCheckR`'s search from a node. -/
def cosetRunR (v : ℕ) (add : ℕ → ℕ → ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res : ℕ)
    (n : Node) : Bool :=
  n.runR (shiftWs v add t) c (k + lam * (c - 1)).toNat k (s + c * v).toNat (lam * c) q res

theorem cosetCheckR_of_nodes {v : ℕ} {add : ℕ → ℕ → ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {q res d : ℕ} (hl : cycLabelsOK v add t = true)
    (h : ∀ n ∈ cosetNodesR v add c k lam t s q res d, cosetRunR v add c k lam t s q res n = true) :
    cosetCheckR v add c k lam t s q res = true := by
  rw [cosetCheckR, hl, Bool.true_and]
  exact valSearchR_of_frontier d _ _ _ _ _ _ _ h

/-- `cosetCheckR` is `true` only if no `f` as in `cosetCheck_sound` with shifted values
`f y + c ≡ res (mod q)` exists. -/
theorem cosetCheckR_sound {v : ℕ} {add : ℕ → ℕ → ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {q res : ℕ} (h : cosetCheckR v add c k lam t s q res = true) (f : ℕ → ℤ)
    (hb : ∀ y < v, |f y| ≤ c) (hres : ∀ y < v, shiftVal c (f y) % q = res)
    (hinv : ∀ y < v, f (mulIdx add y t t) = f y) (hs : ∑ y ∈ Finset.range v, f y = s)
    (hq : ∑ y ∈ Finset.range v, f y * f y = k + lam * ((c : ℤ) - 1))
    (ha : ∑ y ∈ Finset.range v, |f y| ≤ k)
    (hp : ((k : ℤ) - ∑ y ∈ Finset.range v, |f y|) % 2 = 0)
    (hm : (k : ℤ) ≤ ∑ y ∈ Finset.range v, maxMarked c (f y))
    (hadd : ∀ y g, y < v → g < v → add y g < v)
    (hcorr : ∀ g, 0 < g → g < v → ∑ y ∈ Finset.range v, f y * f (add y g) = lam * c) :
    False := by
  simp only [cosetCheckR, Bool.and_eq_true] at h
  obtain ⟨hl, hv⟩ := h
  have hlab := labelsOK_spec (f := f) hl hinv
  have hperm : (sortedCls v add t).Perm (classes v (cycLab v add t) (cycDist v add t)) :=
    perm_sortBySize _
  have hw (F : ℤ → ℤ) :
      wsum (fun r => F (f r)) (sortedCls v add t) = ∑ y ∈ Finset.range v, F (f y) := by
    rw [wsum_perm _ hperm, sum_range_eq_wsum hlab F]
  have hkeys : (classes v (cycLab v add t) (cycDist v add t)).map Prod.fst =
      roots v (cycDist v add t) := by
    simp [classes, List.map_map, Function.comp_def]
  have hrs : ((sortedCls v add t).map Prod.fst).Perm (roots v (cycDist v add t)) := by
    rw [← hkeys]
    exact hperm.map Prod.fst
  have hnodup : ((sortedCls v add t).map Prod.fst).Nodup :=
    hrs.nodup_iff.2 (List.nodup_range.filter _)
  have hroot : ∀ y < v, cycLab v add t y ∈ (sortedCls v add t).map Prod.fst := fun y hy =>
    hrs.mem_iff.2 (by
      simp only [roots, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨(hlab y hy).1, (hlab y hy).2.1⟩)
  have hlt : ∀ cz ∈ sortedCls v add t, cz.1 < v := fun cz hcz => by
    have h := hrs.mem_iff.1 (List.mem_map_of_mem (f := Prod.fst) hcz)
    simp only [roots, List.mem_filter, List.mem_range] at h
    exact h.1
  have hb' : ∀ cz ∈ sortedCls v add t, |f cz.1| ≤ c := fun cz hcz => hb _ (hlt cz hcz)
  have hres' : ∀ cz ∈ sortedCls v add t, shiftVal c (f cz.1) % q = res := fun cz hcz =>
    hres _ (hlt cz hcz)
  -- The sums over the classes, in ℕ.
  have hv1 : wsum (fun _ => 1) (sortedCls v add t) = v := by
    rw [hw fun _ => 1]
    simp
  have hsu : wsumN (fun r => shiftVal c (f r)) (sortedCls v add t) = (s + c * v).toNat := by
    have e : (wsumN (fun r => shiftVal c (f r)) (sortedCls v add t) : ℤ) = s + c * v := by
      rw [natCast_wsumN_shift f _ hb', hv1, ← hs]
      exact congrArg (· + (c : ℤ) * v) (hw fun x => x)
    rw [← e, Int.toNat_natCast]
  have hsq : wsumN (fun r => (f r).natAbs * (f r).natAbs) (sortedCls v add t) =
      (k + lam * (c - 1)).toNat := by
    have e : (wsumN (fun r => (f r).natAbs * (f r).natAbs) (sortedCls v add t) : ℤ) =
        k + lam * (c - 1) := by
      rw [natCast_wsumN_sq, ← hq]
      exact hw fun x => x * x
    rw [← e, Int.toNat_natCast]
  have hab : (wsumN (fun r => (f r).natAbs) (sortedCls v add t) : ℤ) =
      ∑ y ∈ Finset.range v, |f y| := by
    rw [natCast_wsumN_abs]
    exact hw fun x => |x|
  have hmm : (k : ℤ) ≤ wsumN (fun r => mmN c (shiftVal c (f r))) (sortedCls v add t) := by
    rw [natCast_wsumN]
    refine hm.trans (le_of_eq_of_le (hw fun x => maxMarked c x).symm ?_)
    exact wsum_mono _ fun cz hcz => maxMarked_le_mmN (hb' cz hcz)
  rw [← hab] at ha hp
  have hk := valSearchR_sound f _ _ [] 0 0 0 0 hv rfl hb' hres' (by rw [zero_add, hsu])
    (by rw [zero_add, hsq]) (by rw [zero_add]; exact_mod_cast ha) (by rw [zero_add]; omega)
    (by rw [zero_add]; exact_mod_cast hmm)
  have hsl : unshift c ([].reverse ++ (sortedCls v add t).map fun cz => shiftVal c (f cz.1)) =
      ((sortedCls v add t).map Prod.fst).map f := by
    simp only [unshift, List.reverse_nil, List.nil_append, List.map_map]
    refine List.map_congr_left fun cz hcz => ?_
    simp only [Function.comp_apply]
    rw [natCast_shiftVal (hb' cz hcz)]
    ring
  rw [hsl] at hk
  simp only [leafKilled, shiftWs, List.any_eq_true, List.mem_map, bne_iff_ne, ne_eq] at hk
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

/-- Values congruent mod `q` have shifted values congruent mod `q`. -/
theorem shiftVal_mod_eq {c q : ℕ} {x y : ℤ} (hx : |x| ≤ c) (hy : |y| ≤ c)
    (h : x ≡ y [ZMOD q]) : shiftVal c x % q = shiftVal c y % q := by
  have e : ((shiftVal c x : ℕ) : ℤ) ≡ (shiftVal c y : ℕ) [ZMOD q] := by
    rw [natCast_shiftVal hx, natCast_shiftVal hy]
    exact h.add_right _
  exact Int.natCast_modEq_iff.1 e

end CosetSearch

open CosetSearch OrbitSearch

/-! ### Soundness on a group -/

section Group

variable {H : Type*} [AddCommGroup H] [Fintype H] [Indexed H]

/-- If `cosetCheckR` holds on `H`'s numbers, no `a : H → ℤ` with shifted values `≡ res (mod q)`
is as in `false_of_cosetCheck`. -/
theorem false_of_cosetCheckR {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ} {q res : ℕ}
    (h : cosetCheckR (Indexed.size H) (Indexed.addIdx H) c k lam t s q res = true) {a : H → ℤ}
    (hd : Demands c k lam a) (hm : (k : ℤ) ≤ ∑ x, maxMarked c (a x))
    (ht : ∀ x, a (t • x) = a x) (hs : ∑ x, a x = s)
    (hres : ∀ x, shiftVal c (a x) % q = res) : False := by
  classical
  let f : ℕ → ℤ := fun y =>
    if hy : y < Indexed.size H then a (Indexed.equiv.symm ⟨y, hy⟩) else 0
  have hfe (x : H) : f (Indexed.equiv x) = a x := by simp [f]
  have hsurj (y : ℕ) (hy : y < Indexed.size H) : ∃ x : H, (Indexed.equiv x : ℕ) = y :=
    ⟨Indexed.equiv.symm ⟨y, hy⟩, by simp⟩
  have hsum (F : ℤ → ℤ) : ∑ y ∈ Finset.range (Indexed.size H), F (f y) = ∑ x, F (a x) := by
    rw [← sum_equiv (G := H) fun y => F (f y)]
    simp only [hfe]
  refine cosetCheckR_sound h f (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
    (fun y g hy hg => ?_) (fun g hg0 hg => ?_)
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [hfe]
    exact hd.bound x
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [hfe]
    exact hres x
  · obtain ⟨x, rfl⟩ := hsurj y hy
    rw [← Indexed.equiv_nsmul x t t le_rfl, hfe, hfe, ht]
  · rw [← hs]
    exact hsum fun x => x
  · rw [hsum fun x => x * x]
    exact hd.sq
  · rw [hsum fun x => |x|]
    exact hd.abs
  · rw [hsum fun x => |x|]
    exact hd.parity
  · rw [hsum fun x => maxMarked c x]
    exact hm
  · obtain ⟨x, rfl⟩ := hsurj y hy
    obtain ⟨x', rfl⟩ := hsurj g hg
    rw [← Indexed.equiv_add]
    exact (Indexed.equiv _).isLt
  · obtain ⟨gH, rfl⟩ := hsurj g hg
    have hne : gH ≠ 0 := by
      rintro rfl
      rw [Indexed.equiv_zero] at hg0
      omega
    rw [← hd.corr gH hne,
      ← sum_equiv (G := H) fun y => f y * f (Indexed.addIdx H y (Indexed.equiv gH))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Indexed.equiv_add, hfe, hfe]

end Group

/-! ### Rows -/

/-- The filtered coset search on the quotient `Grp ds` for the residue `res` mod `q`. -/
def cosetSearchR (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res : ℕ) : Bool :=
  onGrp ds fun v add => cosetCheckR v add c k lam t s q res

/-- The split filtered search's top: labels checked, at most `N` nodes `d` levels down. -/
def cosetTopR (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res d N : ℕ) : Bool :=
  onGrp ds fun v add =>
    cycLabelsOK v add t && decide ((cosetNodesR v add c k lam t s q res d).length ≤ N)

/-- The split filtered search's nodes `a, …, b − 1`, `d` levels down, all pass. -/
def cosetSliceR (ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q res d a b : ℕ) : Bool :=
  onGrp ds fun v add =>
    sliceOK (cosetNodesR v add c k lam t s q res d) (cosetRunR v add c k lam t s q res) a b

/-- The filtered search from its top and slices `[0, c₁), [c₁, c₂), …` of its nodes. -/
theorem cosetSearchR_of_slices {ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {q res d : ℕ} (cuts : List ℕ)
    (htop : cosetTopR ds c k lam t s q res d (lastCut 0 cuts) = true)
    (hsl : SlicesPass (cosetSliceR ds c k lam t s q res d) (0 :: cuts)) :
    cosetSearchR ds c k lam t s q res = true := by
  obtain ⟨hds, htop⟩ := onGrp_spec htop
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
  have e : cosetSliceR ds c k lam t s q res d = fun a b =>
      sliceOK (cosetNodesR (@Indexed.size (Grp ds) _ (Grp.indexed ds hds))
        (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)) c k lam t s q res d)
        (cosetRunR (@Indexed.size (Grp ds) _ (Grp.indexed ds hds))
          (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds hds)) c k lam t s q res) a b := by
    funext a b
    simp only [cosetSliceR, onGrp, dite_eq_left hds]
  rw [e] at hsl
  simp only [cosetSearchR, onGrp, dite_eq_left hds]
  exact cosetCheckR_of_nodes htop.1 fun n hn =>
    all_of_slices cuts 0 hsl htop.2 n (by rwa [List.drop_zero])

theorem forall_lt_two {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) : ∀ r < 2, P r := by
  intro r hr
  interval_cases r <;> assumption

theorem forall_lt_three {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ r < 3, P r := by
  intro r hr
  interval_cases r <;> assumption

/-- `CosetRowSelfConj` and a modulus `q = p^j` for a prime `p ∤ |H|` with `p^i ≡ −1` on every
factor of `ds` (`0 < i`) and `p^(2j) ∣ n`: by C5 the coset sums agree mod `q`. -/
def CosetRowCongr (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q : ℕ) : Prop :=
  CosetRowSelfConj ms ds c k lam t s ∧ 0 < q ∧
    ∃ p ∈ List.range (((k : ℤ) - lam).toNat + 1), IsPrimeTD p ∧ ds.prod % p ≠ 0 ∧
      (∃ i ∈ List.range ds.prod, 0 < i ∧ ∀ d ∈ ds, (p ^ i + 1) % d = 0) ∧
      ∃ j ∈ List.range (((k : ℤ) - lam).toNat + 1), q = p ^ j ∧
        ((k : ℤ) - lam).toNat % p ^ (2 * j) = 0

instance (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) (q : ℕ) :
    Decidable (CosetRowCongr ms ds c k lam t s q) := by
  unfold CosetRowCongr; infer_instance

/-- A row meeting `CosetRowCongr` whose filtered coset search passes for every residue has no
SDS: the fixed translate of C25 (or its negation) has shifted values in one residue mod `q`. -/
theorem not_hasSDS_of_cosetRowCongr {ms ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    {q : ℕ} (h : CosetRowCongr ms ds c k lam t s q)
    (hs : ∀ res < q, cosetSearchR ds c k lam t s q res = true)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨⟨hdv, hprod, hn, hcop, htH, hpf, hss⟩, hq0, p, -, hp, hpH, ⟨i, -, hi, hdi⟩, j, -,
    hqj, hj⟩ := h
  obtain ⟨hds, -⟩ := onGrp_spec (hs 0 hq0)
  let _ : Fintype (Grp ds) := Grp.fintype ds hds
  have hφ := quot_surjective ms ds hdv
  have hcard : Fintype.card (Grp ms) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, Grp.card_eq, hprod]
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  have hpos : 0 < ((k : ℤ) - lam).toNat := by omega
  have hcopZ : IsCoprime (Fintype.card (Grp ds) : ℤ) ((k : ℤ) - lam) := by
    rw [Grp.card_eq, hnz]
    exact Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract_selfConj (quot ms ds hdv) hφ hcard hn.ne'
    hcopZ
  have hfix := hb t (by rw [Grp.card_eq]; exact htH) fun p hp hpn => by
    have hpn' : p ∣ ((k : ℤ) - lam).toNat := by
      rw [hnz, Int.natCast_dvd_natCast] at hpn
      exact hpn
    rcases hpf p (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn')))
      (Nat.mod_eq_zero_of_dvd hpn') (isPrimeTD_of_prime hp) with
      ⟨f, -, hf⟩ | ⟨⟨i, -, hi, hdi⟩, j, -, hj, hj1⟩
    · exact Or.inl ⟨f, Grp.nsmul_eq_of_mod ds hf⟩
    · refine Or.inr ⟨⟨i, hi, fun x => ?_⟩, j, ?_, ?_⟩
      · have := Grp.nsmul_eq_zero (N := p ^ i + 1) ds
          (fun d hd => Nat.dvd_of_mod_eq_zero (hdi d hd)) x
        rw [add_smul, one_smul] at this
        exact eq_neg_of_add_eq_zero_left this
      · rw [hnz]
        exact_mod_cast Nat.dvd_of_mod_eq_zero hj
      · rw [hnz]
        intro hd
        exact hj1 (Nat.mod_eq_zero_of_dvd (by exact_mod_cast hd))
  have hfib := card_fibre_eq hφ hcard
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card (Grp ms))
      rw [hcard, h0, zero_mul] at this
      omega
    · exact h0
  set a := contract (quot ms ds hdv) D
  -- C5: the coset sums agree mod `q = p^j`.
  have hcong (x y : Grp ds) : a x ≡ a y [ZMOD q] := by
    have : Fact p.Prime := ⟨hp.prime⟩
    by_cases hH1 : ∃ g : Grp ds, g ≠ 0
    · have hc (x : Grp ds) : p ^ i • x = -x := by
        have := Grp.nsmul_eq_zero (N := p ^ i + 1) ds
          (fun d hd => Nat.dvd_of_mod_eq_zero (hdi d hd)) x
        rw [add_smul, one_smul] at this
        exact eq_neg_of_add_eq_zero_left this
      have hH : (Fintype.card (Grp ds) : ZMod p) ≠ 0 := by
        rw [Grp.card_eq, Ne, ZMod.natCast_eq_zero_iff]
        exact fun hd => hpH (Nat.mod_eq_zero_of_dvd hd)
      have hn2 : (p : ℤ) ^ (2 * j) ∣ (k : ℤ) - lam := by
        rw [hnz]
        exact_mod_cast Nat.dvd_of_mod_eq_zero hj
      rw [hqj, Nat.cast_pow]
      exact hD.contract_congr_pow (quot ms ds hdv) hφ hcard hi hc hH hH1 hn2 x y
    · push Not at hH1
      have ex : x = 0 := hH1 x
      have ey : y = 0 := hH1 y
      subst ex ey
      exact Int.ModEq.refl _
  have hdem : Demands c k lam a :=
    { bound := fun h => by
        have := abs_contract_le (quot ms ds hdv) D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq (quot ms ds hdv), hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr (quot ms ds hdv) g hg, hfib]
      abs := hD.sum_abs_contract_le (quot ms ds hdv)
      parity := hD.sum_abs_contract_parity (quot ms ds hdv) }
  have hmm : (k : ℤ) ≤ ∑ h, maxMarked c (a h) := by
    rw [← hD.sum_marked (quot ms ds hdv)]
    refine Finset.sum_le_sum fun h _ => marked_le_maxMarked _ D h ?_
    have := marked_le_card (quot ms ds hdv) D h
    rw [hfib] at this
    exact_mod_cast this
  -- The fixed translate `a'` and its sum `±s`.
  let a' : Grp ds → ℤ := fun h => a (h + b)
  have hda : Demands c k lam a' := hdem.translate b
  have hma : (k : ℤ) ≤ ∑ h, maxMarked c (a' h) := by
    rw [Fintype.sum_equiv (Equiv.addRight b) (fun h => maxMarked c (a' h))
      (fun u => maxMarked c (a u)) fun _ => rfl]
    exact hmm
  have hta : ∀ x, a' (t • x) = a' x := hfix
  have hca : ∀ x y, a' x ≡ a' y [ZMOD q] := fun x y => hcong (x + b) (y + b)
  have hH1 : 1 ≤ Fintype.card (Grp ds) := Fintype.card_pos
  have hv : ((ms.prod : ℕ) : ℤ) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, hprod, Nat.cast_mul]
  have hsq : (∑ h, a' h) * (∑ h, a' h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hda.sq, Finset.sum_congr rfl fun g hg => hda.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hss,
      nsmul_eq_mul, Nat.cast_sub hH1, hv]
    push_cast
    ring
  have key : ∀ a' : Grp ds → ℤ, Demands c k lam a' → (k : ℤ) ≤ ∑ h, maxMarked c (a' h) →
      (∀ x, a' (t • x) = a' x) → ∑ h, a' h = s → (∀ x y, a' x ≡ a' y [ZMOD q]) → False :=
    fun a' h1 h2 h3 h4 h5 => by
      obtain ⟨hds', hchk⟩ := onGrp_spec (hs _ (Nat.mod_lt (shiftVal c (a' 0)) hq0))
      exact @false_of_cosetCheckR (Grp ds) _ _ (Grp.indexed ds hds') _ _ _ _ _ _ _ hchk a' h1
        h2 h3 h4 fun x => shiftVal_mod_eq (h1.bound x) (h1.bound 0) (h5 x 0)
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key a' hda hma hta h1 hca
  · have hna : ∀ x, -a' (t • x) = -a' x := fun x => by rw [hta]
    have hns : ∑ h, -a' h = s := by rw [Finset.sum_neg_distrib, h1, neg_neg]
    exact key (fun h => -a' h) hda.neg (by simpa only [maxMarked_neg] using hma) hna hns
      fun x y => (hca x y).neg

end SignedDifferenceSets
