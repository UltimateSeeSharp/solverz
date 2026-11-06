module

public import SignedDifferenceSets.Statement

/-!
# The table's groups as data

`Grp [m₁, …, m_r]` is `ZMod m₁ × ⋯ × ZMod m_r` (`ZMod 1` for `[]`), with its instances
defined by the same recursion, so it unfolds definitionally to the group a row names. A rule's
soundness theorem can then be stated once over the list and checked per row by `decide`.
`ZMod 0 = ℤ` is infinite, so `Fintype` is a `def` under positive factors.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The group `ZMod m₁ × ⋯ × ZMod m_r` of the row `[m₁, …, m_r]`. Reducible, so a
concrete row is its product type even for instance search. -/
@[reducible] def Grp : List ℕ → Type
  | [] => ZMod 1
  | [m] => ZMod m
  | m :: m' :: ms => ZMod m × Grp (m' :: ms)

instance Grp.instAddCommGroup : (ms : List ℕ) → AddCommGroup (Grp ms)
  | [] => inferInstanceAs (AddCommGroup (ZMod 1))
  | [m] => inferInstanceAs (AddCommGroup (ZMod m))
  | m :: m' :: ms =>
    @Prod.instAddCommGroup (ZMod m) (Grp (m' :: ms)) _ (Grp.instAddCommGroup (m' :: ms))

instance Grp.instDecidableEq : (ms : List ℕ) → DecidableEq (Grp ms)
  | [] => inferInstanceAs (DecidableEq (ZMod 1))
  | [m] => inferInstanceAs (DecidableEq (ZMod m))
  | m :: m' :: ms =>
    @instDecidableEqProd (ZMod m) (Grp (m' :: ms)) _ (Grp.instDecidableEq (m' :: ms))

/-- `Grp ms` is finite when every factor is positive. -/
@[instance_reducible]
def Grp.fintype : (ms : List ℕ) → (∀ m ∈ ms, 0 < m) → Fintype (Grp ms)
  | [], _ => inferInstanceAs (Fintype (ZMod 1))
  | [m], h => @ZMod.fintype m ⟨(h m List.mem_cons_self).ne'⟩
  | m :: m' :: ms, h =>
    @instFintypeProd (ZMod m) (Grp (m' :: ms)) (@ZMod.fintype m ⟨(h m List.mem_cons_self).ne'⟩)
      (Grp.fintype (m' :: ms) fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `Grp ms` has `ms.prod` elements (`0` when infinite). -/
theorem Grp.natCard_eq : (ms : List ℕ) → Nat.card (Grp ms) = ms.prod
  | [] => Nat.card_zmod 1
  | [m] => by
    change Nat.card (ZMod m) = _
    simp
  | m :: m' :: ms => by
    change Nat.card (ZMod m × Grp (m' :: ms)) = _
    rw [Nat.card_prod, Nat.card_zmod, Grp.natCard_eq (m' :: ms)]
    exact List.prod_cons.symm

/-- Any `Fintype` instance on `Grp ms` counts `ms.prod` elements. -/
theorem Grp.card_eq (ms : List ℕ) {_ : Fintype (Grp ms)} : Fintype.card (Grp ms) = ms.prod := by
  rw [Fintype.card_eq_nat_card, Grp.natCard_eq]

/-- `ds` divides `ms` factor by factor (same length). -/
def Dvds : List ℕ → List ℕ → Prop
  | [], [] => True
  | d :: ds, m :: ms => d ∣ m ∧ Dvds ds ms
  | _, _ => False

instance Dvds.instDecidable : (ds ms : List ℕ) → Decidable (Dvds ds ms)
  | [], [] => isTrue trivial
  | d :: ds, m :: ms =>
    letI := Dvds.instDecidable ds ms
    inferInstanceAs (Decidable (d ∣ m ∧ Dvds ds ms))
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id

/-- The quotient map `Grp ms →+ Grp ds`, reduction mod `dᵢ` in each factor. -/
def quot : (ms ds : List ℕ) → Dvds ds ms → Grp ms →+ Grp ds
  | [], [], _ => AddMonoidHom.id _
  | [_], [d], h => (ZMod.castHom h.1 (ZMod d)).toAddMonoidHom
  | _ :: m' :: ms, d :: d' :: ds, h =>
    AddMonoidHom.prodMap (ZMod.castHom h.1 (ZMod d)).toAddMonoidHom
      (quot (m' :: ms) (d' :: ds) h.2)
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | [_], _ :: _ :: _, h => False.elim h.2
  | _ :: _ :: _, [_], h => False.elim h.2

/-- Each factor's reduction is onto, so `quot` is. -/
theorem quot_surjective :
    (ms ds : List ℕ) → (h : Dvds ds ms) → Function.Surjective (quot ms ds h)
  | [], [], _ => Function.surjective_id
  | [_], [d], h => by
    change Function.Surjective (ZMod.castHom h.1 (ZMod d))
    exact ZMod.ringHom_surjective _
  | _ :: m' :: ms, d :: d' :: ds, h => by
    change Function.Surjective
      (Prod.map (ZMod.castHom h.1 (ZMod d)) (quot (m' :: ms) (d' :: ds) h.2))
    exact (ZMod.ringHom_surjective _).prodMap (quot_surjective (m' :: ms) (d' :: ds) h.2)
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | [_], _ :: _ :: _, h => False.elim h.2
  | _ :: _ :: _, [_], h => False.elim h.2

/-- `N` kills `ZMod d` when `d ∣ N`. -/
theorem zmod_nsmul_eq_zero {d N : ℕ} (h : d ∣ N) (x : ZMod d) : N • x = 0 := by
  rw [nsmul_eq_mul, (CharP.cast_eq_zero_iff (ZMod d) d N).2 h, zero_mul]

/-- `N` kills `Grp ds` when every factor divides `N`. -/
theorem Grp.nsmul_eq_zero {N : ℕ} :
    (ds : List ℕ) → (∀ d ∈ ds, d ∣ N) → (x : Grp ds) → N • x = 0
  | [], _, _ => Subsingleton.elim (α := ZMod 1) _ _
  | [d], h, x => zmod_nsmul_eq_zero (h d List.mem_cons_self) (x : ZMod d)
  | d :: d' :: ds, h, x =>
    Prod.ext (zmod_nsmul_eq_zero (h d List.mem_cons_self) (x.1 : ZMod d))
      (Grp.nsmul_eq_zero (d' :: ds) (fun e he => h e (List.mem_cons_of_mem _ he)) x.2)

/-- `1 ≠ 0` in `ZMod d` for `d > 1`. -/
theorem zmod_one_ne_zero {d : ℕ} (h : 1 < d) : (1 : ZMod d) ≠ 0 := by
  intro h1
  have := Nat.le_of_dvd one_pos ((CharP.cast_eq_zero_iff (ZMod d) d 1).1 (by simpa using h1))
  omega

/-- `Grp ds` is nontrivial when it has more than one element. -/
theorem Grp.exists_ne_zero : (ds : List ℕ) → 1 < ds.prod → ∃ x : Grp ds, x ≠ 0
  | [], h => absurd h (by simp)
  | [d], h => ⟨(1 : ZMod d), zmod_one_ne_zero (by simpa using h)⟩
  | d :: d' :: ds, h => by
    rw [List.prod_cons] at h
    by_cases hd : 1 < d
    · exact ⟨((1 : ZMod d), (0 : Grp (d' :: ds))), fun h0 =>
        zmod_one_ne_zero hd (congrArg Prod.fst h0 :)⟩
    · have hd1 : d = 1 := by
        rcases Nat.lt_or_ge d 1 with h0 | h0
        · simp [Nat.lt_one_iff.1 h0] at h
        · omega
      obtain ⟨y, hy⟩ := Grp.exists_ne_zero (d' :: ds) (by simpa [hd1] using h)
      exact ⟨((0 : ZMod d), y), fun h0 => hy (congrArg Prod.snd h0 :)⟩

/-! Tests: the row form instantiates to the group the row names. -/

example (h : ∀ inst : Fintype (Grp [2, 10]), ¬ @HasSDS (Grp [2, 10]) _ inst 17 8) :
    ¬ HasSDS (ZMod 2 × ZMod 10) 17 8 := h _

example (h : ∀ inst : Fintype (Grp [2, 2, 8]), ¬ @HasSDS (Grp [2, 2, 8]) _ inst 17 8) :
    ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 8) 17 8 := h _

example (h : ∀ inst : Fintype (Grp [7]), ¬ @HasSDS (Grp [7]) _ inst 4 0) :
    ¬ HasSDS (ZMod 7) 4 0 := h _

/-- The generic instance at a concrete row is the product instance. -/
example (h : ∀ ms : List ℕ, ∀ inst : Fintype (Grp ms), ¬ @HasSDS (Grp ms) _ inst 17 8) :
    ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 8) 17 8 := h [2, 2, 8] _

example : ZMod 2 × ZMod 10 →+ ZMod 1 × ZMod 5 := quot [2, 10] [1, 5] (by decide)

example : quot [2, 10] [1, 5] (by decide) ((1 : ZMod 2), (7 : ZMod 10)) =
    ((0 : ZMod 1), (2 : ZMod 5)) := by decide

example : ¬ Dvds [2, 3] [2, 10] := by decide

example : ¬ Dvds [2] [2, 10] := by decide

example : Fintype.card (ZMod 2 × ZMod 2 × ZMod 8) = 32 := Grp.card_eq [2, 2, 8]

example : @Fintype.card (Grp [2, 10]) (Grp.fintype [2, 10] (by decide)) = 20 := Grp.card_eq _

example : Nat.card (Grp [0, 3]) = 0 := Grp.natCard_eq _

end SignedDifferenceSets
