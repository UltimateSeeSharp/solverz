module

public import SignedDifferenceSets.Rows

/-!
# Linear maps between the table's groups

A form `x ↦ ∑ aᵢ xᵢ` with natural coefficients `as` is a homomorphism `Grp ms →+ ZMod n` when
`n ∣ aᵢ mᵢ` for every factor (`FormOk`); one form per factor of `ds` gives
`linMap : Grp ms →+ Grp ds`. Missing coefficients and coordinates count as `0`.

`linMap` is onto when it sends given preimages to the unit vectors of `Grp ds` (`SurjCert`, a check
on natural numbers): the unit vectors generate `Grp ds` (`Grp.mem_of_unitL_mem`).
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `x ↦ a x` from `ZMod m` to `ZMod n`, a homomorphism when `n ∣ a m`. -/
def zmodMul (m n a : ℕ) (h : n ∣ a * m) : ZMod m →+ ZMod n :=
  ZMod.lift m ⟨a • Int.castAddHom (ZMod n), by
    simpa [nsmul_eq_mul] using (CharP.cast_eq_zero_iff (ZMod n) n (a * m)).2 h⟩

theorem zmodMul_natCast (m n a : ℕ) (h : n ∣ a * m) (x : ℕ) :
    zmodMul m n a h (x : ZMod m) = ((a * x : ℕ) : ZMod n) := by
  rw [show (x : ZMod m) = ((x : ℤ) : ZMod m) from (Int.cast_natCast x).symm, zmodMul,
    ZMod.lift_coe]
  simp [nsmul_eq_mul]

/-- The element of `Grp ms` with coordinates `xs`. -/
def Grp.ofList : (ms : List ℕ) → List ℕ → Grp ms
  | [], _ => 0
  | [m], xs => ((xs.headD 0 : ℕ) : ZMod m)
  | m :: m' :: ms, xs => (((xs.headD 0 : ℕ) : ZMod m), Grp.ofList (m' :: ms) xs.tail)

theorem Grp.ofList_nil : (ms : List ℕ) → Grp.ofList ms [] = 0
  | [] => rfl
  | [m] => Nat.cast_zero (R := ZMod m)
  | m :: m' :: ms => Prod.ext (Nat.cast_zero (R := ZMod m)) (Grp.ofList_nil (m' :: ms))

/-- `n ∣ aᵢ mᵢ` for every factor `mᵢ` of `ms`. -/
def FormOk (n : ℕ) : List ℕ → List ℕ → Prop
  | _, [] => True
  | as, [m] => n ∣ as.headD 0 * m
  | as, m :: m' :: ms => n ∣ as.headD 0 * m ∧ FormOk n as.tail (m' :: ms)

instance FormOk.instDecidable (n : ℕ) : (as ms : List ℕ) → Decidable (FormOk n as ms)
  | _, [] => isTrue trivial
  | as, [m] => inferInstanceAs (Decidable (n ∣ as.headD 0 * m))
  | as, m :: m' :: ms =>
    letI := FormOk.instDecidable n as.tail (m' :: ms)
    inferInstanceAs (Decidable (n ∣ as.headD 0 * m ∧ FormOk n as.tail (m' :: ms)))

/-- The form `x ↦ ∑ aᵢ xᵢ` on `Grp ms`. -/
def form (n : ℕ) : (as ms : List ℕ) → FormOk n as ms → Grp ms →+ ZMod n
  | _, [], _ => 0
  | as, [m], h => zmodMul m n (as.headD 0) h
  | as, m :: m' :: ms, h =>
    (zmodMul m n (as.headD 0) h.1).comp (AddMonoidHom.fst (ZMod m) (Grp (m' :: ms))) +
      (form n as.tail (m' :: ms) h.2).comp (AddMonoidHom.snd (ZMod m) (Grp (m' :: ms)))

/-- `∑ aᵢ xᵢ` over the factors of `ms`. -/
def dotL : List ℕ → List ℕ → List ℕ → ℕ
  | [], _, _ => 0
  | [_], as, xs => as.headD 0 * xs.headD 0
  | _ :: m' :: ms, as, xs => as.headD 0 * xs.headD 0 + dotL (m' :: ms) as.tail xs.tail

theorem form_ofList (n : ℕ) :
    (as ms : List ℕ) → (h : FormOk n as ms) → (xs : List ℕ) →
      form n as ms h (Grp.ofList ms xs) = (dotL ms as xs : ZMod n)
  | _, [], _, _ => by simp [form, dotL]
  | as, [m], h, xs => zmodMul_natCast m n _ h _
  | as, m :: m' :: ms, h, xs => by
    change zmodMul m n (as.headD 0) h.1 ((xs.headD 0 : ℕ) : ZMod m) +
      form n as.tail (m' :: ms) h.2 (Grp.ofList (m' :: ms) xs.tail) = _
    rw [zmodMul_natCast, form_ofList n as.tail (m' :: ms) h.2 xs.tail, dotL, Nat.cast_add]

/-- One form per factor of `ds`, each valid on `Grp ms`. -/
def MapOk (ms : List ℕ) : List ℕ → List (List ℕ) → Prop
  | [], _ => True
  | [d], A => FormOk d (A.headD []) ms
  | d :: d' :: ds, A => FormOk d (A.headD []) ms ∧ MapOk ms (d' :: ds) A.tail

instance MapOk.instDecidable (ms : List ℕ) :
    (ds : List ℕ) → (A : List (List ℕ)) → Decidable (MapOk ms ds A)
  | [], _ => isTrue trivial
  | [d], A => inferInstanceAs (Decidable (FormOk d (A.headD []) ms))
  | d :: d' :: ds, A =>
    letI := MapOk.instDecidable ms (d' :: ds) A.tail
    inferInstanceAs (Decidable (FormOk d (A.headD []) ms ∧ MapOk ms (d' :: ds) A.tail))

/-- The map `Grp ms →+ Grp ds` whose `t`-th coordinate is the form `A[t]`. -/
def linMap (ms : List ℕ) : (ds : List ℕ) → (A : List (List ℕ)) → MapOk ms ds A →
    Grp ms →+ Grp ds
  | [], _, _ => 0
  | [d], A, h => form d (A.headD []) ms h
  | d :: d' :: ds, A, h =>
    AddMonoidHom.prod (form d (A.headD []) ms h.1) (linMap ms (d' :: ds) A.tail h.2)

/-- The forms' values at `xs`. -/
def evalMap (ms xs : List ℕ) : List ℕ → List (List ℕ) → List ℕ
  | [], _ => []
  | [_], A => [dotL ms (A.headD []) xs]
  | _ :: d' :: ds, A => dotL ms (A.headD []) xs :: evalMap ms xs (d' :: ds) A.tail

theorem linMap_ofList (ms xs : List ℕ) :
    (ds : List ℕ) → (A : List (List ℕ)) → (h : MapOk ms ds A) →
      linMap ms ds A h (Grp.ofList ms xs) = Grp.ofList ds (evalMap ms xs ds A)
  | [], _, _ => rfl
  | [d], A, h => form_ofList d (A.headD []) ms h xs
  | d :: d' :: ds, A, h =>
    Prod.ext (form_ofList d (A.headD []) ms h.1 xs) (linMap_ofList ms xs (d' :: ds) A.tail h.2)

/-- Coordinates of the `t`-th unit vector. -/
def unitL : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => 0 :: unitL t

/-- A subgroup holding every unit vector is everything. -/
theorem Grp.mem_of_unitL_mem :
    (ds : List ℕ) → (S : AddSubgroup (Grp ds)) →
      (∀ t < ds.length, Grp.ofList ds (unitL t) ∈ S) → ∀ y, y ∈ S
  | [], S, _, y => by
    rw [Subsingleton.elim (α := ZMod 1) y 0]
    exact S.zero_mem
  | [d], S, h, y => by
    have h1 : (1 : ZMod d) ∈ S := by
      have := h 0 (by simp)
      simpa [Grp.ofList, unitL] using this
    rw [← ZMod.intCast_zmod_cast y, ← zsmul_one]
    exact S.zsmul_mem h1 _
  | d :: d' :: ds, S, h, y => by
    have h1 : ((1 : ZMod d), (0 : Grp (d' :: ds))) ∈ S := by
      have := h 0 (by simp)
      rwa [show Grp.ofList (d :: d' :: ds) (unitL 0) = ((1 : ZMod d), (0 : Grp (d' :: ds))) from
        Prod.ext Nat.cast_one (Grp.ofList_nil (d' :: ds))] at this
    have h2 (z : Grp (d' :: ds)) : ((0 : ZMod d), z) ∈ S := by
      refine AddSubgroup.mem_comap.1 (Grp.mem_of_unitL_mem (d' :: ds)
        (S.comap (AddMonoidHom.inr (ZMod d) (Grp (d' :: ds)))) (fun t ht => ?_) z)
      have := h (t + 1) (by simpa using ht)
      rw [AddSubgroup.mem_comap, AddMonoidHom.inr_apply]
      rwa [show Grp.ofList (d :: d' :: ds) (unitL (t + 1)) =
        ((0 : ZMod d), Grp.ofList (d' :: ds) (unitL t)) from Prod.ext Nat.cast_zero rfl] at this
    have hy : y = ((y.1.cast : ℤ) • ((1 : ZMod d), (0 : Grp (d' :: ds)))) +
        ((0 : ZMod d), y.2) := by
      refine Prod.ext ?_ ?_
      · change y.1 = (y.1.cast : ℤ) • (1 : ZMod d) + 0
        rw [zsmul_one, ZMod.intCast_zmod_cast, add_zero]
      · change y.2 = (y.1.cast : ℤ) • (0 : Grp (d' :: ds)) + y.2
        rw [smul_zero, zero_add]
    rw [hy]
    exact S.add_mem (S.zsmul_mem h1 _) (h2 _)

/-- `xs` and `ys` agree modulo each factor of `ds`. -/
def ModEqs : List ℕ → List ℕ → List ℕ → Prop
  | [], _, _ => True
  | [d], xs, ys => xs.headD 0 % d = ys.headD 0 % d
  | d :: d' :: ds, xs, ys => xs.headD 0 % d = ys.headD 0 % d ∧ ModEqs (d' :: ds) xs.tail ys.tail

instance ModEqs.instDecidable : (ds xs ys : List ℕ) → Decidable (ModEqs ds xs ys)
  | [], _, _ => isTrue trivial
  | [d], xs, ys => inferInstanceAs (Decidable (xs.headD 0 % d = ys.headD 0 % d))
  | d :: d' :: ds, xs, ys =>
    letI := ModEqs.instDecidable (d' :: ds) xs.tail ys.tail
    inferInstanceAs
      (Decidable (xs.headD 0 % d = ys.headD 0 % d ∧ ModEqs (d' :: ds) xs.tail ys.tail))

theorem Grp.ofList_eq_of_modEqs :
    (ds xs ys : List ℕ) → ModEqs ds xs ys → Grp.ofList ds xs = Grp.ofList ds ys
  | [], _, _, _ => rfl
  | [d], _, _, h => (ZMod.natCast_eq_natCast_iff' _ _ d).2 h
  | d :: d' :: ds, xs, ys, h =>
    Prod.ext ((ZMod.natCast_eq_natCast_iff' _ _ d).2 h.1)
      (Grp.ofList_eq_of_modEqs (d' :: ds) xs.tail ys.tail h.2)

/-- The forms `A` send the preimages `P[t]` to the unit vectors of `Grp ds`. -/
def SurjCert (ms ds : List ℕ) (A P : List (List ℕ)) : Prop :=
  ∀ t ∈ List.range ds.length, ModEqs ds (evalMap ms (P.getD t []) ds A) (unitL t)

instance (ms ds : List ℕ) (A P : List (List ℕ)) : Decidable (SurjCert ms ds A P) := by
  unfold SurjCert; infer_instance

theorem linMap_surjective {ms ds : List ℕ} {A P : List (List ℕ)} (h : MapOk ms ds A)
    (hs : SurjCert ms ds A P) : Function.Surjective (linMap ms ds A h) := fun y =>
  AddMonoidHom.mem_range.1 <| Grp.mem_of_unitL_mem ds (linMap ms ds A h).range (fun t ht =>
    AddMonoidHom.mem_range.2 ⟨Grp.ofList ms (P.getD t []), by
      rw [linMap_ofList]
      exact Grp.ofList_eq_of_modEqs _ _ _ (hs t (List.mem_range.2 ht))⟩) y

end SignedDifferenceSets
