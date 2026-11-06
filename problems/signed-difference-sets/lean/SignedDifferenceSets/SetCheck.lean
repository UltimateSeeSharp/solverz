module

public import SignedDifferenceSets.Statement
public import SignedDifferenceSets.Index
public import SignedDifferenceSets.Loops

/-!
# Checking a found set fast

A sign vector given as two bit masks over the element numbers of `Indexed G` (plus, minus)
and a `Bool` check of the definition that `decide +kernel` evaluates with the kernel's big
number arithmetic: about a minute at v = 361, where `decide` on `IsSDS` would take hours.
`isSDS_of_checkSet` turns a `true` into `IsSDS`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The sign of element number `i`: `+` where `P` has bit `i`, else `−` where `N` has it. -/
def ofMasks (P N i : ℕ) : SignType :=
  if P.testBit i then 1 else if N.testBit i then -1 else 0

/-- Whether the masks mark `k` elements and every shift `g ≠ 0` has signed count `λ`. -/
def checkSet (G : Type*) [AddCommGroup G] [Indexed G] (k : ℕ) (lam : ℤ) (P N : ℕ) : Bool :=
  sumTo (fun i => if ofMasks P N i = 0 then 0 else 1) (Indexed.size G) == k &&
    allTo (fun g => g == 0 ||
      sumTo (fun x => (ofMasks P N x : ℤ) * ofMasks P N (Indexed.addIdx G x g))
        (Indexed.size G) == lam) (Indexed.size G)

variable {G : Type*} [AddCommGroup G] [Fintype G] [Indexed G]

theorem isSDS_of_checkSet {k : ℕ} {lam : ℤ} {P N : ℕ} (h : checkSet G k lam P N = true) :
    IsSDS k lam (fun x : G => ofMasks P N (Indexed.equiv x)) := by
  simp only [checkSet, Bool.and_eq_true, beq_iff_eq, allTo_iff, Bool.or_eq_true] at h
  obtain ⟨hk, hg⟩ := h
  refine ⟨?_, fun g hg0 => ?_⟩
  · have : ((Finset.univ.filter fun x : G => ofMasks P N (Indexed.equiv x) ≠ 0).card : ℤ) =
        ∑ x : G, (if ofMasks P N (Indexed.equiv x) = 0 then 0 else 1 : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp_all
    rw [sum_equiv (fun i => if ofMasks P N i = 0 then (0 : ℤ) else 1), ← sumTo_eq, hk] at this
    exact_mod_cast this
  · have hj := hg (Indexed.equiv g) (Indexed.equiv g).isLt
    simp only [equiv_ne_zero hg0, false_or] at hj
    rw [← hj, sumTo_eq, ← sum_equiv]
    simp only [Indexed.equiv_add]

end SignedDifferenceSets
