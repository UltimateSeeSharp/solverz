module

public import SignedDifferenceSets.SetCheck

/-!
# Checking a found set in chunks of shifts

`checkSet`'s shift test over a range `lo, …, lo + m − 1` of element numbers, so a large set's
check splits into one `decide +kernel` per range: each declaration's kernel run, and its
memory, covers only its shifts. `isSDS_of_checkSplit` joins the count and the ranges.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- Whether `p i` for the `m` numbers `lo, lo + 1, …`, testing `lo` first. -/
def allFrom (p : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => p lo && allFrom p (lo + 1) m

theorem allFrom_iff (p : ℕ → Bool) (lo m : ℕ) :
    allFrom p lo m = true ↔ ∀ i, lo ≤ i → i < lo + m → p i = true := by
  induction m generalizing lo with
  | zero => simp only [allFrom, true_iff]; intro i h1 h2; omega
  | succ m ih =>
    simp only [allFrom, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h⟩ i h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h1
      · exact h0
      · exact h i (by omega) (by omega)
    · intro h
      exact ⟨h lo le_rfl (by omega), fun i h1 h2 => h i (by omega) (by omega)⟩

theorem allFrom_append {p : ℕ → Bool} {lo a b : ℕ} (ha : allFrom p lo a = true)
    (hb : allFrom p (lo + a) b = true) : allFrom p lo (a + b) = true := by
  rw [allFrom_iff] at ha hb ⊢
  intro i h1 h2
  rcases lt_or_ge i (lo + a) with h | h
  · exact ha i h1 h
  · exact hb i h (by omega)

/-- `checkSet`'s count: the masks mark `k` elements. -/
def countOk (G : Type*) [AddCommGroup G] [Indexed G] (k : ℕ) (P N : ℕ) : Bool :=
  sumTo (fun i => if ofMasks P N i = 0 then 0 else 1) (Indexed.size G) == k

/-- `checkSet`'s test of shift number `g`: zero, or signed count `λ`. -/
def shiftOk (G : Type*) [AddCommGroup G] [Indexed G] (lam : ℤ) (P N : ℕ) (g : ℕ) : Bool :=
  g == 0 || sumTo (fun x => (ofMasks P N x : ℤ) * ofMasks P N (Indexed.addIdx G x g))
    (Indexed.size G) == lam

variable {G : Type*} [AddCommGroup G] [Fintype G] [Indexed G]

theorem isSDS_of_checkSplit {k : ℕ} {lam : ℤ} {P N : ℕ} (hc : countOk G k P N = true)
    (hs : allFrom (shiftOk G lam P N) 0 (Indexed.size G) = true) :
    IsSDS k lam (fun x : G => ofMasks P N (Indexed.equiv x)) := by
  refine isSDS_of_checkSet ?_
  rw [allFrom_iff] at hs
  simp only [checkSet, Bool.and_eq_true]
  exact ⟨hc, (allTo_iff _ _).2 fun i hi => hs i (Nat.zero_le i) (by omega)⟩

end SignedDifferenceSets
