module

public import Mathlib

/-!
# Signed difference sets: the goal

A signed difference set (SDS) with parameters (v, k, λ) in a finite abelian group `G`
of order v: k elements of `G`, each marked `+1` or `−1`, such that every non-identity
element `g` arises as a difference `(x + g) − x` of two marked elements with total sign λ.
In group-ring terms `D D⁻¹ = (k − λ) + λ G` (Gordon, arXiv:2212.10630). All signs `+1`:
an ordinary difference set; λ = 0 in a cyclic group: a circulant weighing matrix CW(v, k).

Goal, per open case of the table: `HasSDS G k λ` (Lean checks the set) or its negation.
Approved by the user 2026-11-05.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `D` marks each element of `G` with a sign, `0` meaning unmarked. It is a signed
difference set with parameters (|G|, k, λ) when it marks exactly `k` elements and for
every `g ≠ 0` the signed count `∑ₓ D(x) · D(x + g)` equals `λ`. -/
def IsSDS {G : Type*} [AddCommGroup G] [Fintype G] (k : ℕ) (lam : ℤ) (D : G → SignType) :
    Prop :=
  (Finset.univ.filter fun x => D x ≠ 0).card = k ∧
    ∀ g : G, g ≠ 0 → ∑ x, ((D x : ℤ) * (D (x + g) : ℤ)) = lam

/-- The group `G` has a signed difference set with parameters (|G|, k, λ). -/
def HasSDS (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) (lam : ℤ) : Prop :=
  ∃ D : G → SignType, IsSDS k lam D

end SignedDifferenceSets
