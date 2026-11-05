module

public import Mathlib

/-!
# Numbering the elements of a key's group

`Indexed G` numbers the elements of `G` as `0, …, size − 1`, `0` first, with addition
computed on the numbers, so a check on numbers that the kernel evaluates speaks about
`G`. Instances cover `ZMod n` and products, so every key's `ZMod m₁ × ⋯ × ZMod m_r`, in
mixed radix with the first factor most significant.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The elements of `G` numbered `0, …, size − 1`, with addition on the numbers. -/
class Indexed (G : Type*) [AddCommGroup G] where
  size : ℕ
  equiv : G ≃ Fin size
  addIdx : ℕ → ℕ → ℕ
  equiv_zero : (equiv 0 : ℕ) = 0
  equiv_add : ∀ x y : G, (equiv (x + y) : ℕ) = addIdx (equiv x) (equiv y)

instance (n : ℕ) [NeZero n] : Indexed (ZMod n) where
  size := n
  equiv :=
    { toFun := fun x => ⟨x.val, x.val_lt⟩
      invFun := fun i => ((i : ℕ) : ZMod n)
      left_inv := fun x => ZMod.natCast_zmod_val x
      right_inv := fun i => Fin.ext (ZMod.val_cast_of_lt i.isLt) }
  addIdx a b := (a + b) % n
  equiv_zero := ZMod.val_zero
  equiv_add x y := ZMod.val_add x y

instance {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Indexed G] [Indexed H] :
    Indexed (G × H) where
  size := Indexed.size G * Indexed.size H
  equiv := (Equiv.prodCongr Indexed.equiv Indexed.equiv).trans finProdFinEquiv
  addIdx a b :=
    Indexed.addIdx H (a % Indexed.size H) (b % Indexed.size H) +
      Indexed.size H * Indexed.addIdx G (a / Indexed.size H) (b / Indexed.size H)
  equiv_zero := by simp [finProdFinEquiv, Indexed.equiv_zero]
  equiv_add x y := by
    have hpos : 0 < Indexed.size H := (Indexed.equiv (0 : H)).pos
    have hmod (u : G) (w : H) :
        ((Indexed.equiv w : ℕ) + Indexed.size H * Indexed.equiv u) % Indexed.size H =
          Indexed.equiv w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Indexed.equiv w).isLt]
    have hdiv (u : G) (w : H) :
        ((Indexed.equiv w : ℕ) + Indexed.size H * Indexed.equiv u) / Indexed.size H =
          Indexed.equiv u := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (Indexed.equiv w).isLt, zero_add]
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, finProdFinEquiv,
      Equiv.coe_fn_mk, Indexed.equiv_add, hmod, hdiv]

variable {G : Type*} [AddCommGroup G] [Indexed G]

/-- A sum over `G` is the sum over the numbers `0, …, size − 1`. -/
theorem sum_equiv [Fintype G] (f : ℕ → ℤ) :
    ∑ x : G, f (Indexed.equiv x) = ∑ i ∈ Finset.range (Indexed.size G), f i := by
  rw [Equiv.sum_comp Indexed.equiv (fun i => f i), Fin.sum_univ_eq_sum_range]

theorem equiv_ne_zero {g : G} (hg : g ≠ 0) : (Indexed.equiv g : ℕ) ≠ 0 := by
  intro h
  apply hg
  apply Indexed.equiv.injective
  exact Fin.ext (h.trans Indexed.equiv_zero.symm)

end SignedDifferenceSets
