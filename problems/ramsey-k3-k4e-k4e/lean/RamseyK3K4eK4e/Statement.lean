module

public import Mathlib

/-!
# R(K₃, K₄−e, K₄−e): the goal

Colour every edge of K₂₁ with colour 0, 1 or 2 (the README's 1, 2, 3) so
that colour 0 has no triangle and colours 1 and 2 contain no K₄−e (four
points with at least five of their six edges in that colour). Such a
colouring exists iff R(K₃, K₄−e, K₄−e) = 22. Approved by the user 2026-10-30.
-/

@[expose] public section

namespace RamseyK3K4eK4e

open SimpleGraph

/-- The graph of the edges that `c` colours `k`. -/
def colourClass {n : ℕ} (c : Sym2 (Fin n) → Fin 3) (k : Fin 3) : SimpleGraph (Fin n) :=
  fromRel fun i j => c s(i, j) = k

/-- K₄−e: four points, every edge but one. -/
def k4e : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}

/-- `c` colours Kₙ with no triangle in colour 0 and no K₄−e in colours 1, 2. -/
def Valid {n : ℕ} (c : Sym2 (Fin n) → Fin 3) : Prop :=
  (colourClass c 0).CliqueFree 3 ∧ k4e.Free (colourClass c 1) ∧ k4e.Free (colourClass c 2)

/-- A valid colouring of K₂₁ exists, so R(K₃, K₄−e, K₄−e) = 22. -/
def Conjecture : Prop := ∃ c : Sym2 (Fin 21) → Fin 3, Valid c

end RamseyK3K4eK4e
