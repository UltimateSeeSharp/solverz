module

public import RamseyK3K4eK4e.Check

/-!
# Tests for `Valid`

Statement audit (`audit`): `Valid` accepts the 20-point colouring of
Shetler, Wurtz and Radziszowski (arXiv:1201.0554, Figure 3, colours 1, 2, 3
read as 0, 1, 2), rejects it with edge 01 recoloured 0 (a colour-0 triangle
on 0, 1, 15), and rejects K₄ in one colour (a K₄−e in colour 1).
-/

@[expose] public section

namespace RamseyK3K4eK4e

open SimpleGraph

/-- The 20-point colouring of arXiv:1201.0554, Figure 3; the diagonal is unused. -/
def paper20 : Fin 20 → Fin 20 → Fin 3 :=
  ![![0, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 2, 1, 2, 0, 1, 2, 2, 1, 0, 1, 2, 0, 1, 0, 0, 0, 2, 1],
    ![1, 2, 0, 2, 1, 0, 2, 1, 1, 0, 1, 2, 0, 2, 0, 1, 0, 0, 2, 1],
    ![2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 0, 1, 0, 1, 2],
    ![2, 2, 1, 1, 0, 0, 0, 0, 2, 2, 1, 1, 1, 2, 0, 0, 0, 1, 1, 2],
    ![1, 0, 0, 0, 0, 0, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 0, 0],
    ![1, 1, 2, 2, 0, 2, 0, 1, 2, 2, 1, 0, 0, 0, 2, 1, 1, 0, 1, 0],
    ![2, 2, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2, 2, 1, 1, 2, 2, 0, 0, 1],
    ![1, 2, 1, 0, 2, 2, 2, 0, 0, 1, 2, 1, 0, 0, 1, 2, 0, 1, 1, 0],
    ![2, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 2, 0],
    ![2, 0, 1, 2, 1, 1, 1, 0, 2, 1, 0, 0, 0, 1, 0, 2, 1, 2, 2, 0],
    ![2, 1, 2, 0, 1, 1, 0, 2, 1, 0, 0, 0, 1, 2, 2, 1, 0, 2, 0, 1],
    ![1, 2, 0, 2, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 2, 0, 2],
    ![1, 0, 2, 1, 2, 2, 0, 1, 0, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0, 2],
    ![0, 1, 0, 0, 0, 1, 2, 1, 1, 2, 0, 2, 1, 0, 0, 2, 1, 2, 1, 2],
    ![0, 0, 1, 0, 0, 1, 1, 2, 2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 1, 2],
    ![0, 0, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1],
    ![0, 0, 0, 0, 1, 2, 0, 0, 1, 1, 2, 2, 2, 1, 2, 1, 1, 0, 2, 1],
    ![0, 2, 2, 1, 1, 0, 1, 0, 1, 2, 2, 0, 0, 0, 1, 1, 2, 2, 0, 1],
    ![0, 1, 1, 2, 2, 0, 0, 1, 0, 0, 0, 1, 2, 2, 2, 2, 1, 1, 1, 0]]

theorem paper20_symm : ∀ i j, paper20 i j = paper20 j i := by decide +kernel

theorem paper20_checks : Checks paper20 := by decide +kernel

theorem paper20_valid : Valid (ofMatrix paper20 paper20_symm) :=
  valid_of_checks _ _ paper20_checks

/-- `paper20` with edge 01 recoloured 0. -/
def broken20 (i j : Fin 20) : Fin 3 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 0 else paper20 i j

theorem broken20_symm : ∀ i j, broken20 i j = broken20 j i := by decide +kernel

theorem broken20_not_valid : ¬Valid (ofMatrix broken20 broken20_symm) := by
  intro h
  refine h.1 {0, 1, 15} (is3Clique_triple_iff.2 ?_)
  simp only [colourClass_ofMatrix_adj]
  decide +kernel

theorem k4_not_valid : ¬Valid (fun _ : Sym2 (Fin 4) => (1 : Fin 3)) := by
  refine fun h => h.2.1 ⟨Copy.ofLE k4e _ fun a b hab => ?_⟩
  simpa [colourClass, SimpleGraph.fromRel_adj] using hab.ne

end RamseyK3K4eK4e
