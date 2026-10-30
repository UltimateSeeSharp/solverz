module

public import RamseyK3K4eK4e.Statement

/-!
# R(K₃, K₄−e, K₄−e): a checker for `Valid`

`Checks m` states `Valid` as loops over distinct points of a symmetric
colour matrix `m`, so `decide +kernel` can evaluate it on a concrete
colouring; `valid_of_checks` makes that enough for `Valid`.
-/

@[expose] public section

namespace RamseyK3K4eK4e

open SimpleGraph

/-- The edge colouring given by a symmetric matrix. -/
def ofMatrix {n : ℕ} (m : Fin n → Fin n → Fin 3) (hm : ∀ i j, m i j = m j i) :
    Sym2 (Fin n) → Fin 3 :=
  Sym2.lift ⟨m, hm⟩

/-- No triangle in colour 0, and in colours 1, 2 no K₄−e whose missing edge is `ab`. -/
def Checks {n : ℕ} (m : Fin n → Fin n → Fin 3) : Prop :=
  (∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ¬(m a b = 0 ∧ m a c = 0 ∧ m b c = 0)) ∧
  ∀ k : Fin 3, k ≠ 0 → ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬(m a c = k ∧ m a d = k ∧ m b c = k ∧ m b d = k ∧ m c d = k)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
-- the nested quantifiers over `Fin n` need a deep instance search
instance {n : ℕ} (m : Fin n → Fin n → Fin 3) : Decidable (Checks m) := by
  unfold Checks; infer_instance

theorem colourClass_ofMatrix_adj {n : ℕ} (m : Fin n → Fin n → Fin 3)
    (hm : ∀ i j, m i j = m j i) (k : Fin 3) (a b : Fin n) :
    (colourClass (ofMatrix m hm) k).Adj a b ↔ a ≠ b ∧ m a b = k := by
  simp [colourClass, ofMatrix, SimpleGraph.fromRel_adj, Sym2.lift_mk, hm b a]

theorem k4e_adj_02 : k4e.Adj 0 2 := by simp [k4e]
theorem k4e_adj_03 : k4e.Adj 0 3 := by simp [k4e]
theorem k4e_adj_12 : k4e.Adj 1 2 := by simp [k4e]
theorem k4e_adj_13 : k4e.Adj 1 3 := by simp [k4e]
theorem k4e_adj_23 : k4e.Adj 2 3 := by simp [k4e]

theorem valid_of_checks {n : ℕ} (m : Fin n → Fin n → Fin 3) (hm : ∀ i j, m i j = m j i)
    (h : Checks m) : Valid (ofMatrix m hm) := by
  have adj := colourClass_ofMatrix_adj m hm
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 hs
    rw [adj] at hab hac hbc
    exact h.1 a b c hab.1 hac.1 hbc.1 ⟨hab.2, hac.2, hbc.2⟩
  all_goals
    rintro ⟨f⟩
    have e : ∀ {i j : Fin 4}, k4e.Adj i j → _ := fun hij => (adj _ _ _).1 (f.toHom.map_adj hij)
    have ne : ∀ i j : Fin 4, i ≠ j → f.toHom i ≠ f.toHom j := fun i j hij => f.injective.ne hij
    first
    | exact h.2 1 (by decide) _ _ _ _ (ne 0 1 (by decide)) (ne 0 2 (by decide))
        (ne 0 3 (by decide)) (ne 1 2 (by decide)) (ne 1 3 (by decide)) (ne 2 3 (by decide))
        ⟨(e k4e_adj_02).2, (e k4e_adj_03).2, (e k4e_adj_12).2, (e k4e_adj_13).2,
          (e k4e_adj_23).2⟩
    | exact h.2 2 (by decide) _ _ _ _ (ne 0 1 (by decide)) (ne 0 2 (by decide))
        (ne 0 3 (by decide)) (ne 1 2 (by decide)) (ne 1 3 (by decide)) (ne 2 3 (by decide))
        ⟨(e k4e_adj_02).2, (e k4e_adj_03).2, (e k4e_adj_12).2, (e k4e_adj_13).2,
          (e k4e_adj_23).2⟩

end RamseyK3K4eK4e
