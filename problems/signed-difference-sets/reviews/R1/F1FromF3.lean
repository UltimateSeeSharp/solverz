import SignedDifferenceSets

open SignedDifferenceSets

/-- F1 from `contract_sq` along the zero map to `ZMod 1`. -/
theorem f1_of_contract_sq {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ}
    {D : G → SignType} (hD : IsSDS k lam D) :
    (∑ x, (D x : ℤ)) ^ 2 = k + lam * ((Fintype.card G - 1 : ℕ) : ℤ) := by
  classical
  have h := hD.contract_sq (0 : G →+ ZMod 1)
  have hf : fibre (0 : G →+ ZMod 1) 0 = Finset.univ := by ext; simp [fibre]
  have hc : contract (0 : G →+ ZMod 1) D 0 = ∑ x, (D x : ℤ) := by simp [contract]
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1), hf, Finset.card_univ, hc] at h
  rw [sq]
  exact h

#print axioms f1_of_contract_sq
