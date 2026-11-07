import SignedDifferenceSets.CosetSearchCongr
import SignedDifferenceSets.Tests.MultiplierSelfConj
import SignedDifferenceSets.CosetRows.Part95
import SignedDifferenceSets.CosetRows.Part96
import SignedDifferenceSets.CosetRows.Part97
import SignedDifferenceSets.CosetRows.Part98

open SignedDifferenceSets

#print axioms IsSDS.exists_translate_fixed_contract_selfConj
#print axioms exists_translate_fixed_of_autocorr_selfConj
#print axioms not_hasSDS_of_cosetRowSelfConj
#print axioms not_hasSDS_of_cosetRowCongr

example {G : Type} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {D : G → SignType}
    {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (hD : IsSDS k lam D) (φ : G →+ H)
    (hφ : Function.Surjective φ) {c : ℕ} (hcard : Fintype.card G = c * Fintype.card H)
    (hn0 : (k : ℤ) - lam ≠ 0) (hcop : IsCoprime (Fintype.card H : ℤ) ((k : ℤ) - lam)) :
    ∃ b : H, ∀ t : ℕ, Nat.Coprime t (Fintype.card H) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : H, t • x = p ^ f • x) →
        ∀ h, contract φ D (t • h + b) = contract φ D (h + b) := by
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract_selfConj φ hφ hcard hn0 hcop
  exact ⟨b, fun t ht hp => hb t ht fun p pp pd => Or.inl (hp p pp pd)⟩

example : ¬ SignedDifferenceSets.HasSDS (ZMod 327) 111 3 := SignedDifferenceSets.CosetRows.n29176_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n29176_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 198) 148 48 := SignedDifferenceSets.CosetRows.n9541_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n9541_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 198) 150 50 := SignedDifferenceSets.CosetRows.n9543_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n9543_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 396) 324 224 := SignedDifferenceSets.CosetRows.n43664_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n43664_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 415 315 := SignedDifferenceSets.CosetRows.n69318_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69318_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 370) 346 150 := SignedDifferenceSets.CosetRows.n37651_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n37651_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 2 × ZMod 198) 124 24 := SignedDifferenceSets.CosetRows.n43469_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n43469_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 396) 124 24 := SignedDifferenceSets.CosetRows.n43472_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n43472_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 370) 244 48 := SignedDifferenceSets.CosetRows.n37613_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n37613_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 120 20 := SignedDifferenceSets.CosetRows.n68992_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n68992_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 3 × ZMod 165) 328 132 := SignedDifferenceSets.CosetRows.n69187_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69187_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 328 132 := SignedDifferenceSets.CosetRows.n69188_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69188_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 290) 202 6 := SignedDifferenceSets.CosetRows.n22696_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n22696_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 342) 102 2 := SignedDifferenceSets.CosetRows.n31579_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n31579_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 435) 219 23 := SignedDifferenceSets.CosetRows.n53298_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n53298_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 435) 200 4 := SignedDifferenceSets.CosetRows.n53285_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n53285_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 3 × ZMod 114) 102 2 := SignedDifferenceSets.CosetRows.n31578_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n31578_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 418) 202 6 := SignedDifferenceSets.CosetRows.n49068_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n49068_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 264 68 := SignedDifferenceSets.CosetRows.n69100_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69100_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 2 × ZMod 198) 204 8 := SignedDifferenceSets.CosetRows.n43533_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n43533_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 396) 204 8 := SignedDifferenceSets.CosetRows.n43536_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n43536_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 311 115 := SignedDifferenceSets.CosetRows.n69166_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69166_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 495) 199 3 := SignedDifferenceSets.CosetRows.n69042_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n69042_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 364) 279 54 := SignedDifferenceSets.CosetRows.n36412_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n36412_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 455) 423 99 := SignedDifferenceSets.CosetRows.n58654_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n58654_not_hasSDS
example : ¬ SignedDifferenceSets.HasSDS (ZMod 390) 372 48 := SignedDifferenceSets.CosetRows.n42350_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n42350_not_hasSDS
