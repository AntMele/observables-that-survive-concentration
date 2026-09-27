import Fluctuations.PauliBrickwork
import Fluctuations.PauliCircuitBridge

namespace Fluctuations
noncomputable section

/-- The literal initial Pauli Z on the leftmost qubit and identities elsewhere. -/
def brickworkInitialZ (c : ℕ) : PauliString (BrickworkSite c) :=
  fun s => if s = (0,0) then 3 else 0

lemma pauliInitialVector_product {Site : Type*} [Fintype Site] [DecidableEq Site]
    (P₀ : PauliString Site) :
    pauliInitialVector P₀ = pauliProductWeight (fun s p => if p = P₀ s then 1 else 0) := by
  funext Q
  simp only [pauliInitialVector, pauliProductWeight, Fintype.prod_boole]
  simp only [funext_iff]

lemma pauliHaar_Z_input (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      ((if p.1 = 3 then 1 else 0 : ℝ) * pauliIdentityWeight p.2)) =
      (1/5 : ℝ) * (pauliNonzeroWeight q.1 * pauliIdentityWeight q.2) +
      (4/5 : ℝ) * (pauliUniformWeight q.1 * pauliNonzeroWeight q.2) := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight, pauliNonzeroWeight, pauliUniformWeight] <;> decide

lemma brickworkRank_zero_iff {c : ℕ} (s : BrickworkSite c) :
    brickworkRank s = 0 ↔ s = (0,0) := by
  rcases s with ⟨a,b⟩
  simp only [brickworkRank, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero]
  omega

lemma brickworkInitialZ_first_gate (c : ℕ) :
    pauliPairEvolution (0,0) (0,1) localPauliHaarKernel
      (pauliInitialVector (brickworkInitialZ c)) = brickworkCellShock (0 : Fin (c+1)) := by
  rw [pauliInitialVector_product]
  funext Q
  apply pauliPairEvolution_product_mix _
    (pauliShockMarginal brickworkRank 0) (pauliShockMarginal brickworkRank 1)
    (0,0) (0,1) (by simp)
  · intro s hsi hsj
    have hz : brickworkRank s ≠ 0 := fun h => hsi ((brickworkRank_zero_iff s).mp h)
    funext p
    simp [pauliShockMarginal, hz, brickworkInitialZ, hsi, pauliIdentityWeight]
  · intro s hsi hsj
    have hz : brickworkRank s ≠ 0 := fun h => hsi ((brickworkRank_zero_iff s).mp h)
    have h1 : brickworkRank s ≠ 1 := by
      intro h
      apply hsj
      apply brickworkRank_injective c
      simpa [brickworkRank] using h
    funext p
    simp [pauliShockMarginal, show ¬brickworkRank s < 1 by omega,
      h1, brickworkInitialZ, hsi, pauliIdentityWeight]
  · intro q
    simpa [pauliShockMarginal, brickworkRank, brickworkInitialZ,
      pauliIdentityWeight] using pauliHaar_Z_input q

/-- The first actual odd Haar layer sends the single initial Z Pauli to the
first cell shock. Uniform initial Pauli orientation is derived here. -/
theorem brickworkInitialZ_odd_layer (c : ℕ) :
    pauliLayerEvolution (brickworkOddBonds c) (pauliInitialVector (brickworkInitialZ c)) =
      brickworkCellShock (0 : Fin (c+1)) := by
  rw [brickworkOddBonds, List.ofFn_succ]
  change pauliLayerEvolution (List.ofFn (fun a : Fin c => brickworkOddBond a.succ))
    (pauliPairEvolution (0,0) (0,1) localPauliHaarKernel
      (pauliInitialVector (brickworkInitialZ c))) = _
  rw [brickworkInitialZ_first_gate]
  change pauliLayerEvolution _ (fun P =>
    (1/5 : ℝ)*pauliShock brickworkRank 0 P+(4/5 : ℝ)*pauliShock brickworkRank 1 P) = _
  rw [pauliLayerEvolution_linear]
  have hfix (x : ℕ) (hx : x ≤ 1) :
      pauliLayerEvolution (List.ofFn (fun a : Fin c => brickworkOddBond a.succ))
        (pauliShock brickworkRank x) = pauliShock brickworkRank x := by
    apply pauliLayerEvolution_shock_fixed brickworkRank (brickworkRank_injective c)
    · intro p hp
      obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
      simp [brickworkOddBond,brickworkRank]
    · intro p hp
      obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
      simp only [brickworkOddBond,brickworkRank,Fin.val_succ,Fin.val_zero,Fin.val_one]
      omega
  rw [hfix 0 (by norm_num),hfix 1 (by norm_num)]
  rfl

end
end Fluctuations
