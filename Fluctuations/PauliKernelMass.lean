import Fluctuations.EndpointLumpability
import Fluctuations.PauliFixedLocal

/-! Finite adjointness and mass preservation for arbitrary two-qubit Pauli kernels. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Finite input-output reindexing for an arbitrary local kernel. -/
theorem pauliPairEvolution_pairing (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (f w : (Site → Fin 4) → ℝ) :
    (∑ Q, f Q * pauliPairEvolution i j K w Q) =
      ∑ P, (∑ q, K q (P i,P j) * f (pauliPairReplace i j P q)) * w P := by
  simp only [pauliPairEvolution, Finset.mul_sum, Finset.sum_mul]
  let F : ((Site → Fin 4) × TwoQubitPauliLabel) → ℝ := fun z =>
    f z.1 * (K (z.1 i,z.1 j) z.2 * w (pauliPairReplace i j z.1 z.2))
  let H : ((Site → Fin 4) × TwoQubitPauliLabel) → ℝ := fun z =>
    K z.2 (z.1 i,z.1 j) * f (pauliPairReplace i j z.1 z.2) * w z.1
  change (∑ P, ∑ p, F (P,p)) = ∑ P, ∑ p, H (P,p)
  rw [← Fintype.sum_prod_type F, ← Fintype.sum_prod_type H]
  apply Fintype.sum_equiv (pauliPairSwapEquiv i j hij)
  rintro ⟨P,p⟩
  simp only [F, H, pauliPairSwapEquiv, Equiv.coe_fn_mk,
    pauliPairReplace_replace i j hij, pauliPairReplace_self]
  simp only [pauliPairReplace, Function.update_self, Function.update_of_ne hij]
  ring

/-- Every column-stochastic pair kernel preserves the sum of full-string weights. -/
theorem pauliPairEvolution_totalMass_of_column_sum (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (hK : ∀ p, ∑ q, K q p = 1) (w : (Site → Fin 4) → ℝ) :
    (∑ P, pauliPairEvolution i j K w P) = ∑ P, w P := by
  have h := pauliPairEvolution_pairing i j hij K (fun _ => 1) w
  simpa only [one_mul, mul_one, hK] using h

/-- The genuine squared Pauli transfer coefficients of any fixed unitary
preserve total mass; no stochasticity assumption is needed as an input. -/
theorem pauliFixedPair_totalMass (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (w : (Site → Fin 4) → ℝ) :
    (∑ P, pauliPairEvolution i j (localPauliSquaredKernel U) w P) = ∑ P, w P := by
  apply pauliPairEvolution_totalMass_of_column_sum i j hij
  intro p
  exact twoQubitPauliTransfer_column_sq p U

end
end Fluctuations
