import Fluctuations.PauliBrickworkCircuit
import Fluctuations.PauliFrozenCircuit
import Fluctuations.PauliBrickworkConditional

open MeasureTheory
open scoped BigOperators

namespace Fluctuations

/-- The actual first-order endpoint OTOC of the canonical finite brickwork
circuit: an initial Z on the first qubit and a Z probe on the last qubit. -/
noncomputable def brickworkEndpointOTOC (c T : ℕ) (ρ : QubitOperator (BrickworkSite c)) :
    C((Fin (T * (2*c+1)) → TwoQubitUnitary), ℂ) where
  toFun x := globalOTOC ρ (pauliStringMatrix (brickworkInitialZ c))
    (pauliStringMatrix (pauliSiteZ (Fin.last c, (1 : Fin 2)))) 1
    (pauliCircuitUnitary (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
      (T * (2*c+1)) x)
  continuous_toFun := pauliCircuit_otoc_continuous _ _ _ _ _ _

/-- Exact conditional quantum-to-classical identity for an interior even
gate. The covariance reset follows from the next full odd Haar layer. -/
theorem brickworkEndpointOTOC_fixed_markov (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1)
    (z : Fin T × Fin c) (hz : z.1.val + 1 < T) (g : TwoQubitUnitary) :
    coordinateAverage (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)
      (brickworkEvenGateIndex z) (brickworkEndpointOTOC c T ρ) g =
      ∑ P : PauliString (BrickworkSite c), (pauliEndpointSign (P (Fin.last c,1)) : ℂ) *
        (markovWeightEvolution
          (pauliCircuitFixedKernel (brickworkCircuitBond c T) (brickworkEvenGateIndex z).val g)
          (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P : ℂ) := by
  apply pauliCircuit_fixed_gate_endpoint_otoc
  · exact hρ
  · intro s
    obtain ⟨u, htu, htouch⟩ := brickworkEvenGate_later_cover z hz s
    exact ⟨u.val, htu, u.isLt, htouch⟩

/-- The ordinary Haar expectation of the concrete endpoint OTOC is the
derived endpoint-sign observable of its exact Pauli Markov evolution. -/
theorem brickworkEndpointOTOC_haar_markov (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1) :
    (∫ x, brickworkEndpointOTOC c T ρ x
      ∂Measure.pi (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)) =
      ∑ P : PauliString (BrickworkSite c), (pauliEndpointSign (P (Fin.last c,1)) : ℂ) *
        (markovWeightEvolution (pauliCircuitHaarKernel (brickworkCircuitBond c T))
          (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P : ℂ) :=
  pauliCircuit_haar_endpoint_otoc _ _ _ ρ hρ _ _

/-- Centering the actual conditional quantum OTOC is exactly centering the
real endpoint-sign observables of the two derived weight evolutions. -/
theorem brickworkEndpointOTOC_conditional_sub_mean (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1)
    (z : Fin T × Fin c) (hz : z.1.val + 1 < T) (U : TwoQubitUnitary) :
    coordinateAverage (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)
        (brickworkEvenGateIndex z) (brickworkEndpointOTOC c T ρ) U -
      (∫ x, brickworkEndpointOTOC c T ρ x
        ∂Measure.pi (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)) =
      ((∑ P : PauliString (BrickworkSite c), pauliEndpointSign (P (Fin.last c,1)) *
          markovWeightEvolution
            (pauliCircuitFixedKernel (brickworkCircuitBond c T) (brickworkEvenGateIndex z).val U)
            (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P -
        ∑ P : PauliString (BrickworkSite c), pauliEndpointSign (P (Fin.last c,1)) *
          markovWeightEvolution (pauliCircuitHaarKernel (brickworkCircuitBond c T))
            (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P : ℝ) : ℂ) := by
  rw [brickworkEndpointOTOC_fixed_markov c T ρ hρ z hz U,
    brickworkEndpointOTOC_haar_markov c T ρ hρ]
  simp only [Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The exact conditional-mean formula for the actual brickwork quantum OTOC.
All other physical gates are genuinely integrated against normalized Haar;
the past/future factors and local A statistic are derived rather than assumed. -/
theorem brickworkEndpointOTOC_conditional_mean (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1)
    (z : Fin T × Fin c) (hz : z.1.val + 1 < T) (U : TwoQubitUnitary) :
    coordinateAverage (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)
      (brickworkEvenGateIndex z) (brickworkEndpointOTOC c T ρ) U =
      (∫ x, brickworkEndpointOTOC c T ρ x
        ∂Measure.pi (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)) -
      (16/15 : ℂ) * (endpointPastFactor c z.1.val z.2 : ℂ) *
        (endpointFutureFactor c (T-z.1.val-2) z.2 : ℂ) * ((localPauliA U : ℂ)-4/5) := by
  have h := brickworkEndpointOTOC_conditional_sub_mean c T ρ hρ z hz U
  rw [brickworkFrozenMarkov_sign_gap z hz U] at h
  push_cast at h
  linear_combination h

/-- Exact variance of the actual one-gate conditional mean, including its
numerical prefactor and the strictly positive universal local Haar variance. -/
theorem brickworkEndpointOTOC_gate_variance (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1)
    (z : Fin T × Fin c) (hz : z.1.val + 1 < T) :
    complexVariance (globalHaar TwoQubitBasis)
      (coordinateAverage (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)
        (brickworkEvenGateIndex z) (brickworkEndpointOTOC c T ρ)) =
      (256/225 : ℝ) * (endpointPastFactor c z.1.val z.2 *
        endpointFutureFactor c (T-z.1.val-2) z.2)^2 *
        ProbabilityTheory.variance localPauliA (globalHaar TwoQubitBasis) := by
  have he : coordinateAverage (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)
      (brickworkEvenGateIndex z) (brickworkEndpointOTOC c T ρ) =
      fun U => (∫ x, brickworkEndpointOTOC c T ρ x
        ∂Measure.pi (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)) -
        (16/15 : ℂ) * (endpointPastFactor c z.1.val z.2 : ℂ) *
          (endpointFutureFactor c (T-z.1.val-2) z.2 : ℂ) * ((localPauliA U : ℂ)-4/5) :=
    funext (brickworkEndpointOTOC_conditional_mean c T ρ hρ z hz)
  rw [he, gate_affine_variance localPauliA_memLp]

end Fluctuations
