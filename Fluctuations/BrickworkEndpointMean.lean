import Fluctuations.BrickworkEndpointOTOC
import Fluctuations.PauliBrickworkConditional
import Fluctuations.EndpointMean

open MeasureTheory
open scoped BigOperators

namespace Fluctuations

lemma brickworkInitialZ_cellMass (c : ℕ) :
    brickworkEndpointCellMass (pauliInitialVector (brickworkInitialZ c)) =
      fun b : Fin (c+1) => if b = 0 then 1 else 0 := by
  rw [← brickworkEndpointCellMass_odd c, brickworkInitialZ_odd_layer]
  funext b
  change pauliEndpointMass brickworkRank (brickworkCellShock 0) (brickworkRank (b,0)) +
    pauliEndpointMass brickworkRank (brickworkCellShock 0) (brickworkRank (b,1)) = _
  rw [pauliEndpointMass_cellShock, pauliEndpointMass_cellShock]
  by_cases hb : b = 0 <;> norm_num [hb]

/-- The literal full Haar schedule gives the exact endpoint-chain mean,
including the empty circuit and the single-cell boundary case. -/
theorem brickworkSchedule_initial_sign_mean (c T : ℕ) :
    (∑ P : PauliString (BrickworkSite c), pauliEndpointSign (P (Fin.last c,1)) *
      pauliLayerEvolution (brickworkGateSchedule c T)
        (pauliInitialVector (brickworkInitialZ c)) P) = endpointEvenMean c T := by
  classical
  cases T with
  | zero =>
    simp [brickworkGateSchedule, pauliLayerEvolution, pauliInitialVector,
      brickworkInitialZ, pauliEndpointSign, endpointEvenMean]
  | succ s =>
    rw [brickworkSchedule_action_succ, brickworkIterateOddEven_sign, brickworkInitialZ_cellMass]
    simp [pauliInitialVector, endpointEvenMean, Matrix.mulVec, dotProduct, mul_ite]

/-- Exact Haar mean of the actual quantum endpoint OTOC for every even depth
and every trace-one input matrix. -/
theorem brickworkEndpointOTOC_haar_mean (c T : ℕ)
    (ρ : QubitOperator (BrickworkSite c)) (hρ : Matrix.trace ρ = 1) :
    (∫ x, brickworkEndpointOTOC c T ρ x
      ∂Measure.pi (fun _ : Fin (T*(2*c+1)) => globalHaar TwoQubitBasis)) =
      (endpointEvenMean c T : ℂ) := by
  rw [brickworkEndpointOTOC_haar_markov c T ρ hρ, brickworkCircuit_markov]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (brickworkSchedule_initial_sign_mean c T)
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using h

/-- The actual circuit Haar mean has the exact finite binomial-image formula. -/
theorem brickworkEndpointOTOC_haar_mean_images (c s : ℕ)
    (ρ : QubitOperator (BrickworkSite (c+1))) (hρ : Matrix.trace ρ = 1) :
    (∫ x, brickworkEndpointOTOC (c+1) (s+1) ρ x
      ∂Measure.pi (fun _ : Fin ((s+1)*(2*(c+1)+1)) => globalHaar TwoQubitBasis)) =
      ((1 - (256/375 : ℝ) * ∑ u ∈ Finset.range s,
        endpointImageKernel (c+2) u ((c : ℤ)+1) : ℝ) : ℂ) := by
  rw [brickworkEndpointOTOC_haar_mean _ _ ρ hρ, endpointEvenMean_images]

theorem brickworkEndpointOTOC_haar_mean_oneCell (s : ℕ)
    (ρ : QubitOperator (BrickworkSite 0)) (hρ : Matrix.trace ρ = 1) :
    (∫ x, brickworkEndpointOTOC 0 (s+1) ρ x
      ∂Measure.pi (fun _ : Fin ((s+1)*(2*0+1)) => globalHaar TwoQubitBasis)) =
      (-1/15 : ℂ) := by
  rw [brickworkEndpointOTOC_haar_mean _ _ ρ hρ, endpointEvenMean_oneCell]
  norm_num

theorem brickworkEndpointOTOC_haar_mean_lightcone (c s : ℕ) (hlight : s < c+1)
    (ρ : QubitOperator (BrickworkSite (c+1))) (hρ : Matrix.trace ρ = 1) :
    (∫ x, brickworkEndpointOTOC (c+1) (s+1) ρ x
      ∂Measure.pi (fun _ : Fin ((s+1)*(2*(c+1)+1)) => globalHaar TwoQubitBasis)) = 1 := by
  rw [brickworkEndpointOTOC_haar_mean _ _ ρ hρ]
  change (endpointChainMean c s : ℂ) = 1
  rw [endpointChainMean_lightcone c s hlight]
  rfl

end Fluctuations
