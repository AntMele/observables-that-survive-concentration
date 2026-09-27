import Fluctuations.BrickworkEndpointOTOC
import Fluctuations.EndpointVarianceAssembly

/-! The concrete first-order endpoint fluctuation theorem. There are
`n = 2*(c+2)` qubits and `d = 2*T` alternating layers. Every gate is an actual
independent Haar U(4) matrix embedded on its two physical sites. -/

open MeasureTheory
open scoped BigOperators

namespace Fluctuations
noncomputable section

/-- Explicit inverse-square single-gate influence for every even gate in the
central diffusive eye. The conditional mean is a proved circuit identity. -/
theorem otoc1_endpoint_gate_influence {c T : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlarge : 12*(C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2)))
    (ρ : QubitOperator (BrickworkSite (c+1))) (hρ : Matrix.trace ρ = 1)
    (z : Fin T × Fin (c+1)) (hz : z ∈ endpointPhysicalEye c T) :
    endpointInfluenceConstant C / (2*(c+2) : ℝ)^2 ≤
      complexVariance (globalHaar TwoQubitBasis)
        (coordinateAverage (fun _ : Fin (T*(2*(c+1)+1)) => globalHaar TwoQubitBasis)
          (brickworkEvenGateIndex z) (brickworkEndpointOTOC (c+1) T ρ)) := by
  have hinterior := endpointPhysicalEye_interior hC hlarge hfront hz
  have he := funext (brickworkEndpointOTOC_conditional_mean (c+1) T ρ hρ z hinterior)
  rw [he]
  have hf := endpointEye_factors_lower c T z.1.val z.2 hC hlarge hfront
    (mem_endpointPhysicalEye.mp hz)
  have hk : 0 ≤ endpointFrontConstant C / Real.sqrt (2*(c+2)) := by
    exact (div_pos (endpointFrontConstant_pos C) (Real.sqrt_pos.mpr (by positivity))).le
  apply endpoint_affine_influence_lower (by positivity) hf.1
  linarith [hf.2]

/-- Uniform front-window variance lower bound for the literal endpoint OTOC.
No mean-change, design-convergence, reverse-variance, Pauli-mixing, conditional
mean, propagation, or gate-count premise remains. -/
theorem otoc1_endpoint_variance_lower {c T : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlarge : 12*(C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2)))
    (ρ : QubitOperator (BrickworkSite (c+1))) (hρ : Matrix.trace ρ = 1) :
    endpointInfluenceConstant C / (24*Real.sqrt (2*(c+2))) ≤
      complexVariance (Measure.pi
        (fun _ : Fin (T*(2*(c+1)+1)) => globalHaar TwoQubitBasis))
        (brickworkEndpointOTOC (c+1) T ρ) := by
  apply endpointVariance_of_conditional_formula hC hlarge hfront brickworkEvenGateIndex
    (brickworkEvenGateIndex_injective (c+1) T)
    (brickworkEndpointOTOC (c+1) T ρ) (brickworkEndpointOTOC (c+1) T ρ).continuous
    (∫ x, brickworkEndpointOTOC (c+1) T ρ x ∂Measure.pi
      (fun _ : Fin (T*(2*(c+1)+1)) => globalHaar TwoQubitBasis))
  intro z hz U
  exact brickworkEndpointOTOC_conditional_mean (c+1) T ρ hρ z
    (endpointPhysicalEye_interior hC hlarge hfront hz) U

/-- The actual physical gate indices selected by the eye. -/
def otoc1InfluentialGates (c T : ℕ) : Finset (Fin (T*(2*(c+1)+1))) :=
  (endpointPhysicalEye c T).image brickworkEvenGateIndex

/-- A concrete set of Θ(n^(3/2)) gates, each contributing at least a positive
constant times n⁻² to the variance through its own conditional mean. -/
theorem otoc1_many_influential_gates {c T : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlarge : 12*(C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2)))
    (ρ : QubitOperator (BrickworkSite (c+1))) (hρ : Matrix.trace ρ = 1) :
    (2*(c+2) : ℝ)*Real.sqrt (2*(c+2))/24 ≤ ((otoc1InfluentialGates c T).card : ℝ) ∧
    ((otoc1InfluentialGates c T).card : ℝ) ≤
      2*(2*(c+2) : ℝ)*Real.sqrt (2*(c+2))/3 ∧
    ∀ i ∈ otoc1InfluentialGates c T,
      endpointInfluenceConstant C / (2*(c+2) : ℝ)^2 ≤
        complexVariance (globalHaar TwoQubitBasis)
          (coordinateAverage (fun _ : Fin (T*(2*(c+1)+1)) => globalHaar TwoQubitBasis)
            i (brickworkEndpointOTOC (c+1) T ρ)) := by
  have hc := endpointPhysicalEye_card_bounds hC hlarge hfront
  have he : (otoc1InfluentialGates c T).card = (endpointPhysicalEye c T).card := by
    exact Finset.card_image_of_injective _ (brickworkEvenGateIndex_injective (c+1) T)
  refine ⟨by simpa [he] using hc.1, by simpa [he] using hc.2, ?_⟩
  intro i hi
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
  exact otoc1_endpoint_gate_influence hC hlarge hfront ρ hρ z hz

end
end Fluctuations
