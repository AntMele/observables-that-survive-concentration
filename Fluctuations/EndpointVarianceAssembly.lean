import Fluctuations.EndpointPhysicalEye
import Fluctuations.CoordinateAverages
import Fluctuations.LocalPauliBalance

/-! Quantitative assembly of the endpoint variance bound. The circuit-specific
conditional-mean formula is explicitly the input to this intermediate theorem;
the concrete circuit theorem must discharge that input. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Fluctuations
noncomputable section

def endpointInfluenceConstant (C : ℝ) : ℝ :=
  (256/225 : ℝ) * variance localPauliA (globalHaar TwoQubitBasis) * endpointFrontConstant C ^ 4

theorem endpointInfluenceConstant_pos (C : ℝ) : 0 < endpointInfluenceConstant C := by
  unfold endpointInfluenceConstant
  exact mul_pos (mul_pos (by norm_num) localPauliA_variance_pos)
    (pow_pos (endpointFrontConstant_pos C) _)

theorem endpoint_affine_influence_lower {n C P F : ℝ} (hn : 0 < n)
    (hP : endpointFrontConstant C / Real.sqrt n ≤ P)
    (hF : endpointFrontConstant C / Real.sqrt n ≤ F) (a : ℂ) :
    endpointInfluenceConstant C / n^2 ≤
      complexVariance (globalHaar TwoQubitBasis)
        (fun U => a - (16/15 : ℂ)*(P : ℂ)*(F : ℂ)*((localPauliA U : ℂ)-4/5)) := by
  rw [gate_affine_variance localPauliA_memLp]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hk : 0 < endpointFrontConstant C / Real.sqrt n :=
    div_pos (endpointFrontConstant_pos C) hs
  have hp : 0 ≤ P := le_trans hk.le hP
  have hprod : (endpointFrontConstant C / Real.sqrt n)^2 ≤ P*F := by
    simpa [pow_two] using mul_le_mul hP hF hk.le hp
  have hsq : ((endpointFrontConstant C / Real.sqrt n)^2)^2 ≤ (P*F)^2 :=
    (sq_le_sq₀ (sq_nonneg _) (le_trans (sq_nonneg _) hprod)).mpr hprod
  have hv := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 256/225))
    localPauliA_variance_pos.le
  have hid : endpointInfluenceConstant C / n^2 =
      (256/225 : ℝ)*((endpointFrontConstant C / Real.sqrt n)^2)^2*
        variance localPauliA (globalHaar TwoQubitBasis) := by
    unfold endpointInfluenceConstant
    have hs₂ := Real.sq_sqrt hn.le
    have hs₄ : Real.sqrt n ^ 4 = n^2 := by
      calc
        _ = (Real.sqrt n ^ 2)^2 := by ring
        _ = _ := by rw [hs₂]
    field_simp
    rw [hs₄]
  rwa [hid]

section Assembly
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The front-window variance conclusion from the precise conditional formula.
All propagation estimates, actual lattice counts, the positive local Haar
variance, and summation of independent-gate influences are proved upstream. -/
theorem endpointVariance_of_conditional_formula {c T : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hlarge : 12*(C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2)))
    (gate : Fin T × Fin (c+1) → ι) (hgate : Function.Injective gate)
    (X : (ι → TwoQubitUnitary) → ℂ) (hX : Continuous X) (a : ℂ)
    (hconditional : ∀ z ∈ endpointPhysicalEye c T, ∀ U : TwoQubitUnitary,
      coordinateAverage (fun _ : ι => globalHaar TwoQubitBasis) (gate z) X U =
        a - (16/15 : ℂ)*(endpointPastFactor (c+1) z.1.val z.2 : ℂ)*
          (endpointFutureFactor (c+1) (T-z.1.val-2) z.2 : ℂ)*
          ((localPauliA U : ℂ)-4/5)) :
    endpointInfluenceConstant C / (24*Real.sqrt (2*(c+2))) ≤
      complexVariance (Measure.pi (fun _ : ι => globalHaar TwoQubitBasis)) X := by
  let n : ℝ := 2*(c+2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hlocal (z : Fin T × Fin (c+1)) (hz : z ∈ endpointPhysicalEye c T) :
      endpointInfluenceConstant C / n^2 ≤ complexVariance (globalHaar TwoQubitBasis)
        (coordinateAverage (fun _ : ι => globalHaar TwoQubitBasis) (gate z) X) := by
    have hf := endpointEye_factors_lower c T z.1.val z.2 hC hlarge hfront
      (mem_endpointPhysicalEye.mp hz)
    have hF : endpointFrontConstant C / Real.sqrt n ≤
        endpointFutureFactor (c+1) (T-z.1.val-2) z.2 := by
      have hk : 0 ≤ endpointFrontConstant C / Real.sqrt n := by
        exact (div_pos (endpointFrontConstant_pos C) (Real.sqrt_pos.mpr hn)).le
      dsimp [n] at hk ⊢
      linarith [hf.2]
    have he : coordinateAverage (fun _ : ι => globalHaar TwoQubitBasis) (gate z) X =
        fun U => a - (16/15 : ℂ)*(endpointPastFactor (c+1) z.1.val z.2 : ℂ)*
          (endpointFutureFactor (c+1) (T-z.1.val-2) z.2 : ℂ)*
          ((localPauliA U : ℂ)-4/5) := funext (hconditional z hz)
    rw [he]
    exact endpoint_affine_influence_lower hn hf.1 hF a
  let s := (endpointPhysicalEye c T).image gate
  have hc := (endpointPhysicalEye_card_bounds hC hlarge hfront).1
  have hcard : n*Real.sqrt n/24 ≤ (s.card : ℝ) := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hgate]
    exact hc
  have hsum := sum_coordinateAverage_variance_le
    (fun _ : ι => globalHaar TwoQubitBasis) s X hX
  have hbelow : (s.card : ℝ)*(endpointInfluenceConstant C/n^2) ≤
      ∑ i ∈ s, complexVariance (globalHaar TwoQubitBasis)
        (coordinateAverage (fun _ : ι => globalHaar TwoQubitBasis) i X) := by
    calc
      _ = ∑ _i ∈ s, endpointInfluenceConstant C/n^2 := by simp
      _ ≤ _ := ?_
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    exact hlocal z hz
  have hm := mul_le_mul_of_nonneg_right hcard
    (div_nonneg (endpointInfluenceConstant_pos C).le (sq_nonneg n))
  have hid : (n*Real.sqrt n/24)*(endpointInfluenceConstant C/n^2) =
      endpointInfluenceConstant C/(24*Real.sqrt n) := by
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
    have hs₂ := Real.sq_sqrt hn.le
    field_simp
    rw [hs₂]
  rw [hid] at hm
  exact hm.trans (hbelow.trans hsum)

end Assembly
end
end Fluctuations
