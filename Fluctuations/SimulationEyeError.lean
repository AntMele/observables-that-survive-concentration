import Fluctuations.SimulationTailCausal

open MeasureTheory
namespace Fluctuations
noncomputable section

/-- Convert the physical Gaussian touching tail to the manuscript's
uniform error budget outside a strip of width `R sqrt u`. -/
lemma simulation_sqrt_tail_error (p u A R : ℝ) (hu : 0 < u) (hp : 0 ≤ p)
    (hbound : p ≤ (5/2)*Real.exp (-A^2/(200*u)))
    (hgap : 3*R*Real.sqrt u ≤ |A|) (hR : 0 ≤ R) :
    4*Real.sqrt p ≤ 40*Real.exp (-R^2/100) := by
  have hsq : 9*R^2*u ≤ A^2 := by
    have h := sq_le_sq₀ (by positivity : 0 ≤ 3*R*Real.sqrt u) (abs_nonneg A)
    have hs := h.mpr hgap
    rw [sq_abs] at hs
    nlinarith [Real.sq_sqrt hu.le]
  have he : -A^2/(200*u) ≤ -R^2/50 := by
    apply (div_le_iff₀ (by positivity : 0 < 200*u)).2
    nlinarith [sq_nonneg R]
  have hb := hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num : (0:ℝ) ≤ 5/2))
  have hex : (Real.exp (-R^2/100))^2 = Real.exp (-R^2/50) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hepos : 0 < Real.exp (-R^2/100) := Real.exp_pos _
  nlinarith [Real.sq_sqrt hp, sq_nonneg (Real.exp (-R^2/100))]

/-- Once the exact causal exclusions are removed, an erased physical gate
lies strictly outside the paper's diffusive strip. -/
lemma simulationOutsideGate_strip (c T : ℕ) (R : ℝ) (z : Fin (T*(2*c+1)))
    (hz : ¬ simulationRetainedGate c T R z)
    (hforward : simulationGatePosition c T z ≤ simulationGateTime c T z)
    (hbackward : 2*(c+1)-simulationGatePosition c T z ≤ 2*T-simulationGateTime c T z) :
    R*simulationSigma (2*T) (simulationGateTime c T z) (simulationGatePosition c T z) <
      |(simulationGateTime c T z:ℝ)-5*(simulationGatePosition c T z:ℝ)/3| := by
  have ht := simulationGateTime_bounds c T z
  have hp := simulationGatePosition_bounds c T z
  have hpar := simulationGate_parity c T z
  have htd : simulationGateTime c T z < 2*T := by omega
  apply lt_of_not_ge
  intro hstrip
  apply hz
  unfold simulationRetainedGate simulationEyePositions
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  constructor
  · exact_mod_cast hpar
  constructor
  · exact_mod_cast hforward
  constructor
  · have hb : 2*(c+1)+simulationGateTime c T z ≤ 2*T+simulationGatePosition c T z := by omega
    have hb' : (2*(c+1):ℝ)+(simulationGateTime c T z:ℝ) ≤ 2*T+(simulationGatePosition c T z:ℝ) := by exact_mod_cast hb
    push_cast
    linarith
  constructor
  · exact htd
  · simpa only [Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] using hstrip

/-- Every discarded gate has the paper's uniform expected error, for the
literal endpoint OTOC of the independent Haar brickwork circuit. -/
theorem simulationOutsideGate_error (c T : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcritical : 3*(2*T:ℝ) = 5*(2*(c+1):ℝ))
    (z : Fin (T*(2*c+1))) (hz : ¬ simulationRetainedGate c T R z) :
    (∫ x, |simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
        (Fin.last c,(1:Fin 2)) (T*(2*c+1)) x -
      eraseGateAverage (globalHaar TwoQubitBasis) z
        (simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
          (Fin.last c,(1:Fin 2)) (T*(2*c+1))) x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤
      40*Real.exp (-R^2/100) := by
  have hf := simulationCoordinate_average_error (brickworkCircuitBond c T)
    (brickworkCircuitBond_distinct c T) (brickworkInitialZ c)
    (Fin.last c,(1:Fin 2)) (T*(2*c+1)) z
  rw [simulationCoordinateMass_expected] at hf
  have hb := simulationCoordinate_average_error_backward (brickworkCircuitBond c T)
    (brickworkCircuitBond_distinct c T) (0,(0:Fin 2))
    (Fin.last c,(1:Fin 2)) (T*(2*c+1)) z
  change (∫ x, |simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
        (Fin.last c,(1:Fin 2)) (T*(2*c+1)) x -
      eraseGateAverage (globalHaar TwoQubitBasis) z
        (simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
          (Fin.last c,(1:Fin 2)) (T*(2*c+1))) x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤ _ at hb
  rw [simulationBackwardMass_expected] at hb
  by_cases hcf : simulationGateTime c T z < simulationGatePosition c T z
  · rw [simulationForwardTouch_causal c T z hcf,Real.sqrt_zero,mul_zero] at hf
    exact hf.trans (by positivity)
  by_cases hcb : 2*T-simulationGateTime c T z < 2*(c+1)-simulationGatePosition c T z
  · rw [simulationBackwardTouch_causal c T z hcb,Real.sqrt_zero,mul_zero] at hb
    exact hb.trans (by positivity)
  have hstrip := simulationOutsideGate_strip c T R z hz (by omega) (by omega)
  have htime := simulationGateTime_bounds c T z
  have hpos := simulationGatePosition_bounds c T z
  have htpos : (0:ℝ) < simulationGateTime c T z := by exact_mod_cast htime.1
  have htd : simulationGateTime c T z < 2*T := by omega
  by_cases hfront : (simulationGateTime c T z:ℝ) ≤ 5*(simulationGatePosition c T z:ℝ)/3
  · unfold simulationSigma at hstrip
    rw [if_pos hfront] at hstrip
    apply hf.trans
    apply simulation_sqrt_tail_error (simulationForwardTouch c T z) _
      (5*(simulationGatePosition c T z:ℝ)-3*(simulationGateTime c T z:ℝ)) R htpos
      (simulationForwardTouch_nonneg c T z) _ _ hR
    · have h := simulationForwardTouch_gaussian c T z
      unfold simulationTouchTail at h
      rwa [max_eq_left (by linarith)] at h
    · rw [abs_of_nonneg (by linarith : 0 ≤ 5*(simulationGatePosition c T z:ℝ)-3*(simulationGateTime c T z:ℝ))]
      rw [abs_of_nonpos (by linarith)] at hstrip
      linarith
  · unfold simulationSigma at hstrip
    rw [if_neg hfront] at hstrip
    have hut : ((2*T-simulationGateTime c T z:ℕ):ℝ) = 2*T-(simulationGateTime c T z:ℝ) := by
      rw [Nat.cast_sub htime.2]
      norm_cast
    have huv : ((2*(c+1)-simulationGatePosition c T z:ℕ):ℝ) = 2*(c+1)-(simulationGatePosition c T z:ℝ) := by
      rw [Nat.cast_sub hpos.2.le]
      norm_cast
    have hu : (0:ℝ) < 2*T-(simulationGateTime c T z:ℝ) := by
      have hh : (simulationGateTime c T z:ℝ) < 2*T := by exact_mod_cast htd
      linarith
    apply hb.trans
    apply simulation_sqrt_tail_error (simulationBackwardTouch c T z) _
      (3*(simulationGateTime c T z:ℝ)-5*(simulationGatePosition c T z:ℝ)) R hu
      (simulationBackwardTouch_nonneg c T z) _ _ hR
    · have h := simulationBackwardTouch_gaussian c T z htd
      unfold simulationTouchTail at h
      rw [hut,huv] at h
      have he : 5*(2*(c+1)-(simulationGatePosition c T z:ℝ))-
          3*(2*T-(simulationGateTime c T z:ℝ)) =
          3*(simulationGateTime c T z:ℝ)-5*(simulationGatePosition c T z:ℝ) := by linarith
      rw [he,max_eq_left (by linarith)] at h
      exact h
    · rw [abs_of_nonneg (by linarith : 0 ≤ 3*(simulationGateTime c T z:ℝ)-5*(simulationGatePosition c T z:ℝ))]
      rw [abs_of_nonneg (by linarith)] at hstrip
      linarith

/-- Actual conditional-mean error of the complete Haar circuit, with the
paper's explicit `100/3` coefficient and the same eye used by the sampler. -/
theorem simulationEye_bias (c T : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcritical : 3*(2*T:ℝ) = 5*(2*(c+1):ℝ)) :
    (∫ x, |simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
        (Fin.last c,(1:Fin 2)) (T*(2*c+1)) x -
      simulationCircuitMean (brickworkCircuitBond c T) (brickworkInitialZ c)
        (Fin.last c,(1:Fin 2)) (T*(2*c+1)) (simulationRetainedSchedule c T R) x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤
      (100/3)*(2*(c+1):ℝ)^2*Real.exp (-R^2/100) := by
  classical
  let s := simulationErasedGates (T*(2*c+1)) (simulationRetainedSchedule c T R)
  let F := simulationCircuitOTOC (brickworkCircuitBond c T) (brickworkInitialZ c)
    (Fin.last c,(1:Fin 2)) (T*(2*c+1))
  have h := eraseSubsetAverage_L1_error_uniform (globalHaar TwoQubitBasis) s F
    (simulationCircuitOTOC_continuous _ _ _ _) (40*Real.exp (-R^2/100)) (by
      intro z hz
      apply simulationOutsideGate_error c T R hR hcritical z
      have hz' : simulationRetainedSchedule c T R z.val = false := (Finset.mem_filter.mp hz).2
      rw [simulationRetainedSchedule_at] at hz'
      exact of_decide_eq_false hz')
  change (∫ x, |F x-eraseSubsetAverage (globalHaar TwoQubitBasis) s F x|
    ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤ _
  apply h.trans
  have hcard : s.card ≤ T*(2*c+1) := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hcardR : (s.card:ℝ) ≤ (T:ℝ)*(2*c+1) := by exact_mod_cast hcard
  have hcount : (T:ℝ)*(2*c+1)*40 ≤ (100/3)*(2*(c+1):ℝ)^2 := by
    nlinarith
  calc
    _ ≤ ((T:ℝ)*(2*c+1))*(40*Real.exp (-R^2/100)) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le

end
end Fluctuations
