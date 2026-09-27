import Fluctuations.SimulationCircuitAverage
import Fluctuations.SimulationBackwardInfluence

open MeasureTheory

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Touching mass of the actual backwards-evolved probe at a gate. -/
noncomputable def simulationBackwardMass (bond : ℕ → Site × Site)
    (probe : Site) (n : ℕ) (t : Fin n) (x : Fin n → TwoQubitUnitary) : ℝ :=
  pauliGateActiveMass (bond t.val).1 (bond t.val).2
    (randomLinearEvolution (pauliCircuitTransfer (reverseCircuitBond bond n))
      (pauliInitialVector (pauliSiteZ probe)) t.rev.val
      (fun i => reverseGateRealization x ⟨i.val, lt_trans i.isLt t.rev.isLt⟩))

lemma simulationBackwardMass_nonneg (bond : ℕ → Site × Site)
    (probe : Site) (n : ℕ) (t : Fin n) (x : Fin n → TwoQubitUnitary) :
    0 ≤ simulationBackwardMass bond probe n t x := pauliGateActiveMass_nonneg _ _ _

lemma simulationBackwardMass_continuous (bond : ℕ → Site × Site)
    (probe : Site) (n : ℕ) (t : Fin n) :
    Continuous (simulationBackwardMass bond probe n t) := by
  have hp : Continuous (fun x : Fin n → TwoQubitUnitary =>
      fun i : Fin t.rev.val => reverseGateRealization x ⟨i.val, lt_trans i.isLt t.rev.isLt⟩) := by
    unfold reverseGateRealization
    fun_prop
  have hc := (randomLinearEvolution_continuous
    (pauliCircuitTransfer (reverseCircuitBond bond n))
    (pauliCircuitTransfer_continuous (reverseCircuitBond bond n))
    (pauliInitialVector (pauliSiteZ probe)) t.rev.val).comp hp
  unfold simulationBackwardMass pauliGateActiveMass amplitudeMass pauliGateActiveVector
  apply continuous_finset_sum
  intro P _
  split_ifs
  · exact continuous_const
  · exact (continuous_apply P |>.comp hc).pow 2

/-- The backwards influence bound controls the very same coordinate average
as the forward bound; no independently defined approximate target is used. -/
theorem simulationCoordinate_average_error_backward
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (initial probe : Site) (n : ℕ) (t : Fin n) :
    (∫ x, |simulationCircuitOTOC bond (pauliSiteZ initial) probe n x -
      eraseGateAverage (globalHaar TwoQubitBasis) t
        (simulationCircuitOTOC bond (pauliSiteZ initial) probe n) x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤
      4 * Real.sqrt (∫ x, simulationBackwardMass bond probe n t x
        ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) := by
  let ν := globalHaar TwoQubitBasis
  let F := simulationCircuitOTOC bond (pauliSiteZ initial) probe n
  let w := simulationBackwardMass bond probe n t
  have hF : Continuous F := simulationCircuitOTOC_continuous bond (pauliSiteZ initial) probe n
  have hw : Continuous w := simulationBackwardMass_continuous bond probe n t
  have hs (x : Fin n → TwoQubitUnitary) (g : TwoQubitUnitary) :
      |F x - F (Function.update x t g)| ≤ 4 * Real.sqrt (w x) := by
    have h := pauliCircuit_coordinate_backward_otoc_change bond hbond initial probe n x t (x t) g
    simp_rw [← simulationCircuitOTOC_eq_trace, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, Function.update_eq_self] at h
    exact h
  calc
    _ ≤ ∫ x, 4 * Real.sqrt (w x) ∂Measure.pi (fun _ : Fin n => ν) := by
      apply integral_mono
      · exact (hF.sub (eraseGateAverage_continuous ν t F hF)).abs.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul hw.sqrt).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact eraseGateAverage_error_le ν t F hF _ hs
    _ = 4 * ∫ x, Real.sqrt (w x) ∂Measure.pi (fun _ : Fin n => ν) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (simulation_integral_sqrt_le w hw (simulationBackwardMass_nonneg bond probe n t)) (by norm_num)

end Fluctuations
