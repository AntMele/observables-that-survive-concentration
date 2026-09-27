import Fluctuations.SimulationSamplingKernel
import Fluctuations.SimulationLocalCoordinate
import Fluctuations.SimulationAveraging

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Real form of the actual infinite-temperature first-order endpoint OTOC. -/
noncomputable def simulationCircuitOTOC (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (probe : Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) : ℝ :=
  amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
    (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n x)

theorem simulationCircuitOTOC_eq_trace
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    (simulationCircuitOTOC bond P₀ probe n x : ℂ) =
      globalOTOC (globalMaximallyMixedState (QubitState Site)) (pauliStringMatrix P₀)
        (pauliStringMatrix (pauliSiteZ probe)) 1 (pauliCircuitUnitary bond hbond n x) :=
  (pauliCircuit_infiniteTemperature_sign bond hbond P₀ probe n x).symm

theorem simulationCircuitOTOC_continuous (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (probe : Site) (n : ℕ) :
    Continuous (simulationCircuitOTOC bond P₀ probe n) := by
  have h := randomLinearEvolution_continuous (pauliCircuitTransfer bond)
    (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) n
  unfold simulationCircuitOTOC amplitudeSignReadout
  fun_prop

/-- The finite set of gate coordinates actually averaged by the algorithm. -/
def simulationErasedGates (n : ℕ) (retained : ℕ → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => retained i.val = false

lemma simulation_replace_erased (n : ℕ) (retained : ℕ → Bool)
    (x y : Fin n → TwoQubitUnitary) :
    replaceGateSubset (simulationErasedGates n retained) x y =
      retainedGateRealization retained (simulationFixedGates n x) y := by
  rw [retainedGateRealization_fixed]
  funext t
  cases h : retained t.val <;> simp [replaceGateSubset, simulationErasedGates, h]

/-- The paper's conditional mean, as a literal product Haar partial integral. -/
noncomputable def simulationCircuitMean (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (probe : Site) (n : ℕ) (retained : ℕ → Bool) : (Fin n → TwoQubitUnitary) → ℝ :=
  eraseSubsetAverage (globalHaar TwoQubitBasis) (simulationErasedGates n retained)
    (simulationCircuitOTOC bond P₀ probe n)

theorem simulationCircuitMean_continuous (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (probe : Site) (n : ℕ) (retained : ℕ → Bool) :
    Continuous (simulationCircuitMean bond P₀ probe n retained) :=
  eraseSubsetAverage_continuous _ _ _ (simulationCircuitOTOC_continuous bond P₀ probe n)

/-- The proved conditional mean is exactly the expectation of the constructed
sampler's final sign; this connects averaging error and sampling error. -/
theorem simulationCircuitMean_sampler
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (n : ℕ) (retained : ℕ → Bool)
    (x : Fin n → TwoQubitUnitary) :
    simulationCircuitMean bond P₀ probe n retained x =
      ∑ P, pauliEndpointSign (P probe) *
        (mixedPauliSampler bond hbond retained (simulationFixedGates n x) P₀ n).probability P := by
  simp_rw [simulationCircuitMean, eraseSubsetAverage, simulation_replace_erased,
    simulationCircuitOTOC, amplitudeSignReadout, mixedPauliSampler_output_probability]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  · intro P _
    have hc := (randomLinearEvolution_continuous (pauliCircuitTransfer bond)
      (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) n).comp
      ((retainedGateRealization_fixed_continuous n retained).comp
        ((continuous_const (y := x)).prodMk continuous_id))
    exact (continuous_const.mul ((continuous_apply P |>.comp hc).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The actual squared mass touching a gate, before applying that gate. -/
noncomputable def simulationCoordinateMass (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (n : ℕ) (t : Fin n) (x : Fin n → TwoQubitUnitary) : ℝ :=
  pauliGateActiveMass (bond t.val).1 (bond t.val).2
    (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) t.val
      (fun i => x ⟨i.val, lt_trans i.isLt t.isLt⟩))

lemma simulationCoordinateMass_nonneg (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (n : ℕ) (t : Fin n) (x : Fin n → TwoQubitUnitary) :
    0 ≤ simulationCoordinateMass bond P₀ n t x := pauliGateActiveMass_nonneg _ _ _

lemma simulationCoordinateMass_continuous (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (n : ℕ) (t : Fin n) :
    Continuous (simulationCoordinateMass bond P₀ n t) := by
  have hp : Continuous (fun x : Fin n → TwoQubitUnitary =>
      fun i : Fin t.val => x ⟨i.val, lt_trans i.isLt t.isLt⟩) := by fun_prop
  have hc := (randomLinearEvolution_continuous (pauliCircuitTransfer bond)
    (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) t.val).comp hp
  unfold simulationCoordinateMass pauliGateActiveMass amplitudeMass pauliGateActiveVector
  apply continuous_finset_sum
  intro P _
  split_ifs
  · exact continuous_const
  · exact (continuous_apply P |>.comp hc).pow 2

/-- The single-coordinate averaging error is at most four times the square
root of the actual expected prefix touching probability. -/
theorem simulationCoordinate_average_error
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (n : ℕ) (t : Fin n) :
    (∫ x, |simulationCircuitOTOC bond P₀ probe n x -
      eraseGateAverage (globalHaar TwoQubitBasis) t (simulationCircuitOTOC bond P₀ probe n) x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤
      4 * Real.sqrt (∫ x, simulationCoordinateMass bond P₀ n t x
        ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) := by
  let ν := globalHaar TwoQubitBasis
  let F := simulationCircuitOTOC bond P₀ probe n
  let w := simulationCoordinateMass bond P₀ n t
  have hF : Continuous F := simulationCircuitOTOC_continuous bond P₀ probe n
  have hw : Continuous w := simulationCoordinateMass_continuous bond P₀ n t
  have hs (x : Fin n → TwoQubitUnitary) (g : TwoQubitUnitary) :
      |F x - F (Function.update x t g)| ≤ 4 * Real.sqrt (w x) := by
    have h := pauliCircuit_coordinate_sign_change_fin bond hbond (pauliInitialVector P₀)
      (by simp [amplitudeMass, pauliInitialVector]) probe n x t (x t) g
    simpa only [Function.update_eq_self] using h
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
      (simulation_integral_sqrt_le w hw (simulationCoordinateMass_nonneg bond P₀ n t)) (by norm_num)

end Fluctuations
