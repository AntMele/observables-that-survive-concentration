import Fluctuations.SimulationCircuitAverage
import Fluctuations.SimulationJointProbability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The estimator actually averages independently sampled endpoint signs. -/
noncomputable def simulationEstimator (probe : Site) (N : ℕ)
    (y : Fin N → PauliString Site) : ℝ := (∑ i, pauliEndpointSign (y i probe)) / N

/-- General accuracy assembly for the constructed sampler, with the one
remaining input being its circuit-averaging bias. The physical eye theorem
discharges that input separately. -/
theorem simulationSampler_joint_failure
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (n N : ℕ) (hN : 0 < N)
    (retained : ℕ → Bool) (ε : ℝ) (hε : 0 < ε) (b : ℝ)
    (hb : (∫ x, |simulationCircuitOTOC bond P₀ probe n x -
      simulationCircuitMean bond P₀ probe n retained x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤ b) :
    ((Measure.pi (fun _ : Fin n => globalHaar TwoQubitBasis)) ⊗ₘ
      mixedPauliSamplerKernel bond hbond retained P₀ n N).real
      {z | ε ≤ |simulationEstimator probe N z.2 - simulationCircuitOTOC bond P₀ probe n z.1|} ≤
      2 * b / ε + 2 * Real.exp (-(N : ℝ) * ε ^ 2 / 8) := by
  have hi : Integrable (fun x => |simulationCircuitOTOC bond P₀ probe n x -
      simulationCircuitMean bond P₀ probe n retained x|)
      (Measure.pi (fun _ => globalHaar TwoQubitBasis)) :=
    ((simulationCircuitOTOC_continuous bond P₀ probe n).sub
      (simulationCircuitMean_continuous bond P₀ probe n retained)).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine simulation_joint_failure
    (Measure.pi (fun _ : Fin n => globalHaar TwoQubitBasis))
    (mixedPauliSamplerKernel bond hbond retained P₀ n N)
    (simulationCircuitOTOC bond P₀ probe n) (simulationCircuitMean bond P₀ probe n retained)
    (simulationEstimator probe N)
    (simulationCircuitOTOC_continuous bond P₀ probe n).measurable
    (simulationCircuitMean_continuous bond P₀ probe n retained).measurable
    (measurable_of_finite _) hi ε hε b _ (by positivity) hb ?_
  intro x
  rw [simulationCircuitMean_sampler bond hbond]
  exact mixedPauliSampler_endpoint_samples_tail bond hbond retained
    (simulationFixedGates n x) P₀ probe n N hN ε hε.le

/-- The same assembly with the exact radius/sample-count choices of the paper. -/
theorem simulationSampler_joint_success_parameters
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (n qubits : ℕ) (hq : 0 < qubits)
    (retained : ℕ → Bool) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hb : (∫ x, |simulationCircuitOTOC bond P₀ probe n x -
      simulationCircuitMean bond P₀ probe n retained x|
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) ≤
      (100 / 3) * (qubits : ℝ)^2 * Real.exp (-(simulationRadius qubits ε δ)^2 / 100)) :
    1 - δ ≤ ((Measure.pi (fun _ : Fin n => globalHaar TwoQubitBasis)) ⊗ₘ
      mixedPauliSamplerKernel bond hbond retained P₀ n (simulationSampleCount ε δ)).real
      {z | |simulationEstimator probe (simulationSampleCount ε δ) z.2 -
        simulationCircuitOTOC bond P₀ probe n z.1| ≤ ε} := by
  apply simulation_joint_success_of_failure _ _ _ _
    (simulationCircuitOTOC_continuous bond P₀ probe n).measurable (measurable_of_finite _)
  have h := simulationSampler_joint_failure bond hbond P₀ probe n
    (simulationSampleCount ε δ) (simulationSampleCount_positive hε hδ hδ1)
    retained ε hε _ hb
  have hp := simulationParameter_failure_sum hq hε hε1 hδ hδ1
  have he : 2 * ((100 / 3) * (qubits : ℝ)^2 *
      Real.exp (-(simulationRadius qubits ε δ)^2 / 100)) / ε =
      200 * (qubits : ℝ)^2 / (3 * ε) * Real.exp (-(simulationRadius qubits ε δ)^2 / 100) := by ring
  rw [he] at h
  exact h.trans hp

end Fluctuations
