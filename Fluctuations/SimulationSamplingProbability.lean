import Fluctuations.SimulationConcentration
import Fluctuations.SimulationMixedCircuitOTOC
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Fluctuations

set_option maxHeartbeats 800000

section FiniteLaw
variable {Q : Type*} [Fintype Q]

/-- The actual finite output distribution obtained by sampling squared amplitudes. -/
noncomputable def amplitudeOutputPMF (E : FiniteAmplitudeEnsemble Q) : PMF Q :=
  PMF.ofFintype (fun q => ENNReal.ofReal (E.probability q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => E.probability_nonneg q), E.probability_total]
    simp)

variable [MeasurableSpace Q] [MeasurableSingletonClass Q]

@[simp] theorem amplitudeOutputPMF_singleton (E : FiniteAmplitudeEnsemble Q) (q : Q) :
    (amplitudeOutputPMF E).toMeasure.real {q} = E.probability q := by
  rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton q)]
  exact ENNReal.toReal_ofReal (E.probability_nonneg q)

theorem amplitudeOutputPMF_mean (E : FiniteAmplitudeEnsemble Q) (f : Q → ℝ) :
    (∫ q, f q ∂(amplitudeOutputPMF E).toMeasure) = ∑ q, f q * E.probability q := by
  rw [integral_fintype f Integrable.of_finite]
  simp only [amplitudeOutputPMF_singleton, smul_eq_mul, mul_comm]

/-- Independent bounded observations on a finite probability space. -/
theorem simulation_iid_average_tail (μ : Measure Q) [IsProbabilityMeasure μ]
    (f : Q → ℝ) (hf : ∀ q, |f q| ≤ 1) (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {x | ε / 2 ≤ |(∑ i, f (x i)) / N - ∫ q, f q ∂μ|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 8) := by
  have hm : Measurable f := measurable_of_finite f
  refine simulation_sample_average_tail (μ := Measure.pi (fun _ : Fin N => μ))
    N hN (fun i x => f (x i)) ?_ ?_ ?_ (∫ q, f q ∂μ) ?_ ε hε
  · exact iIndepFun_pi fun _ => hm.aemeasurable
  · intro i
    exact (hm.comp (measurable_pi_apply i)).aemeasurable
  · intro i
    exact Filter.Eventually.of_forall fun x => abs_le.mp (hf (x i))
  · intro i
    have hp := measurePreserving_eval (fun _ : Fin N => μ) i
    calc
      _ = ∫ q, f q ∂(Measure.pi (fun _ : Fin N => μ)).map (Function.eval i) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]

/-- Independent actual samples from the finite output law satisfy the desired
Monte Carlo bound around its proved mean. -/
theorem amplitudeOutputPMF_samples_tail (E : FiniteAmplitudeEnsemble Q)
    (f : Q → ℝ) (hf : ∀ q, |f q| ≤ 1) (N : ℕ) (hN : 0 < N)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => (amplitudeOutputPMF E).toMeasure)).real
      {x | ε / 2 ≤ |(∑ i, f (x i)) / N - ∑ q, f q * E.probability q|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 8) := by
  simpa only [amplitudeOutputPMF_mean] using
    simulation_iid_average_tail (amplitudeOutputPMF E).toMeasure f hf N hN ε hε

end FiniteLaw

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The Monte Carlo guarantee for the constructed coherent Pauli sampler. -/
theorem mixedPauliSampler_endpoint_samples_tail
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (j : Site) (n N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 ≤ ε) :
    let E := mixedPauliSampler bond hbond retained gates P₀ n
    (Measure.pi (fun _ : Fin N => (amplitudeOutputPMF E).toMeasure)).real
      {x | ε / 2 ≤ |(∑ i, pauliEndpointSign (x i j)) / N -
        ∑ P, pauliEndpointSign (P j) * E.probability P|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 8) := by
  exact amplitudeOutputPMF_samples_tail _ _ (pauliSampler_endpoint_readout_abs j) N hN ε hε

end Fluctuations
