import Fluctuations.SimulationSamplingProbability
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Fluctuations

set_option maxHeartbeats 800000

section OutputKernel
variable {C Q : Type*} [MeasurableSpace C] [Fintype Q]
  [MeasurableSpace Q] [MeasurableSingletonClass Q]

lemma amplitudeOutputSamples_singleton (E : FiniteAmplitudeEnsemble Q)
    (N : ℕ) (y : Fin N → Q) :
    (Measure.pi (fun _ : Fin N => (amplitudeOutputPMF E).toMeasure)) {y} =
      ∏ i, ENNReal.ofReal (E.probability (y i)) := by
  rw [← Set.univ_pi_singleton y, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- A genuine probability kernel for independent repetitions of the sampler,
allowing its finite output probabilities to depend on the retained circuit. -/
noncomputable def amplitudeOutputKernel (E : C → FiniteAmplitudeEnsemble Q)
    (hE : ∀ q, Measurable (fun x => (E x).probability q)) (N : ℕ) : Kernel C (Fin N → Q) where
  toFun x := Measure.pi (fun _ : Fin N => (amplitudeOutputPMF (E x)).toMeasure)
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he (x : C) :
        (Measure.pi (fun _ : Fin N => (amplitudeOutputPMF (E x)).toMeasure)) s =
          ∑ y ∈ s.toFinset, ∏ i, ENNReal.ofReal ((E x).probability (y i)) := by
      rw [← Set.coe_toFinset s, ← sum_measure_singleton]
      simp only [amplitudeOutputSamples_singleton, Finset.toFinset_coe]
    simp_rw [he]
    apply Finset.measurable_sum
    intro y _
    exact Finset.measurable_prod _ fun i _ => (hE (y i)).ennreal_ofReal

instance amplitudeOutputKernel_isMarkov (E : C → FiniteAmplitudeEnsemble Q)
    (hE : ∀ q, Measurable (fun x => (E x).probability q)) (N : ℕ) :
    IsMarkovKernel (amplitudeOutputKernel E hE N) := by
  constructor
  intro x
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => (amplitudeOutputPMF (E x)).toMeasure))
  infer_instance

end OutputKernel

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Extend the actual finite gate input by identities beyond its end. -/
def simulationFixedGates (n : ℕ) (x : Fin n → TwoQubitUnitary) (t : ℕ) : TwoQubitUnitary :=
  if h : t < n then x ⟨t, h⟩ else 1

lemma retainedGateRealization_fixed (n : ℕ) (retained : ℕ → Bool)
    (x y : Fin n → TwoQubitUnitary) :
    retainedGateRealization retained (simulationFixedGates n x) y =
      fun t => if retained t.val then x t else y t := by
  funext t
  simp [retainedGateRealization, simulationFixedGates, t.isLt]

lemma retainedGateRealization_fixed_continuous (n : ℕ) (retained : ℕ → Bool) :
    Continuous (fun p : (Fin n → TwoQubitUnitary) × (Fin n → TwoQubitUnitary) =>
      retainedGateRealization retained (simulationFixedGates n p.1) p.2) := by
  simp_rw [retainedGateRealization_fixed]
  apply continuous_pi
  intro t
  cases retained t.val <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-- The actual sampler law varies continuously with the retained gate values.
The zero-branch normalization has no effect on these output probabilities. -/
theorem mixedPauliSampler_probability_continuous
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (P₀ : PauliString Site) (n : ℕ) (P : PauliString Site) :
    Continuous (fun x : Fin n → TwoQubitUnitary =>
      (mixedPauliSampler bond hbond retained (simulationFixedGates n x) P₀ n).probability P) := by
  simp_rw [mixedPauliSampler_output_probability]
  apply continuous_product_average (fun p : (Fin n → TwoQubitUnitary) × (Fin n → TwoQubitUnitary) =>
    randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
      (retainedGateRealization retained (simulationFixedGates n p.1) p.2) P ^ 2)
  have h := (randomLinearEvolution_continuous (pauliCircuitTransfer bond)
    (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) n).comp
    (retainedGateRealization_fixed_continuous n retained)
  exact (continuous_apply P |>.comp h).pow 2

/-- Actual conditional Monte Carlo law given the full Haar circuit input. -/
noncomputable def mixedPauliSamplerKernel
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (P₀ : PauliString Site) (n N : ℕ) :
    Kernel (Fin n → TwoQubitUnitary) (Fin N → PauliString Site) :=
  amplitudeOutputKernel
    (fun x => mixedPauliSampler bond hbond retained (simulationFixedGates n x) P₀ n)
    (fun P => (mixedPauliSampler_probability_continuous bond hbond retained P₀ n P).measurable) N

instance mixedPauliSamplerKernel_isMarkov
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (P₀ : PauliString Site) (n N : ℕ) :
    IsMarkovKernel (mixedPauliSamplerKernel bond hbond retained P₀ n N) := by
  unfold mixedPauliSamplerKernel
  infer_instance

end Fluctuations
