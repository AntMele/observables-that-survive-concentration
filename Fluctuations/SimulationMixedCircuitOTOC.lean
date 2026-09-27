import Fluctuations.SimulationMixedCircuit
import Fluctuations.SimulationTrace

open MeasureTheory
open scoped BigOperators
namespace Fluctuations
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Averaging the final ±1 sampled endpoint sign gives exactly the
infinite-temperature OTOC with the retained physical gates fixed. -/
theorem mixedPauliSampler_endpoint_expectation
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (j : Site) (n : ℕ) :
    (∫ x : Fin n → TwoQubitUnitary,
      globalOTOC (globalMaximallyMixedState (QubitState Site)) (pauliStringMatrix P₀)
        (pauliStringMatrix (pauliSiteZ j)) 1
        (pauliCircuitUnitary bond hbond n (retainedGateRealization retained gates x))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ((∑ P, pauliEndpointSign (P j) *
        (mixedPauliSampler bond hbond retained gates P₀ n).probability P : ℝ) : ℂ) := by
  rw [mixedPauliSampler_otoc_covariance]
  simp_rw [pauliOTOCWeight_maximallyMixed]
  simp [Complex.ofReal_sum, Complex.ofReal_mul, FiniteAmplitudeEnsemble.probability]

omit [Fintype Site] [DecidableEq Site] in
/-- The sampled readout is bounded by one for every possible output string. -/
theorem pauliSampler_endpoint_readout_abs (j : Site) (P : PauliString Site) :
    |pauliEndpointSign (P j)| ≤ 1 := by
  unfold pauliEndpointSign
  split_ifs <;> norm_num

end Fluctuations
