import Fluctuations.SimulationSamplerCovariance

open MeasureTheory
open scoped BigOperators
namespace Fluctuations

set_option linter.unusedSectionVars false

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma pauliInitialVector_normalized (P₀ : PauliString Site) :
    amplitudeNormalized (pauliInitialVector P₀) := by
  classical
  simp [amplitudeNormalized, pauliInitialVector]

/-- The coherent branching sampler for any physical gate sequence and any
retained subset. At retained gates one local vector is updated deterministically;
at averaged gates only one finite input/output branch is sampled. -/
noncomputable def mixedPauliSampler
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site) :
    ℕ → FiniteAmplitudeEnsemble (PauliString Site)
  | 0 => amplitudePoint (pauliInitialVector P₀) (pauliInitialVector_normalized P₀)
  | n + 1 => pauliSamplerStep (bond n).1 (bond n).2 (hbond n) (retained n) (gates n)
      (mixedPauliSampler bond hbond retained gates P₀ n)

noncomputable def mixedCircuitTransfer (bond : ℕ → Site × Site)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) :
    ℕ → TwoQubitUnitary → Matrix (PauliString Site) (PauliString Site) ℝ :=
  fun t => mixedPauliTransfer (bond t).1 (bond t).2 (retained t) (gates t)

lemma mixedCircuitTransfer_continuous (bond : ℕ → Site × Site)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (t : ℕ) :
    Continuous (mixedCircuitTransfer bond retained gates t) :=
  mixedPauliTransfer_continuous _ _ _ _

/-- Induction over the actual finite branching law preserves the complete
second-moment matrix, not merely its diagonal. -/
theorem mixedPauliSampler_covariance
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (n : ℕ) (P Q : PauliString Site) :
    (mixedPauliSampler bond hbond retained gates P₀ n).covariance P Q =
      fullSecondMomentEvolution (globalHaar TwoQubitBasis)
        (mixedCircuitTransfer bond retained gates) (pauliInitialVector P₀) n P Q := by
  induction n generalizing P Q with
  | zero => simp [mixedPauliSampler, fullSecondMomentEvolution]
  | succ n ih =>
    rw [mixedPauliSampler, pauliSamplerStep_covariance]
    simp only [fullSecondMomentEvolution, mixedCircuitTransfer, ih]

/-- Replace precisely the retained coordinates by their prescribed gates. -/
def retainedGateRealization (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary)
    {n : ℕ} (x : Fin n → TwoQubitUnitary) : Fin n → TwoQubitUnitary :=
  fun t => if retained t.val then gates t.val else x t

lemma randomLinearEvolution_mixed (bond : ℕ → Site × Site)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    randomLinearEvolution (mixedCircuitTransfer bond retained gates) (pauliInitialVector P₀) n x =
      randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
        (retainedGateRealization retained gates x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [randomLinearEvolution, mixedCircuitTransfer, mixedPauliTransfer,
      pauliCircuitTransfer, retainedGateRealization, Fin.val_last]
    rw [ih]
    cases retained n <;> rfl

/-- The sampler's full covariance equals the literal independent product-Haar
integral over all unretained physical gates, with retained values fixed. -/
theorem mixedPauliSampler_covariance_integral
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (n : ℕ) (P Q : PauliString Site) :
    (mixedPauliSampler bond hbond retained gates P₀ n).covariance P Q =
      ∫ x : Fin n → TwoQubitUnitary,
        randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
          (retainedGateRealization retained gates x) P *
        randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
          (retainedGateRealization retained gates x) Q
        ∂Measure.pi (fun _ => globalHaar TwoQubitBasis) := by
  simp_rw [← randomLinearEvolution_mixed]
  rw [integral_randomLinearEvolution_mul _ _
    (mixedCircuitTransfer_continuous bond retained gates), mixedPauliSampler_covariance]

/-- Final sampling from the squared stored amplitudes has exactly the desired
conditional Pauli probability distribution. The finite law is normalized. -/
theorem mixedPauliSampler_output_probability
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (n : ℕ) (P : PauliString Site) :
    (mixedPauliSampler bond hbond retained gates P₀ n).probability P =
      ∫ x : Fin n → TwoQubitUnitary,
        randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
          (retainedGateRealization retained gates x) P ^ 2
        ∂Measure.pi (fun _ => globalHaar TwoQubitBasis) := by
  simpa only [FiniteAmplitudeEnsemble.probability, pow_two] using
    mixedPauliSampler_covariance_integral bond hbond retained gates P₀ n P P

/-- The exact conditional probability law is nonnegative and sums to one;
these properties are derived from the finite trajectory sampler. -/
theorem mixedPauliSampler_output_law
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (n : ℕ) :
    (∀ P, 0 ≤ (mixedPauliSampler bond hbond retained gates P₀ n).probability P) ∧
    (∑ P, (mixedPauliSampler bond hbond retained gates P₀ n).probability P) = 1 :=
  ⟨FiniteAmplitudeEnsemble.probability_nonneg _, FiniteAmplitudeEnsemble.probability_total _⟩

/-- The sampler covariance is also tied directly to the literal quantum
matrix-trace observable, with any retained physical gates fixed. -/
theorem mixedPauliSampler_otoc_covariance
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (retained : ℕ → Bool) (gates : ℕ → TwoQubitUnitary) (P₀ : PauliString Site)
    (ρ M : QubitOperator Site) (n : ℕ) :
    (∫ x : Fin n → TwoQubitUnitary,
      globalOTOC ρ (pauliStringMatrix P₀) M 1
        (pauliCircuitUnitary bond hbond n (retainedGateRealization retained gates x))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ∑ P, ∑ Q, pauliOTOCWeight ρ M P Q *
        ((mixedPauliSampler bond hbond retained gates P₀ n).covariance P Q : ℂ) := by
  simp_rw [pauliCircuit_otoc_quadratic, ← randomLinearEvolution_mixed]
  rw [integral_randomLinearEvolution_quadratic _ _
    (mixedCircuitTransfer_continuous bond retained gates)]
  simp_rw [mixedPauliSampler_covariance]

end Fluctuations
