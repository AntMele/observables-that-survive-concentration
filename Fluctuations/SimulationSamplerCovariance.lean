import Fluctuations.SimulationSampler

open MeasureTheory
open scoped BigOperators
namespace Fluctuations

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

section Local
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Haar averaging of one physical gate agrees with the finite 256-branch
sampling rule, including all off-diagonal spectator entries. -/
theorem amplitudeHaarBranch_eq_integral (s₀ : S)
    (ψ : TwoQubitPauliLabel × S → ℝ) (p q : TwoQubitPauliLabel × S) :
    (∑ ab, amplitudeHaarWeight localPauliHaarKernel ψ ab *
      (amplitudeHaarBranch s₀ ψ ab p * amplitudeHaarBranch s₀ ψ ab q)) =
    ∫ U, amplitudeLocalUpdate (twoQubitPauliTransfer U) ψ p *
      amplitudeLocalUpdate (twoQubitPauliTransfer U) ψ q ∂globalHaar TwoQubitBasis := by
  rw [amplitudeHaarBranch_covariance]
  simp_rw [amplitudeLocalUpdate_covariance]
  rw [integral_finset_sum]
  · symm
    trans ∑ a, ∑ b, (if a = b ∧ p.1 = q.1 then localPauliHaarKernel p.1 a else 0) *
      (ψ (a,p.2) * ψ (b,q.2))
    · apply Finset.sum_congr rfl
      intro a _
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_mul_const, twoQubitPauliTransfer_haar_covariance]
      · intro b _
        apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        unfold twoQubitPauliTransfer
        fun_prop
    · by_cases hpq : p.1 = q.1 <;> simp [hpq]
  · intro a _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold twoQubitPauliTransfer
    fun_prop

end Local

section Physical
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

theorem pauliSamplerBranch_eq_integral (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (P Q : PauliString Site) :
    (∑ ab, pauliSamplerWeight i j hij ψ ab *
      (pauliSamplerBranch i j hij ψ ab P * pauliSamplerBranch i j hij ψ ab Q)) =
    ∫ U, Matrix.mulVec (pauliPairTransfer i j U) ψ P *
      Matrix.mulVec (pauliPairTransfer i j U) ψ Q ∂globalHaar TwoQubitBasis := by
  simp_rw [← pauliSamplerFixed_eq_mulVec i j hij]
  exact amplitudeHaarBranch_eq_integral _ _ _ _

noncomputable def pauliSamplerStep (i j : Site) (hij : i ≠ j) (retained : Bool)
    (g : TwoQubitUnitary) (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    FiniteAmplitudeEnsemble (PauliString Site) :=
  if retained then E.map (pauliSamplerFixed i j hij g) (pauliSamplerFixed_normalized i j hij g)
  else E.bind (pauliSamplerWeight i j hij) (pauliSamplerBranch i j hij)
    (pauliSamplerWeight_nonneg i j hij) (pauliSamplerWeight_total i j hij)
    (pauliSamplerBranch_normalized i j hij)

/-- This pointwise kernel fixes precisely the retained gates; unused Haar
coordinates integrate to one. -/
noncomputable def mixedPauliTransfer (i j : Site) (retained : Bool) (g U : TwoQubitUnitary) :
    Matrix (PauliString Site) (PauliString Site) ℝ :=
  if retained then pauliPairTransfer i j g else pauliPairTransfer i j U

lemma mixedPauliTransfer_continuous (i j : Site) (retained : Bool) (g : TwoQubitUnitary) :
    Continuous (mixedPauliTransfer i j retained g) := by
  cases retained
  · exact pauliPairTransfer_continuous i j
  · exact continuous_const

theorem pauliSamplerStep_covariance_integral (i j : Site) (hij : i ≠ j) (retained : Bool)
    (g : TwoQubitUnitary) (E : FiniteAmplitudeEnsemble (PauliString Site))
    (P Q : PauliString Site) :
    (pauliSamplerStep i j hij retained g E).covariance P Q =
      ∑ x, E.weight x * (∫ U,
        Matrix.mulVec (mixedPauliTransfer i j retained g U) (E.vector x) P *
        Matrix.mulVec (mixedPauliTransfer i j retained g U) (E.vector x) Q
        ∂globalHaar TwoQubitBasis) := by
  cases retained
  · simp only [pauliSamplerStep, Bool.false_eq_true, ↓reduceIte,
      FiniteAmplitudeEnsemble.bind_covariance, mixedPauliTransfer]
    simp_rw [pauliSamplerBranch_eq_integral]
  · change (∑ x, E.weight x * (pauliSamplerFixed i j hij g (E.vector x) P *
        pauliSamplerFixed i j hij g (E.vector x) Q)) = _
    simp only [mixedPauliTransfer, ↓reduceIte, integral_const,
      measureReal_univ_eq_one, smul_eq_mul, one_mul]
    simp_rw [pauliSamplerFixed_eq_mulVec]

end Physical

/-- Full covariance of a mixture after a common random real matrix update. -/
theorem sampler_integral_matrix_covariance
    {G Q : Type*} [Fintype Q]
    [TopologicalSpace G] [CompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [IsProbabilityMeasure ν]
    (K : G → Matrix Q Q ℝ) (hK : Continuous K) (ψ : Q → ℝ) (i j : Q) :
    (∫ U, (K U).mulVec ψ i * (K U).mulVec ψ j ∂ν) =
      ∑ a, ∑ b, gateSecondMoment ν K (i,j) (a,b) * (ψ a * ψ b) := by
  have he (U : G) : (K U).mulVec ψ i * (K U).mulVec ψ j =
      ∑ a, ∑ b, (K U i a * K U j b) * (ψ a * ψ b) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro b _
      exact integral_mul_const _ _
    · intro b _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
  · intro a _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop

section Physical
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

theorem pauliSamplerStep_covariance (i j : Site) (hij : i ≠ j) (retained : Bool)
    (g : TwoQubitUnitary) (E : FiniteAmplitudeEnsemble (PauliString Site))
    (P Q : PauliString Site) :
    (pauliSamplerStep i j hij retained g E).covariance P Q =
      ∑ R, ∑ S, gateSecondMoment (globalHaar TwoQubitBasis)
        (mixedPauliTransfer i j retained g) (P,Q) (R,S) * E.covariance R S := by
  rw [pauliSamplerStep_covariance_integral]
  simp_rw [sampler_integral_matrix_covariance _ _
    (mixedPauliTransfer_continuous i j retained g), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp only [FiniteAmplitudeEnsemble.covariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Physical
end Fluctuations
