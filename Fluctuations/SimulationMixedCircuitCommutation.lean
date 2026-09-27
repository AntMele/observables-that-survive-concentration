import Fluctuations.SimulationGeometrySampler
import Fluctuations.SimulationSamplerReorder

open MeasureTheory
open scoped BigOperators
namespace Fluctuations
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The full local four-index covariance kernel of a fixed or Haar gate. -/
def samplerLocalCovarianceKernel (retained : Bool) (g : TwoQubitUnitary)
    (out inp : TwoQubitPauliLabel × TwoQubitPauliLabel) : ℝ :=
  ∫ U, twoQubitPauliTransfer (if retained then g else U) out.1 inp.1 *
    twoQubitPauliTransfer (if retained then g else U) out.2 inp.2 ∂globalHaar TwoQubitBasis

/-- Local action on the full covariance, without any diagonal assumption. -/
def pauliCovarianceUpdate (i j : Site)
    (L : Matrix (TwoQubitPauliLabel × TwoQubitPauliLabel)
      (TwoQubitPauliLabel × TwoQubitPauliLabel) ℝ)
    (C : PauliString Site → PauliString Site → ℝ) (P Q : PauliString Site) : ℝ :=
  ∑ a, L ((P i,P j),(Q i,Q j)) a *
    C (pauliPairReplace i j P a.1) (pauliPairReplace i j Q a.2)

lemma pauliSamplerFixed_product (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (P Q : PauliString Site) :
    pauliSamplerFixed i j hij U ψ P * pauliSamplerFixed i j hij U ψ Q =
      ∑ a : TwoQubitPauliLabel × TwoQubitPauliLabel,
        (twoQubitPauliTransfer U (P i,P j) a.1 * twoQubitPauliTransfer U (Q i,Q j) a.2) *
        (ψ (pauliPairReplace i j P a.1) * ψ (pauliPairReplace i j Q a.2)) := by
  rw [pauliSamplerFixed_eq_pairEvolution]
  simp only [pauliPairEvolution, Finset.sum_mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma sampler_mixed_local_product (i j : Site) (hij : i ≠ j) (retained : Bool)
    (g : TwoQubitUnitary) (ψ : PauliString Site → ℝ) (P Q : PauliString Site) :
    (∫ U, Matrix.mulVec (mixedPauliTransfer i j retained g U) ψ P *
      Matrix.mulVec (mixedPauliTransfer i j retained g U) ψ Q ∂globalHaar TwoQubitBasis) =
      pauliCovarianceUpdate i j (samplerLocalCovarianceKernel retained g)
        (fun R S => ψ R * ψ S) P Q := by
  have he (U : TwoQubitUnitary) : mixedPauliTransfer i j retained g U =
      pauliPairTransfer i j (if retained then g else U) := by
    cases retained <;> rfl
  simp_rw [he, ← pauliSamplerFixed_eq_mulVec i j hij, pauliSamplerFixed_product]
  unfold pauliCovarianceUpdate
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a _
    exact integral_mul_const _ _
  · intro a _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    cases retained with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold twoQubitPauliTransfer
      fun_prop
    | true =>
      exact (continuous_const : Continuous (fun _ : TwoQubitUnitary =>
        (twoQubitPauliTransfer g (P i,P j) a.1 * twoQubitPauliTransfer g (Q i,Q j) a.2) *
        (ψ (pauliPairReplace i j P a.1) * ψ (pauliPairReplace i j Q a.2))))

/-- Exact local covariance semantics of the implemented ensemble step. -/
theorem pauliSamplerStep_covariance_local (i j : Site) (hij : i ≠ j) (retained : Bool)
    (g : TwoQubitUnitary) (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (pauliSamplerStep i j hij retained g E).covariance =
      pauliCovarianceUpdate i j (samplerLocalCovarianceKernel retained g) E.covariance := by
  funext P Q
  rw [pauliSamplerStep_covariance_integral]
  simp_rw [sampler_mixed_local_product i j hij]
  unfold pauliCovarianceUpdate
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [FiniteAmplitudeEnsemble.covariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Two disjoint local full-covariance operators commute for arbitrary kernels.
This is a finite algebraic statement, retaining every spectator cross term. -/
theorem pauliCovarianceUpdate_commute (i j k l : Site)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (K L : Matrix (TwoQubitPauliLabel × TwoQubitPauliLabel)
      (TwoQubitPauliLabel × TwoQubitPauliLabel) ℝ)
    (C : PauliString Site → PauliString Site → ℝ) :
    pauliCovarianceUpdate i j K (pauliCovarianceUpdate k l L C) =
      pauliCovarianceUpdate k l L (pauliCovarianceUpdate i j K C) := by
  funext P Q
  simp only [pauliCovarianceUpdate, Finset.mul_sum,
    pauliPairReplace_apply_away i j k hik.symm hjk.symm,
    pauliPairReplace_apply_away i j l hil.symm hjl.symm,
    pauliPairReplace_apply_away k l i hik hil,
    pauliPairReplace_apply_away k l j hjk hjl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [pauliPairReplace_commute i j k l hik hil hjk hjl,
    pauliPairReplace_commute i j k l hik hil hjk hjl]
  ring

/-- Any fixed/Haar mixture of two disjoint gate calls commutes in full
covariance. Their internal branch-index types need not be identified. -/
theorem pauliSamplerStep_covariance_commute (i j k l : Site)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (r s : Bool) (U V : TwoQubitUnitary) (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (pauliSamplerStep i j hij r U (pauliSamplerStep k l hkl s V E)).covariance =
      (pauliSamplerStep k l hkl s V (pauliSamplerStep i j hij r U E)).covariance := by
  simp_rw [pauliSamplerStep_covariance_local]
  exact pauliCovarianceUpdate_commute i j k l hik hil hjk hjl _ _ E.covariance

/-- A heterogeneous sequence of actual sampler calls. -/
def simulationMixedListEnsemble (retained : Site × Site → Bool)
    (gates : Site × Site → TwoQubitUnitary) (word : List (Site × Site))
    (E : FiniteAmplitudeEnsemble (PauliString Site)) :=
  word.foldl (fun E p => simulationPairEnsembleStep (retained p) (gates p) p E) E

def simulationPairCovarianceStep (retained : Bool) (U : TwoQubitUnitary)
    (p : Site × Site) (C : PauliString Site → PauliString Site → ℝ) :=
  if p.1 ≠ p.2 then pauliCovarianceUpdate p.1 p.2 (samplerLocalCovarianceKernel retained U) C else C

lemma simulationPairEnsembleStep_covariance (r : Bool) (U : TwoQubitUnitary)
    (p : Site × Site) (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (simulationPairEnsembleStep r U p E).covariance =
      simulationPairCovarianceStep r U p E.covariance := by
  unfold simulationPairEnsembleStep simulationPairCovarianceStep
  split_ifs
  · exact pauliSamplerStep_covariance_local _ _ _ _ _ _
  · rfl

theorem simulationMixedListEnsemble_covariance (retained : Site × Site → Bool)
    (gates : Site × Site → TwoQubitUnitary) (word : List (Site × Site))
    (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (simulationMixedListEnsemble retained gates word E).covariance =
      word.foldl (fun C p => simulationPairCovarianceStep (retained p) (gates p) p C) E.covariance := by
  induction word generalizing E with
  | nil => rfl
  | cons p word ih =>
    change (simulationMixedListEnsemble retained gates word
      (simulationPairEnsembleStep (retained p) (gates p) p E)).covariance = _
    rw [ih,simulationPairEnsembleStep_covariance]
    rfl

/-- The actual ensemble laws of any two matching-layer orders have identical
full covariance, including heterogeneous fixed and averaged gates. -/
theorem simulationMixedListEnsemble_covariance_perm
    (retained : Site × Site → Bool) (gates : Site × Site → TwoQubitUnitary)
    (word other : List (Site × Site)) (hp : word.Perm other)
    (hm : ∀ p ∈ word, ∀ q ∈ word, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (simulationMixedListEnsemble retained gates word E).covariance =
      (simulationMixedListEnsemble retained gates other E).covariance := by
  simp_rw [simulationMixedListEnsemble_covariance]
  apply hp.foldl_eq'
  intro p hp q hq C
  by_cases hpq : p=q
  · subst q
    rfl
  · obtain ⟨h1,h2,h3,h4⟩ := hm p hp q hq hpq
    unfold simulationPairCovarianceStep
    split_ifs <;> try rfl
    exact (pauliCovarianceUpdate_commute p.1 p.2 q.1 q.2 h1 h2 h3 h4 _ _ C).symm

lemma simulationMixedListEnsemble_append
    (retained : Site × Site → Bool) (gates : Site × Site → TwoQubitUnitary)
    (xs ys : List (Site × Site)) (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    simulationMixedListEnsemble retained gates (xs++ys) E =
      simulationMixedListEnsemble retained gates ys (simulationMixedListEnsemble retained gates xs E) :=
  List.foldl_append

lemma simulationMixedListEnsemble_constant
    (retained : Site × Site → Bool) (gates : Site × Site → TwoQubitUnitary)
    (word : List (Site × Site)) (r : Bool) (hr : ∀ p ∈ word, retained p = r)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    simulationMixedListEnsemble retained gates word E = simulationListEnsemble r gates word E := by
  induction word generalizing E with
  | nil => rfl
  | cons p word ih =>
    change simulationMixedListEnsemble retained gates word
      (simulationPairEnsembleStep (retained p) (gates p) p E) =
      simulationListEnsemble r gates word (simulationPairEnsembleStep r (gates p) p E)
    rw [hr p (by simp),ih (fun q hq => hr q (by simp [hq]))]

/-- A chronological mixed layer and the exact outside-first/retained-second
list sampler have the same output covariance. -/
theorem simulationMixedListEnsemble_outside_covariance
    (retained : Site × Site → Bool) (gates : Site × Site → TwoQubitUnitary)
    (word outside inside : List (Site × Site)) (hp : word.Perm (outside++inside))
    (ho : ∀ p ∈ outside, retained p = false) (hi : ∀ p ∈ inside, retained p = true)
    (hm : ∀ p ∈ word, ∀ q ∈ word, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) :
    (simulationMixedListEnsemble retained gates word E).covariance =
      (simulationListEnsemble true gates inside (simulationListEnsemble false gates outside E)).covariance := by
  rw [simulationMixedListEnsemble_covariance_perm retained gates word _ hp hm,
    simulationMixedListEnsemble_append, simulationMixedListEnsemble_constant retained gates outside false ho,
    simulationMixedListEnsemble_constant retained gates inside true hi]

end
end Fluctuations
