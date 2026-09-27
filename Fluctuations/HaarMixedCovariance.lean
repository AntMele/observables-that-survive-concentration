import Fluctuations.HaarConjugationCovariance

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

set_option maxHeartbeats 800000

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The actual rank-one covariance integrand of the conjugated matrix. -/
noncomputable def globalHaarCrossCovarianceIntegrand (B C X : Matrix N N ℂ) :
    C(GlobalUnitary N, Matrix N N ℂ) where
  toFun U := Matrix.trace (globalHaarConjugate B U * X) • globalHaarConjugate C U
  continuous_toFun := by fun_prop

lemma globalHaarCrossCovarianceIntegrand_integrable (B C X : Matrix N N ℂ) :
    Integrable (globalHaarCrossCovarianceIntegrand B C X) (globalHaar N) :=
  (globalHaarCrossCovarianceIntegrand B C X).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def globalHaarCrossCovariance (B C X : Matrix N N ℂ) : Matrix N N ℂ :=
  ∫ U, globalHaarCrossCovarianceIntegrand B C X U ∂globalHaar N

lemma globalHaarCrossCovariance_add (B C X Y : Matrix N N ℂ) :
    globalHaarCrossCovariance B C (X + Y) = globalHaarCrossCovariance B C X + globalHaarCrossCovariance B C Y := by
  unfold globalHaarCrossCovariance
  simp only [globalHaarCrossCovarianceIntegrand, ContinuousMap.coe_mk, Matrix.mul_add,
    Matrix.trace_add, add_smul]
  exact integral_add (globalHaarCrossCovarianceIntegrand_integrable B C X)
    (globalHaarCrossCovarianceIntegrand_integrable B C Y)

lemma globalHaarCrossCovariance_smul (B C X : Matrix N N ℂ) (c : ℂ) :
    globalHaarCrossCovariance B C (c • X) = c • globalHaarCrossCovariance B C X := by
  unfold globalHaarCrossCovariance
  simp only [globalHaarCrossCovarianceIntegrand, ContinuousMap.coe_mk, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_smul]
  exact integral_smul c _

noncomputable def globalHaarCrossCovarianceLinear (B C : Matrix N N ℂ) :
    Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ where
  toFun := globalHaarCrossCovariance B C
  map_add' := globalHaarCrossCovariance_add B C
  map_smul' := fun c X => globalHaarCrossCovariance_smul B C X c

lemma globalHaarCrossCovariance_one (B C : Matrix N N ℂ) (hB : Matrix.trace B = 0) :
    globalHaarCrossCovariance B C 1 = 0 := by
  unfold globalHaarCrossCovariance
  have hp (U : GlobalUnitary N) : globalHaarCrossCovarianceIntegrand B C 1 U = 0 := by
    change Matrix.trace (globalHaarConjugate B U * 1) • globalHaarConjugate C U = 0
    rw [Matrix.mul_one, globalHaarConjugate_trace, hB, zero_smul]
  simp_rw [hp]
  simp

lemma globalHaarCrossCovarianceIntegrand_conjugate (B C X : Matrix N N ℂ) (U S : GlobalUnitary N) :
    globalHaarCrossCovarianceIntegrand B C (S.val.conjTranspose * X * S.val) (U * S) =
      S.val.conjTranspose * globalHaarCrossCovarianceIntegrand B C X U * S.val := by
  have hSS : S.val * S.val.conjTranspose = 1 := S.prop.2
  have ht : Matrix.trace (globalHaarConjugate B (U * S) *
      (S.val.conjTranspose * X * S.val)) = Matrix.trace (globalHaarConjugate B U * X) := by
    rw [globalHaarConjugate_mul_right]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S.val S.val.conjTranspose,
      hSS, Matrix.one_mul]
    simpa only [globalHaarConjugate, ContinuousMap.coe_mk, Matrix.mul_assoc] using
      globalHaarConjugate_trace (globalHaarConjugate B U * X) S
  change Matrix.trace (globalHaarConjugate B (U * S) *
    (S.val.conjTranspose * X * S.val)) • globalHaarConjugate C (U * S) =
    S.val.conjTranspose * (Matrix.trace (globalHaarConjugate B U * X) •
      globalHaarConjugate C U) * S.val
  rw [ht, globalHaarConjugate_mul_right, Matrix.mul_smul, Matrix.smul_mul]

theorem globalHaarCrossCovariance_equivariant (B C X : Matrix N N ℂ) (S : GlobalUnitary N) :
    globalHaarCrossCovariance B C (S.val.conjTranspose * X * S.val) =
      S.val.conjTranspose * globalHaarCrossCovariance B C X * S.val := by
  calc
    _ = ∫ U, globalHaarCrossCovarianceIntegrand B C (S.val.conjTranspose * X * S.val) (U * S)
        ∂globalHaar N := (integral_mul_right_eq_self _ S).symm
    _ = ∫ U, S.val.conjTranspose * globalHaarCrossCovarianceIntegrand B C X U * S.val
        ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => globalHaarCrossCovarianceIntegrand_conjugate B C X U S
    _ = _ := (matrixSandwichCLM S.val.conjTranspose S.val).integral_comp_comm
      (globalHaarCrossCovarianceIntegrand_integrable B C X)

lemma globalHaarCrossCovariance_single_entry (B C : Matrix N N ℂ) (i j : N) :
    globalHaarCrossCovariance B C (Matrix.single i j 1) i j =
      ∫ U, globalHaarConjugate B U j i * globalHaarConjugate C U i j ∂globalHaar N := by
  have h := (matrixEntryCLM i j).integral_comp_comm
    (globalHaarCrossCovarianceIntegrand_integrable B C (Matrix.single i j 1))
  change (∫ U, globalHaarCrossCovarianceIntegrand B C (Matrix.single i j 1) U i j ∂globalHaar N) =
    globalHaarCrossCovariance B C (Matrix.single i j 1) i j at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with U
  simp [globalHaarCrossCovarianceIntegrand, Matrix.trace_mul_single]

lemma globalHaarConjugate_mul (B C : Matrix N N ℂ) (U : GlobalUnitary N) :
    globalHaarConjugate B U * globalHaarConjugate C U = globalHaarConjugate (B * C) U := by
  have hU : U.val * U.val.conjTranspose = 1 := U.prop.2
  simp only [globalHaarConjugate, ContinuousMap.coe_mk, Matrix.mul_assoc,
    ← Matrix.mul_assoc U.val U.val.conjTranspose, hU, Matrix.one_mul]

lemma globalHaarCrossCovariance_superTrace (B C : Matrix N N ℂ) :
    matrixSuperTrace (globalHaarCrossCovarianceLinear B C) = Matrix.trace (B * C) := by
  have hi (i j : N) : Integrable
      (fun U : GlobalUnitary N => globalHaarConjugate B U j i * globalHaarConjugate C U i j)
      (globalHaar N) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _
  unfold matrixSuperTrace
  change (∑ i : N, ∑ j : N, globalHaarCrossCovariance B C (Matrix.single i j 1) i j) = _
  simp_rw [globalHaarCrossCovariance_single_entry]
  simp_rw [← integral_finset_sum _ (fun j _ => hi _ j)]
  rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  have hp (U : GlobalUnitary N) :
      (∑ i : N, ∑ j : N, globalHaarConjugate B U j i * globalHaarConjugate C U i j) =
        Matrix.trace (B * C) := by
    calc
      _ = Matrix.trace (globalHaarConjugate C U * globalHaarConjugate B U) := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, mul_comm]
      _ = _ := by rw [globalHaarConjugate_mul, globalHaarConjugate_trace, Matrix.trace_mul_comm]
  simp_rw [hp]
  simp

/-- The full mixed covariance follows from actual unitary invariance, with
both input matrices arbitrary. This is stronger than a squared-weight rule. -/
theorem globalHaarCrossCovariance_traceless [Nontrivial N]
    (B C X : Matrix N N ℂ) (hB : Matrix.trace B = 0) (hX : Matrix.trace X = 0) :
    globalHaarCrossCovariance B C X =
      (Matrix.trace (B * C) / ((Fintype.card N : ℂ) ^ 2 - 1)) • X := by
  obtain ⟨a, b, hab⟩ := unitaryConjugationEquivariant_classification
    (globalHaarCrossCovarianceLinear B C) (globalHaarCrossCovariance_equivariant B C)
  have hmaps : globalHaarCrossCovarianceLinear B C = scalarTraceLinear a b := by
    ext X : 1
    exact hab X
  have hs := globalHaarCrossCovariance_superTrace B C
  rw [hmaps, matrixSuperTrace_scalarTraceLinear] at hs
  have ho := hab (1 : Matrix N N ℂ)
  change globalHaarCrossCovariance B C 1 = _ at ho
  rw [globalHaarCrossCovariance_one B C hB] at ho
  let i : N := Classical.choice inferInstance
  have ho' := congrArg (fun A : Matrix N N ℂ => A i i) ho
  simp only [Matrix.zero_apply, Matrix.one_apply_eq, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one, Matrix.trace_one] at ho'
  have hD : (2 : ℝ) ≤ Fintype.card N := by exact_mod_cast Fintype.one_lt_card
  have hden : (Fintype.card N : ℂ) ^ 2 - 1 ≠ 0 := by
    intro hzero
    have hr := congrArg Complex.re hzero
    simp [pow_two, Complex.mul_re] at hr
    nlinarith
  have ha : a = Matrix.trace (B * C) / ((Fintype.card N : ℂ) ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    linear_combination hs + ho'
  have hx := hab X
  change globalHaarCrossCovariance B C X = _ at hx
  simpa [hX, ha] using hx

theorem globalHaarConjugate_mixed_trace_product [Nontrivial N]
    (B C Q R : Matrix N N ℂ) (hB : Matrix.trace B = 0) (hQ : Matrix.trace Q = 0) :
    (∫ U, Matrix.trace (Q * globalHaarConjugate B U) *
      Matrix.trace (R * globalHaarConjugate C U) ∂globalHaar N) =
      Matrix.trace (B * C) / ((Fintype.card N : ℂ) ^ 2 - 1) * Matrix.trace (Q * R) := by
  have h := (stateTraceCLM R).integral_comp_comm
    (globalHaarCrossCovarianceIntegrand_integrable B C Q)
  change (∫ U, Matrix.trace (R * globalHaarCrossCovarianceIntegrand B C Q U) ∂globalHaar N) =
    Matrix.trace (R * globalHaarCrossCovariance B C Q) at h
  have hp (U : GlobalUnitary N) :
      Matrix.trace (R * globalHaarCrossCovarianceIntegrand B C Q U) =
        Matrix.trace (Q * globalHaarConjugate B U) *
          Matrix.trace (R * globalHaarConjugate C U) := by
    change Matrix.trace (R * (Matrix.trace (globalHaarConjugate B U * Q) •
      globalHaarConjugate C U)) = _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm (globalHaarConjugate B U) Q]
  simp_rw [hp] at h
  rw [h, globalHaarCrossCovariance_traceless B C Q hB hQ, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm R Q]

/-- Complete local Haar second moment: orthogonal input or output matrices
give zero, which proves rather than assumes cancellation of interference. -/
theorem globalHaarTraceCoefficient_mixed_product [Nontrivial N]
    (B C Q R : Matrix N N ℂ) (hB : Matrix.trace B = 0) (hQ : Matrix.trace Q = 0) :
    (∫ U, globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient C R U
      ∂globalHaar N) =
      (Fintype.card N : ℂ)⁻¹ ^ 2 *
        (Matrix.trace (B * C) / ((Fintype.card N : ℂ) ^ 2 - 1)) * Matrix.trace (Q * R) := by
  have hp (U : GlobalUnitary N) :
      globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient C R U =
        (Fintype.card N : ℂ)⁻¹ ^ 2 * (Matrix.trace (Q * globalHaarConjugate B U) *
          Matrix.trace (R * globalHaarConjugate C U)) := by
    dsimp only [globalHaarTraceCoefficient, ContinuousMap.coe_mk]
    ring
  simp_rw [hp]
  rw [integral_const_mul, globalHaarConjugate_mixed_trace_product B C Q R hB hQ]
  ring

end Fluctuations
