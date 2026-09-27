import Fluctuations.GlobalHaarFirstOrderValue

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

set_option maxHeartbeats 800000

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The actual rank-one covariance integrand of the conjugated matrix. -/
noncomputable def globalHaarCovarianceIntegrand (B X : Matrix N N ℂ) :
    C(GlobalUnitary N, Matrix N N ℂ) where
  toFun U := Matrix.trace (globalHaarConjugate B U * X) • globalHaarConjugate B U
  continuous_toFun := by fun_prop

lemma globalHaarCovarianceIntegrand_integrable (B X : Matrix N N ℂ) :
    Integrable (globalHaarCovarianceIntegrand B X) (globalHaar N) :=
  (globalHaarCovarianceIntegrand B X).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def globalHaarCovariance (B X : Matrix N N ℂ) : Matrix N N ℂ :=
  ∫ U, globalHaarCovarianceIntegrand B X U ∂globalHaar N

lemma globalHaarCovariance_add (B X Y : Matrix N N ℂ) :
    globalHaarCovariance B (X + Y) = globalHaarCovariance B X + globalHaarCovariance B Y := by
  unfold globalHaarCovariance
  simp only [globalHaarCovarianceIntegrand, ContinuousMap.coe_mk, Matrix.mul_add,
    Matrix.trace_add, add_smul]
  exact integral_add (globalHaarCovarianceIntegrand_integrable B X)
    (globalHaarCovarianceIntegrand_integrable B Y)

lemma globalHaarCovariance_smul (B X : Matrix N N ℂ) (c : ℂ) :
    globalHaarCovariance B (c • X) = c • globalHaarCovariance B X := by
  unfold globalHaarCovariance
  simp only [globalHaarCovarianceIntegrand, ContinuousMap.coe_mk, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, mul_smul]
  exact integral_smul c _

noncomputable def globalHaarCovarianceLinear (B : Matrix N N ℂ) :
    Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ where
  toFun := globalHaarCovariance B
  map_add' := globalHaarCovariance_add B
  map_smul' := fun c X => globalHaarCovariance_smul B X c

lemma globalHaarCovariance_one (B : Matrix N N ℂ) (hB : Matrix.trace B = 0) :
    globalHaarCovariance B 1 = 0 := by
  unfold globalHaarCovariance
  have hp (U : GlobalUnitary N) : globalHaarCovarianceIntegrand B 1 U = 0 := by
    change Matrix.trace (globalHaarConjugate B U * 1) • globalHaarConjugate B U = 0
    rw [Matrix.mul_one, globalHaarConjugate_trace, hB, zero_smul]
  simp_rw [hp]
  simp

lemma globalHaarCovarianceIntegrand_conjugate (B X : Matrix N N ℂ) (U S : GlobalUnitary N) :
    globalHaarCovarianceIntegrand B (S.val.conjTranspose * X * S.val) (U * S) =
      S.val.conjTranspose * globalHaarCovarianceIntegrand B X U * S.val := by
  have hSS : S.val * S.val.conjTranspose = 1 := S.prop.2
  have ht : Matrix.trace (globalHaarConjugate B (U * S) *
      (S.val.conjTranspose * X * S.val)) = Matrix.trace (globalHaarConjugate B U * X) := by
    rw [globalHaarConjugate_mul_right]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S.val S.val.conjTranspose,
      hSS, Matrix.one_mul]
    simpa only [globalHaarConjugate, ContinuousMap.coe_mk, Matrix.mul_assoc] using
      globalHaarConjugate_trace (globalHaarConjugate B U * X) S
  change Matrix.trace (globalHaarConjugate B (U * S) *
    (S.val.conjTranspose * X * S.val)) • globalHaarConjugate B (U * S) =
    S.val.conjTranspose * (Matrix.trace (globalHaarConjugate B U * X) •
      globalHaarConjugate B U) * S.val
  rw [ht, globalHaarConjugate_mul_right, Matrix.mul_smul, Matrix.smul_mul]

theorem globalHaarCovariance_equivariant (B X : Matrix N N ℂ) (S : GlobalUnitary N) :
    globalHaarCovariance B (S.val.conjTranspose * X * S.val) =
      S.val.conjTranspose * globalHaarCovariance B X * S.val := by
  calc
    _ = ∫ U, globalHaarCovarianceIntegrand B (S.val.conjTranspose * X * S.val) (U * S)
        ∂globalHaar N := (integral_mul_right_eq_self _ S).symm
    _ = ∫ U, S.val.conjTranspose * globalHaarCovarianceIntegrand B X U * S.val
        ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => globalHaarCovarianceIntegrand_conjugate B X U S
    _ = _ := (matrixSandwichCLM S.val.conjTranspose S.val).integral_comp_comm
      (globalHaarCovarianceIntegrand_integrable B X)

lemma globalHaarCovariance_single_entry (B : Matrix N N ℂ) (i j : N) :
    globalHaarCovariance B (Matrix.single i j 1) i j =
      ∫ U, globalHaarConjugate B U j i * globalHaarConjugate B U i j ∂globalHaar N := by
  have h := (matrixEntryCLM i j).integral_comp_comm
    (globalHaarCovarianceIntegrand_integrable B (Matrix.single i j 1))
  change (∫ U, globalHaarCovarianceIntegrand B (Matrix.single i j 1) U i j ∂globalHaar N) =
    globalHaarCovariance B (Matrix.single i j 1) i j at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with U
  simp [globalHaarCovarianceIntegrand, Matrix.trace_mul_single]

lemma globalHaarCovariance_superTrace (B : Matrix N N ℂ) (hB : B * B = 1) :
    matrixSuperTrace (globalHaarCovarianceLinear B) = Fintype.card N := by
  have hi (i j : N) : Integrable
      (fun U : GlobalUnitary N => globalHaarConjugate B U j i * globalHaarConjugate B U i j)
      (globalHaar N) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _
  unfold matrixSuperTrace
  change (∑ i : N, ∑ j : N, globalHaarCovariance B (Matrix.single i j 1) i j) = _
  simp_rw [globalHaarCovariance_single_entry]
  simp_rw [← integral_finset_sum _ (fun j _ => hi _ j)]
  rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  have hp (U : GlobalUnitary N) :
      (∑ i : N, ∑ j : N, globalHaarConjugate B U j i * globalHaarConjugate B U i j) =
        (Fintype.card N : ℂ) := by
    have ht := congrArg Matrix.trace (globalHaarConjugate_involution B hB U)
    simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_comm] using ht
  simp_rw [hp]
  simp

/-- Exact isotropic Haar covariance on the traceless matrix space. -/
theorem globalHaarCovariance_traceless [Nontrivial N]
    (B X : Matrix N N ℂ) (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hX : Matrix.trace X = 0) :
    globalHaarCovariance B X =
      ((Fintype.card N : ℂ) / ((Fintype.card N : ℂ) ^ 2 - 1)) • X := by
  obtain ⟨a, b, hab⟩ := unitaryConjugationEquivariant_classification
    (globalHaarCovarianceLinear B) (globalHaarCovariance_equivariant B)
  have hmaps : globalHaarCovarianceLinear B = scalarTraceLinear a b := by
    ext X : 1
    exact hab X
  have hs := globalHaarCovariance_superTrace B hBB
  rw [hmaps, matrixSuperTrace_scalarTraceLinear] at hs
  have ho := hab (1 : Matrix N N ℂ)
  change globalHaarCovariance B 1 = _ at ho
  rw [globalHaarCovariance_one B hB] at ho
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
  have ha : a = (Fintype.card N : ℂ) / ((Fintype.card N : ℂ) ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    linear_combination hs + ho'
  have hx := hab X
  change globalHaarCovariance B X = _ at hx
  simpa [hX, ha] using hx

/-- The full second-moment pairing, including the vanishing off-diagonal
Pauli covariances needed for the Markov evolution of squared coefficients. -/
theorem globalHaarConjugate_trace_product [Nontrivial N]
    (B Q R : Matrix N N ℂ) (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hR : Matrix.trace R = 0) :
    (∫ U, Matrix.trace (Q * globalHaarConjugate B U) *
      Matrix.trace (R * globalHaarConjugate B U) ∂globalHaar N) =
      ((Fintype.card N : ℂ) / ((Fintype.card N : ℂ) ^ 2 - 1)) * Matrix.trace (Q * R) := by
  have h := (stateTraceCLM Q).integral_comp_comm
    (globalHaarCovarianceIntegrand_integrable B R)
  change (∫ U, Matrix.trace (Q * globalHaarCovarianceIntegrand B R U) ∂globalHaar N) =
    Matrix.trace (Q * globalHaarCovariance B R) at h
  have hp (U : GlobalUnitary N) :
      Matrix.trace (Q * globalHaarCovarianceIntegrand B R U) =
        Matrix.trace (Q * globalHaarConjugate B U) *
          Matrix.trace (R * globalHaarConjugate B U) := by
    change Matrix.trace (Q * (Matrix.trace (globalHaarConjugate B U * R) •
      globalHaarConjugate B U)) = _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm (globalHaarConjugate B U) R]
    ring
  simp_rw [hp] at h
  rw [h, globalHaarCovariance_traceless B R hBB hB hR, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]

/-- The normalized trace coefficient of an actual unitary conjugate. -/
noncomputable def globalHaarTraceCoefficient (B Q : Matrix N N ℂ) :
    C(GlobalUnitary N, ℂ) where
  toFun U := (Fintype.card N : ℂ)⁻¹ * Matrix.trace (Q * globalHaarConjugate B U)
  continuous_toFun := by fun_prop

omit [DecidableEq N] in
lemma trace_mul_hermitian_star (Q R : Matrix N N ℂ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    star (Matrix.trace (Q * R)) = Matrix.trace (Q * R) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hQ.eq, hR.eq,
    Matrix.trace_mul_comm]

lemma globalHaarTraceCoefficient_star (B Q : Matrix N N ℂ)
    (hB : B.IsHermitian) (hQ : Q.IsHermitian) (U : GlobalUnitary N) :
    star (globalHaarTraceCoefficient B Q U) = globalHaarTraceCoefficient B Q U := by
  have hC : (globalHaarConjugate B U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul U.val hB
  change star ((Fintype.card N : ℂ)⁻¹ * Matrix.trace (Q * globalHaarConjugate B U)) = _
  rw [star_mul', star_inv₀, star_natCast, trace_mul_hermitian_star Q _ hQ hC]
  rfl

theorem globalHaarTraceCoefficient_product [Nontrivial N]
    (B Q R : Matrix N N ℂ) (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hR : Matrix.trace R = 0) :
    (∫ U, globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient B R U
      ∂globalHaar N) =
      (Fintype.card N : ℂ)⁻¹ * ((Fintype.card N : ℂ) ^ 2 - 1)⁻¹ *
        Matrix.trace (Q * R) := by
  have hp (U : GlobalUnitary N) :
      globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient B R U =
        (Fintype.card N : ℂ)⁻¹ ^ 2 * (Matrix.trace (Q * globalHaarConjugate B U) *
          Matrix.trace (R * globalHaarConjugate B U)) := by
    dsimp only [globalHaarTraceCoefficient, ContinuousMap.coe_mk]
    ring
  simp_rw [hp]
  rw [integral_const_mul, globalHaarConjugate_trace_product B Q R hBB hB hR]
  have hD : (Fintype.card N : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [div_eq_mul_inv]
  field_simp

/-- Haar conjugation spreads squared coefficients equally over normalized
traceless Hermitian involution directions. In dimension four this is 1/15. -/
theorem globalHaarTraceCoefficient_norm_sq [Nontrivial N]
    (B Q : Matrix N N ℂ) (hBH : B.IsHermitian) (hBB : B * B = 1)
    (hB : Matrix.trace B = 0) (hQH : Q.IsHermitian) (hQQ : Q * Q = 1)
    (hQ : Matrix.trace Q = 0) :
    (∫ U, ‖globalHaarTraceCoefficient B Q U‖ ^ 2 ∂globalHaar N) =
      1 / ((Fintype.card N : ℝ) ^ 2 - 1) := by
  have hp (U : GlobalUnitary N) :
      ((‖globalHaarTraceCoefficient B Q U‖ ^ 2 : ℝ) : ℂ) =
        globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient B Q U := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    rw [← Complex.star_def, globalHaarTraceCoefficient_star B Q hBH hQH]
  have h := globalHaarTraceCoefficient_product B Q Q hBB hB hQ
  simp_rw [← hp] at h
  rw [integral_complex_ofReal, hQQ, Matrix.trace_one] at h
  have hD : (Fintype.card N : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card N : ℂ)⁻¹ * ((Fintype.card N : ℂ) ^ 2 - 1)⁻¹ *
      (Fintype.card N : ℂ) = ((Fintype.card N : ℂ) ^ 2 - 1)⁻¹ := by
    field_simp
  rw [he] at h
  have hcast : ((Fintype.card N : ℂ) ^ 2 - 1)⁻¹ =
      ((1 / ((Fintype.card N : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by push_cast; simp
  apply Complex.ofReal_injective
  rw [h, hcast]

instance globalHaar_isInvInvariant : (globalHaar N).IsInvInvariant where
  inv_eq_self := by
    let ν := (globalHaar N).inv
    letI : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map continuous_inv.measurable.aemeasurable
    have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (globalHaar N)
    have hu := congrArg (fun τ : Measure (GlobalUnitary N) => τ Set.univ) h
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hu
    have hc : ν.haarScalarFactor (globalHaar N) = 1 := by exact_mod_cast hu.symm
    simpa only [hc, one_smul] using h

lemma globalHaarTraceCoefficient_inv (B Q : Matrix N N ℂ) (U : GlobalUnitary N) :
    globalHaarTraceCoefficient B Q U⁻¹ = globalHaarTraceCoefficient Q B U := by
  change (Fintype.card N : ℂ)⁻¹ *
    Matrix.trace (Q * ((U⁻¹).val.conjTranspose * B * (U⁻¹).val)) =
    (Fintype.card N : ℂ)⁻¹ * Matrix.trace (B * (U.val.conjTranspose * Q * U.val))
  congr 1
  rw [← unitary.star_eq_inv, unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.trace (Q * (U.val * B * U.val.conjTranspose)) =
        Matrix.trace ((U.val.conjTranspose * Q * U.val) * B) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (Q * U.val) B U.val.conjTranspose
    _ = _ := Matrix.trace_mul_comm _ _

/-- Input-direction covariances, the cancellation needed when a gate acts on
an arbitrary superposition of Pauli strings rather than a single Pauli. -/
theorem globalHaarTraceCoefficient_input_product [Nontrivial N]
    (B C Q : Matrix N N ℂ) (hQQ : Q * Q = 1) (hQ : Matrix.trace Q = 0)
    (hC : Matrix.trace C = 0) :
    (∫ U, globalHaarTraceCoefficient B Q U * globalHaarTraceCoefficient C Q U
      ∂globalHaar N) =
      (Fintype.card N : ℂ)⁻¹ * ((Fintype.card N : ℂ) ^ 2 - 1)⁻¹ *
        Matrix.trace (B * C) := by
  calc
    _ = ∫ U, globalHaarTraceCoefficient B Q U⁻¹ * globalHaarTraceCoefficient C Q U⁻¹
        ∂globalHaar N := (integral_inv_eq_self _ _).symm
    _ = _ := by
      simp_rw [globalHaarTraceCoefficient_inv]
      exact globalHaarTraceCoefficient_product Q B C hQQ hQ hC

end Fluctuations
