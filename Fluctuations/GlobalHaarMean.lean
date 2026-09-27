import Fluctuations.MeanChange
import Fluctuations.ActiveHaarCircuit

open MeasureTheory Set
open scoped Matrix Matrix.Norms.Elementwise

namespace Fluctuations

/-- The genuine global unitary group, in an arbitrary finite matrix dimension. -/
abbrev GlobalUnitary (N : Type*) [Fintype N] [DecidableEq N] :=
  Matrix.unitaryGroup N ℂ

variable {N : Type*} [Fintype N] [DecidableEq N]

lemma globalUnitary_entry_norm_le_one (A : GlobalUnitary N) (i j : N) :
    ‖A.val i j‖ ≤ 1 := by
  have hrow := congrArg (fun T : Matrix N N ℂ => (T i i).re) A.prop.2
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum] at hrow
  have heq : (∑ k : N, Complex.normSq (A.val i k)) = 1 := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Matrix.one_apply_eq, Complex.one_re] using hrow
  have hle := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset N)) => Complex.normSq_nonneg (A.val i k))
    (Finset.mem_univ j)
  rw [heq, Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (A.val i j)]

lemma isClosed_globalUnitary :
    IsClosed (Matrix.unitaryGroup N ℂ : Set (Matrix N N ℂ)) := by
  have heq : (Matrix.unitaryGroup N ℂ : Set (Matrix N N ℂ)) =
      {A | A * star A = 1} := by
    ext A
    exact Matrix.mem_unitaryGroup_iff
  rw [heq]
  exact isClosed_eq (continuous_id.mul continuous_star) continuous_const

instance globalUnitary_compactSpace : CompactSpace (GlobalUnitary N) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_globalUnitary
  intro A hA i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact globalUnitary_entry_norm_le_one ⟨A, hA⟩ i j

instance globalUnitary_secondCountableTopology : SecondCountableTopology (GlobalUnitary N) := by
  letI : SecondCountableTopology (Matrix N N ℂ) := by
    change SecondCountableTopology (N → N → ℂ)
    infer_instance
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance globalUnitary_measurableSpace : MeasurableSpace (GlobalUnitary N) :=
  borel (GlobalUnitary N)

instance globalUnitary_borelSpace : BorelSpace (GlobalUnitary N) := ⟨rfl⟩

/-- Normalized Haar probability measure on the full global unitary group. -/
noncomputable def globalHaar (N : Type*) [Fintype N] [DecidableEq N] :
    Measure (GlobalUnitary N) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance globalHaar_probability : IsProbabilityMeasure (globalHaar N) where
  measure_univ := Measure.haarMeasure_self

instance globalHaar_isHaarMeasure : Measure.IsHaarMeasure (globalHaar N) :=
  Measure.isHaarMeasure_haarMeasure _

instance globalHaar_isMulRightInvariant : (globalHaar N).IsMulRightInvariant where
  map_mul_right_eq_self S := by
    let ν := Measure.map (fun U : GlobalUnitary N => U * S) (globalHaar N)
    haveI : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map (measurable_mul_const S).aemeasurable
    have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (globalHaar N)
    have hu := congrArg (fun τ : Measure (GlobalUnitary N) => τ Set.univ) h
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hu
    have hc : ν.haarScalarFactor (globalHaar N) = 1 := by exact_mod_cast hu.symm
    simpa only [hc, one_smul] using h

/-- The matrix whose state expectation is the actual fixed-order OTOC. -/
noncomputable def globalOTOCMatrix (B M : Matrix N N ℂ) (k : ℕ) :
    C(GlobalUnitary N, Matrix N N ℂ) where
  toFun U := (U.val.conjTranspose * B * U.val * M) ^ (2 * k)
  continuous_toFun := by fun_prop

/-- The actual trace OTOC on global unitary matrices. -/
noncomputable def globalOTOC (ρ B M : Matrix N N ℂ) (k : ℕ) :
    C(GlobalUnitary N, ℂ) where
  toFun U := Matrix.trace (ρ * globalOTOCMatrix B M k U)
  continuous_toFun := by fun_prop

/-- Actual global-Haar mean, rather than an unspecified reference scalar. -/
noncomputable def globalHaarOTOCMean (ρ B M : Matrix N N ℂ) (k : ℕ) : ℂ :=
  ∫ U, globalOTOC ρ B M k U ∂globalHaar N

/-- The matrix-valued global Haar average before taking a state expectation. -/
noncomputable def globalHaarOTOCMatrixMean (B M : Matrix N N ℂ) (k : ℕ) :
    Matrix N N ℂ := ∫ U, globalOTOCMatrix B M k U ∂globalHaar N

/-- The manuscript's observable-specific moment-control property, with the
reference explicitly identified as the actual global-Haar OTOC mean. -/
def OTOCTestMomentControl (ν : Measure (GlobalUnitary N))
    (ρ B M : Matrix N N ℂ) (k : ℕ) (ε : ℝ) : Prop :=
  ‖(∫ U, globalOTOC ρ B M k U ∂ν) - globalHaarOTOCMean ρ B M k‖ ≤ ε

lemma globalOTOC_integrable (ρ B M : Matrix N N ℂ) (k : ℕ) :
    Integrable (globalOTOC ρ B M k) (globalHaar N) :=
  (globalOTOC ρ B M k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma globalOTOCMatrix_integrable (B M : Matrix N N ℂ) (k : ℕ) :
    Integrable (globalOTOCMatrix B M k) (globalHaar N) :=
  (globalOTOCMatrix B M k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma globalHaar_integral_mul_right (f : GlobalUnitary N → ℂ) (S : GlobalUnitary N) :
    (∫ U, f (U * S) ∂globalHaar N) = ∫ U, f U ∂globalHaar N := by
  exact integral_mul_right_eq_self f S

/-- Matrix multiplication on the two sides is a continuous complex-linear map. -/
noncomputable def matrixSandwichCLM (A B : Matrix N N ℂ) :
    Matrix N N ℂ →L[ℂ] Matrix N N ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

/-- A fixed state's trace expectation is a continuous complex-linear map. -/
noncomputable def stateTraceCLM (ρ : Matrix N N ℂ) : Matrix N N ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => Matrix.trace (ρ * X)
      map_add' := fun X Y => by simp only [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c X => by simp only [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply] }

lemma globalHaarOTOCMean_eq_trace_matrixMean (ρ B M : Matrix N N ℂ) (k : ℕ) :
    globalHaarOTOCMean ρ B M k = Matrix.trace (ρ * globalHaarOTOCMatrixMean B M k) := by
  exact (stateTraceCLM ρ).integral_comp_comm (globalOTOCMatrix_integrable B M k)

lemma unitary_conjugation_pow (S : GlobalUnitary N) (X : Matrix N N ℂ) (r : ℕ) :
    (S.val.conjTranspose * X * S.val) ^ r = S.val.conjTranspose * X ^ r * S.val := by
  induction r with
  | zero =>
      simp only [pow_zero, Matrix.mul_one]
      change 1 = star S.val * S.val
      exact S.prop.1.symm
  | succ r ih =>
      rw [pow_succ, ih, pow_succ]
      have hS : S.val * S.val.conjTranspose = 1 := S.prop.2
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc S.val S.val.conjTranspose, hS, Matrix.one_mul]

/-- Right multiplication by a symmetry of the probe acts by conjugation on
every even-order OTOC matrix, including anticommuting symmetries. -/
lemma globalOTOCMatrix_mul_right (B M : Matrix N N ℂ) (k : ℕ)
    (S : GlobalUnitary N)
    (hS : S.val * M = M * S.val ∨ S.val * M = -(M * S.val))
    (U : GlobalUnitary N) :
    globalOTOCMatrix B M k (U * S) =
      S.val.conjTranspose * globalOTOCMatrix B M k U * S.val := by
  change (((U.val * S.val).conjTranspose * B * (U.val * S.val)) * M) ^ (2 * k) = _
  have heq : (U.val * S.val).conjTranspose * B * (U.val * S.val) * M =
      S.val.conjTranspose * (U.val.conjTranspose * B * U.val) * (S.val * M) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [heq]
  rcases hS with hS | hS
  · rw [hS]
    simpa only [globalOTOCMatrix, ContinuousMap.coe_mk, Matrix.mul_assoc] using
      unitary_conjugation_pow S (U.val.conjTranspose * B * U.val * M) (2 * k)
  · rw [hS, Matrix.mul_neg]
    have hneg (X : Matrix N N ℂ) : (-X) ^ (2 * k) = X ^ (2 * k) := by
      simp only [pow_mul, pow_two, neg_mul_neg]
    rw [hneg]
    simpa only [globalOTOCMatrix, ContinuousMap.coe_mk, Matrix.mul_assoc] using
      unitary_conjugation_pow S (U.val.conjTranspose * B * U.val * M) (2 * k)

/-- The actual global Haar matrix mean is fixed by every symmetry that
commutes or anticommutes with the probe. -/
theorem globalHaarOTOCMatrixMean_conjugation (B M : Matrix N N ℂ) (k : ℕ)
    (S : GlobalUnitary N)
    (hS : S.val * M = M * S.val ∨ S.val * M = -(M * S.val)) :
    S.val.conjTranspose * globalHaarOTOCMatrixMean B M k * S.val =
      globalHaarOTOCMatrixMean B M k := by
  have hp := (matrixSandwichCLM S.val.conjTranspose S.val).integral_comp_comm
    (globalOTOCMatrix_integrable B M k)
  calc
    S.val.conjTranspose * globalHaarOTOCMatrixMean B M k * S.val =
        ∫ U, S.val.conjTranspose * globalOTOCMatrix B M k U * S.val ∂globalHaar N := hp.symm
    _ = ∫ U, globalOTOCMatrix B M k (U * S) ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => (globalOTOCMatrix_mul_right B M k S hS U).symm
    _ = globalHaarOTOCMatrixMean B M k :=
      integral_mul_right_eq_self (globalOTOCMatrix B M k) S

theorem globalHaarOTOCMatrixMean_commute (B M : Matrix N N ℂ) (k : ℕ)
    (S : GlobalUnitary N)
    (hS : S.val * M = M * S.val ∨ S.val * M = -(M * S.val)) :
    Commute S.val (globalHaarOTOCMatrixMean B M k) := by
  have h := congrArg (fun X : Matrix N N ℂ => S.val * X)
    (globalHaarOTOCMatrixMean_conjugation B M k S hS)
  have hSS : S.val * S.val.conjTranspose = 1 := S.prop.2
  simpa only [← Matrix.mul_assoc, hSS, Matrix.one_mul] using h.symm

lemma globalOTOCMatrix_conjugateProbe (B M : Matrix N N ℂ) (k : ℕ)
    (S U : GlobalUnitary N) :
    globalOTOCMatrix B (S.val.conjTranspose * M * S.val) k (U * S) =
      S.val.conjTranspose * globalOTOCMatrix B M k U * S.val := by
  have hSS : S.val * S.val.conjTranspose = 1 := S.prop.2
  have heq : (U.val * S.val).conjTranspose * B * (U.val * S.val) *
      (S.val.conjTranspose * M * S.val) =
        S.val.conjTranspose * (U.val.conjTranspose * B * U.val * M) * S.val := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.val S.val.conjTranspose, hSS, Matrix.one_mul]
  change ((U.val * S.val).conjTranspose * B * (U.val * S.val) *
    (S.val.conjTranspose * M * S.val)) ^ (2 * k) = _
  rw [heq]
  exact unitary_conjugation_pow S _ _

/-- Changing the probe's unitary eigenbasis conjugates the actual global mean. -/
theorem globalHaarOTOCMatrixMean_conjugateProbe (B M : Matrix N N ℂ) (k : ℕ)
    (S : GlobalUnitary N) :
    globalHaarOTOCMatrixMean B (S.val.conjTranspose * M * S.val) k =
      S.val.conjTranspose * globalHaarOTOCMatrixMean B M k * S.val := by
  calc
    globalHaarOTOCMatrixMean B (S.val.conjTranspose * M * S.val) k =
        ∫ U, globalOTOCMatrix B (S.val.conjTranspose * M * S.val) k (U * S) ∂globalHaar N :=
      (integral_mul_right_eq_self _ S).symm
    _ = ∫ U, S.val.conjTranspose * globalOTOCMatrix B M k U * S.val ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (globalOTOCMatrix_conjugateProbe B M k S)
    _ = S.val.conjTranspose * globalHaarOTOCMatrixMean B M k * S.val :=
      (matrixSandwichCLM S.val.conjTranspose S.val).integral_comp_comm
        (globalOTOCMatrix_integrable B M k)

/-- Changing the butterfly's unitary eigenbasis leaves the actual global mean
unchanged, by left Haar invariance. -/
theorem globalHaarOTOCMatrixMean_conjugateButterfly (B M : Matrix N N ℂ) (k : ℕ)
    (S : GlobalUnitary N) :
    globalHaarOTOCMatrixMean (S.val.conjTranspose * B * S.val) M k =
      globalHaarOTOCMatrixMean B M k := by
  have hp (U : GlobalUnitary N) :
      globalOTOCMatrix (S.val.conjTranspose * B * S.val) M k U =
        globalOTOCMatrix B M k (S * U) := by
    simp only [globalOTOCMatrix, ContinuousMap.coe_mk, Matrix.UnitaryGroup.mul_val,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold globalHaarOTOCMatrixMean
  simp_rw [hp]
  exact integral_mul_left_eq_self (globalOTOCMatrix B M k) S

/-- The normalized identity state, with normalization expressed at the matrix
level rather than by modifying the OTOC trace. -/
noncomputable def globalMaximallyMixedState (N : Type*) [Fintype N] [DecidableEq N] :
    Matrix N N ℂ := (Fintype.card N : ℂ)⁻¹ • (1 : Matrix N N ℂ)

lemma globalMaximallyMixedState_trace [Nonempty N] :
    Matrix.trace (globalMaximallyMixedState N) = 1 := by
  have hcard : (Fintype.card N : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [globalMaximallyMixedState, hcard]

end Fluctuations
