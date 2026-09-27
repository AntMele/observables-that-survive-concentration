import Fluctuations.GlobalHaarStateIndependence

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The genuine Haar conjugate of a fixed butterfly matrix. -/
noncomputable def globalHaarConjugate (B : Matrix N N ℂ) :
    C(GlobalUnitary N, Matrix N N ℂ) where
  toFun U := U.val.conjTranspose * B * U.val
  continuous_toFun := by fun_prop

/-- The actual conjugation-twirl integrand used by the first-order OTOC. -/
noncomputable def globalHaarTwirlIntegrand (B X : Matrix N N ℂ) :
    C(GlobalUnitary N, Matrix N N ℂ) where
  toFun U := globalHaarConjugate B U * X * globalHaarConjugate B U
  continuous_toFun := by fun_prop

lemma globalHaarTwirlIntegrand_integrable (B X : Matrix N N ℂ) :
    Integrable (globalHaarTwirlIntegrand B X) (globalHaar N) :=
  (globalHaarTwirlIntegrand B X).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual first-order Haar twirl, not an assumed depolarizing map. -/
noncomputable def globalHaarTwirl (B X : Matrix N N ℂ) : Matrix N N ℂ :=
  ∫ U, globalHaarTwirlIntegrand B X U ∂globalHaar N

lemma globalHaarTwirl_add (B X Y : Matrix N N ℂ) :
    globalHaarTwirl B (X + Y) = globalHaarTwirl B X + globalHaarTwirl B Y := by
  unfold globalHaarTwirl
  simp only [globalHaarTwirlIntegrand, ContinuousMap.coe_mk, Matrix.mul_add, Matrix.add_mul]
  exact integral_add (globalHaarTwirlIntegrand_integrable B X)
    (globalHaarTwirlIntegrand_integrable B Y)

lemma globalHaarTwirl_smul (B X : Matrix N N ℂ) (c : ℂ) :
    globalHaarTwirl B (c • X) = c • globalHaarTwirl B X := by
  unfold globalHaarTwirl
  simp only [globalHaarTwirlIntegrand, ContinuousMap.coe_mk, Matrix.mul_smul, Matrix.smul_mul]
  exact integral_smul c _

noncomputable def globalHaarTwirlLinear (B : Matrix N N ℂ) :
    Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ where
  toFun := globalHaarTwirl B
  map_add' := globalHaarTwirl_add B
  map_smul' := fun c X => globalHaarTwirl_smul B X c

lemma globalHaarConjugate_involution (B : Matrix N N ℂ) (hB : B * B = 1)
    (U : GlobalUnitary N) : globalHaarConjugate B U * globalHaarConjugate B U = 1 :=
  unitary_conjugate_involution U.val B U.prop hB

/-- A butterfly involution makes the actual twirl unital. -/
theorem globalHaarTwirl_one (B : Matrix N N ℂ) (hB : B * B = 1) :
    globalHaarTwirl B 1 = 1 := by
  unfold globalHaarTwirl
  have hp (U : GlobalUnitary N) : globalHaarTwirlIntegrand B 1 U = 1 := by
    change globalHaarConjugate B U * 1 * globalHaarConjugate B U = 1
    rw [Matrix.mul_one, globalHaarConjugate_involution B hB]
  simp_rw [hp]
  simp

lemma globalHaarConjugate_trace (B : Matrix N N ℂ) (U : GlobalUnitary N) :
    Matrix.trace (globalHaarConjugate B U) = Matrix.trace B := by
  change Matrix.trace (U.val.conjTranspose * B * U.val) = Matrix.trace B
  rw [Matrix.trace_mul_cycle]
  have hU : U.val * U.val.conjTranspose = 1 := U.prop.2
  rw [hU, Matrix.one_mul]

/-- The actual twirl preserves trace whenever the butterfly is an involution. -/
theorem globalHaarTwirl_trace (B X : Matrix N N ℂ) (hB : B * B = 1) :
    Matrix.trace (globalHaarTwirl B X) = Matrix.trace X := by
  have h := (stateTraceCLM (1 : Matrix N N ℂ)).integral_comp_comm
    (globalHaarTwirlIntegrand_integrable B X)
  have hp (U : GlobalUnitary N) : Matrix.trace (globalHaarTwirlIntegrand B X U) =
      Matrix.trace X := by
    change Matrix.trace (globalHaarConjugate B U * X * globalHaarConjugate B U) = _
    rw [Matrix.trace_mul_cycle, globalHaarConjugate_involution B hB, Matrix.one_mul]
  have hi : (∫ U, Matrix.trace (globalHaarTwirlIntegrand B X U) ∂globalHaar N) =
      Matrix.trace (globalHaarTwirl B X) := by
    change (∫ U, Matrix.trace (1 * globalHaarTwirlIntegrand B X U) ∂globalHaar N) =
      Matrix.trace (1 * globalHaarTwirl B X) at h
    simpa only [Matrix.one_mul] using h
  rw [← hi]
  simp_rw [hp]
  simp

/-- The exact first-order OTOC mean is the actual Haar twirl of the probe,
multiplied by the same probe. -/
theorem globalHaarOTOCMatrixMean_one_eq_twirl (B M : Matrix N N ℂ) :
    globalHaarOTOCMatrixMean B M 1 = globalHaarTwirl B M * M := by
  have h := (matrixSandwichCLM (1 : Matrix N N ℂ) M).integral_comp_comm
    (globalHaarTwirlIntegrand_integrable B M)
  change (∫ U, (1 * globalHaarTwirlIntegrand B M U) * M ∂globalHaar N) =
    (1 * globalHaarTwirl B M) * M at h
  simpa only [globalHaarOTOCMatrixMean, globalOTOCMatrix, globalHaarTwirl,
    globalHaarTwirlIntegrand, globalHaarConjugate, ContinuousMap.coe_mk,
    Matrix.one_mul, Nat.mul_one, pow_two, Matrix.mul_assoc] using h

lemma globalHaarConjugate_mul_right (B : Matrix N N ℂ) (U S : GlobalUnitary N) :
    globalHaarConjugate B (U * S) =
      S.val.conjTranspose * globalHaarConjugate B U * S.val := by
  simp only [globalHaarConjugate, ContinuousMap.coe_mk, Matrix.UnitaryGroup.mul_val,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma globalHaarTwirlIntegrand_conjugate (B X : Matrix N N ℂ) (U S : GlobalUnitary N) :
    globalHaarTwirlIntegrand B (S.val.conjTranspose * X * S.val) (U * S) =
      S.val.conjTranspose * globalHaarTwirlIntegrand B X U * S.val := by
  simp only [globalHaarTwirlIntegrand, ContinuousMap.coe_mk, globalHaarConjugate_mul_right]
  have hSS : S.val * S.val.conjTranspose = 1 := S.prop.2
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc S.val S.val.conjTranspose, hSS, Matrix.one_mul]

/-- The actual Haar twirl intertwines every unitary conjugation. -/
theorem globalHaarTwirl_equivariant (B X : Matrix N N ℂ) (S : GlobalUnitary N) :
    globalHaarTwirl B (S.val.conjTranspose * X * S.val) =
      S.val.conjTranspose * globalHaarTwirl B X * S.val := by
  calc
    globalHaarTwirl B (S.val.conjTranspose * X * S.val) =
        ∫ U, globalHaarTwirlIntegrand B (S.val.conjTranspose * X * S.val) (U * S)
          ∂globalHaar N := (integral_mul_right_eq_self _ S).symm
    _ = ∫ U, S.val.conjTranspose * globalHaarTwirlIntegrand B X U * S.val ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => globalHaarTwirlIntegrand_conjugate B X U S
    _ = S.val.conjTranspose * globalHaarTwirl B X * S.val :=
      (matrixSandwichCLM S.val.conjTranspose S.val).integral_comp_comm
        (globalHaarTwirlIntegrand_integrable B X)

noncomputable def matrixEntryCLM (i j : N) : Matrix N N ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma matrix_sandwich_single_entry (A : Matrix N N ℂ) (i j : N) :
    (A * (Matrix.single i j (1 : ℂ) : Matrix N N ℂ) * A) i j = A i i * A j j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hbj]
    simp
  · simp

lemma globalHaarTwirl_single_entry (B : Matrix N N ℂ) (i j : N) :
    globalHaarTwirl B (Matrix.single i j 1) i j =
      ∫ U, globalHaarConjugate B U i i * globalHaarConjugate B U j j ∂globalHaar N := by
  have h := (matrixEntryCLM i j).integral_comp_comm
    (globalHaarTwirlIntegrand_integrable B (Matrix.single i j 1))
  change (∫ U, globalHaarTwirlIntegrand B (Matrix.single i j 1) U i j ∂globalHaar N) =
    globalHaarTwirl B (Matrix.single i j 1) i j at h
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => matrix_sandwich_single_entry (globalHaarConjugate B U) i j

/-- Trace of a matrix superoperator in the standard matrix-unit basis. -/
noncomputable def matrixSuperTrace (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) : ℂ :=
  ∑ i : N, ∑ j : N, T (Matrix.single i j 1) i j

/-- The actual Haar twirl's superoperator trace is the squared butterfly trace.
In particular it vanishes for the nonidentity Pauli butterflies in the paper. -/
theorem globalHaarTwirl_superTrace (B : Matrix N N ℂ) :
    matrixSuperTrace (globalHaarTwirlLinear B) = (Matrix.trace B) ^ 2 := by
  have hi (i j : N) : Integrable
      (fun U : GlobalUnitary N => globalHaarConjugate B U i i * globalHaarConjugate B U j j)
      (globalHaar N) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _
  unfold matrixSuperTrace
  change (∑ i : N, ∑ j : N, globalHaarTwirl B (Matrix.single i j 1) i j) = _
  simp_rw [globalHaarTwirl_single_entry]
  simp_rw [← integral_finset_sum _ (fun j _ => hi _ j)]
  rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))]
  have hp (U : GlobalUnitary N) :
      (∑ i : N, ∑ j : N, globalHaarConjugate B U i i * globalHaarConjugate B U j j) =
        (Matrix.trace B) ^ 2 := by
    rw [← Finset.sum_mul_sum]
    change Matrix.trace (globalHaarConjugate B U) * Matrix.trace (globalHaarConjugate B U) = _
    rw [globalHaarConjugate_trace]
    ring
  simp_rw [hp]
  simp

end Fluctuations
