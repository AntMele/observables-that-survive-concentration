import Fluctuations.HaarTensorProjection
import Mathlib.Logic.Equiv.Fin.Rotate

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
lemma sum_fin_succ_function (n : ℕ) (f : (Fin (n + 1) → N) → ℂ) :
    (∑ x, f x) = ∑ i : N, ∑ x : Fin n → N, f (Fin.cons i x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => N)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- Matrix powers expanded along all open coordinate paths. -/
lemma matrix_power_path_sum (A : Matrix N N ℂ) (n : ℕ) (i j : N) :
    (A ^ (n + 1)) i j = ∑ x : Fin n → N,
      ∏ t : Fin (n + 1), A (Fin.cons (α := fun _ : Fin (n + 1) => N) i x t) (Fin.snoc (α := fun _ : Fin (n + 1) => N) x j t) := by
  induction n generalizing i j with
  | zero => simp [Fin.snoc]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, sum_fin_succ_function]
    simp_rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro x _
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The trace of a power is the contraction around a cyclic coordinate path. -/
lemma matrix_trace_power_cycle_sum (A : Matrix N N ℂ) {r : ℕ} (hr : 0 < r) :
    Matrix.trace (A ^ r) =
      ∑ x : Fin r → N, ∏ t : Fin r, A (x t) (x (finRotate r t)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Matrix.trace, Matrix.diag, matrix_power_path_sum]
  rw [sum_fin_succ_function]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro t _
  rw [Fin.snoc_eq_cons_rotate]

/-- Exact tensor contraction for the trace of an arbitrary positive power.
The permutation orientation is the literal `finRotate` used by the paper sum. -/
theorem trace_power_eq_tensor_cycle (A : Matrix N N ℂ) {r : ℕ} (hr : 0 < r) :
    Matrix.trace (A ^ r) = Matrix.trace
      (tensorPowerMatrix r A * tensorPositionPermutation N (finRotate r)) := by
  rw [matrix_trace_power_cycle_sum A hr]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    tensorPositionPermutation, mul_ite, mul_one, mul_zero]
  simp [tensorPowerMatrix, Function.comp_def]

/-- Pointwise tensor representation of the actual OTOC trace. -/
theorem globalOTOCMatrix_trace_tensor (B M : Matrix N N ℂ) (k : ℕ) (hk : 0 < k)
    (U : GlobalUnitary N) :
    Matrix.trace (globalOTOCMatrix B M k U) = Matrix.trace
      (((tensorPowerRepresentation (2 * k) U).conjTranspose * tensorPowerMatrix (2 * k) B *
        tensorPowerRepresentation (2 * k) U) * tensorPowerMatrix (2 * k) M *
        tensorPositionPermutation N (finRotate (2 * k))) := by
  change Matrix.trace ((U.val.conjTranspose * B * U.val * M) ^ (2 * k)) = _
  rw [trace_power_eq_tensor_cycle _ (Nat.mul_pos (by decide) hk),
    tensorPowerMatrix_mul, ← tensorPowerRepresentation_conjugate]

/-- A trace contraction commutes with the actual Haar representation average. -/
lemma integral_trace_representation_conjugate_mul
    {W : Type*} [Fintype W] [DecidableEq W]
    (R : GlobalUnitary N →* Matrix W W ℂ) (hR : Continuous R)
    (X Q : Matrix W W ℂ) :
    (∫ U, Matrix.trace (((R U).conjTranspose * X * R U) * Q) ∂globalHaar N) =
      Matrix.trace (globalHaarRepresentationMean R X * Q) := by
  have h := (stateTraceCLM Q).integral_comp_comm
    (globalHaarRepresentationMean_integrable R hR X)
  change (∫ U, Matrix.trace (Q * ((R U).conjTranspose * X * R U)) ∂globalHaar N) =
    Matrix.trace (Q * globalHaarRepresentationMean R X) at h
  calc
    _ = ∫ U, Matrix.trace (Q * ((R U).conjTranspose * X * R U)) ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q * globalHaarRepresentationMean R X) := h
    _ = _ := Matrix.trace_mul_comm _ _

/-- Exact reduction of the normalized-trace global Haar OTOC to the genuine
Haar average in the tensor-power representation. This is an integral identity,
not an assumed Weingarten expansion. -/
theorem globalHaarOTOCMean_maximallyMixed_eq_tensor (B M : Matrix N N ℂ)
    (k : ℕ) (hk : 0 < k) :
    globalHaarOTOCMean (globalMaximallyMixedState N) B M k =
      (Fintype.card N : ℂ)⁻¹ * Matrix.trace
        (globalHaarRepresentationMean (tensorPowerRepresentation (N := N) (2 * k))
          (tensorPowerMatrix (2 * k) B) * tensorPowerMatrix (2 * k) M *
          tensorPositionPermutation N (finRotate (2 * k))) := by
  have hp (U : GlobalUnitary N) :
      globalOTOC (globalMaximallyMixedState N) B M k U =
        (Fintype.card N : ℂ)⁻¹ * Matrix.trace
          (((tensorPowerRepresentation (2 * k) U).conjTranspose * tensorPowerMatrix (2 * k) B *
            tensorPowerRepresentation (2 * k) U) * tensorPowerMatrix (2 * k) M *
            tensorPositionPermutation N (finRotate (2 * k))) := by
    change Matrix.trace (((Fintype.card N : ℂ)⁻¹ • (1 : Matrix N N ℂ)) *
      globalOTOCMatrix B M k U) = _
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    rw [globalOTOCMatrix_trace_tensor B M k hk U]
    rfl
  unfold globalHaarOTOCMean
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  simpa only [Matrix.mul_assoc] using
    integral_trace_representation_conjugate_mul
      (tensorPowerRepresentation (N := N) (2 * k)) (tensorPowerRepresentation_continuous (2 * k))
      (tensorPowerMatrix (2 * k) B)
      (tensorPowerMatrix (2 * k) M * tensorPositionPermutation N (finRotate (2 * k)))

end Fluctuations
