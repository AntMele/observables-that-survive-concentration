import Fluctuations.HaarMixedCovariance
import Fluctuations.PauliBasis

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

abbrev TwoQubitBasis := Fin 2 × Fin 2
abbrev TwoQubitPauliLabel := Fin 4 × Fin 4
abbrev TwoQubitUnitary := GlobalUnitary TwoQubitBasis

/-- The genuine two-qubit Pauli transfer coefficient under unitary conjugation. -/
noncomputable def twoQubitPauliCoefficient (p q : TwoQubitPauliLabel) : C(TwoQubitUnitary, ℂ) :=
  globalHaarTraceCoefficient (twoQubitPauli p) (twoQubitPauli q)

/-- The complete Haar second moment includes cancellation of all distinct
input or output Pauli directions, not just equality of their squared weights. -/
theorem twoQubitPauliCoefficient_haar_product (p s q r : TwoQubitPauliLabel)
    (hp : p ≠ (0, 0)) (hq : q ≠ (0, 0)) :
    (∫ U, twoQubitPauliCoefficient p q U * twoQubitPauliCoefficient s r U
      ∂globalHaar TwoQubitBasis) = if p = s ∧ q = r then (1 / 15 : ℂ) else 0 := by
  have h := globalHaarTraceCoefficient_mixed_product
    (twoQubitPauli p) (twoQubitPauli s) (twoQubitPauli q) (twoQubitPauli r)
    (by simp [twoQubitPauli_trace, hp]) (by simp [twoQubitPauli_trace, hq])
  change (∫ U, twoQubitPauliCoefficient p q U * twoQubitPauliCoefficient s r U
    ∂globalHaar TwoQubitBasis) = _ at h
  rw [h, twoQubitPauli_trace_mul, twoQubitPauli_trace_mul]
  by_cases hps : p = s <;> by_cases hqr : q = r <;> norm_num [hps, hqr]

/-- A genuine Haar gate sends each nonidentity Pauli with equal squared weight
to each of the fifteen nonidentity output Paulis. -/
theorem twoQubitPauliCoefficient_haar_norm_sq (p q : TwoQubitPauliLabel)
    (hp : p ≠ (0, 0)) (hq : q ≠ (0, 0)) :
    (∫ U, ‖twoQubitPauliCoefficient p q U‖ ^ 2 ∂globalHaar TwoQubitBasis) = 1 / 15 := by
  have h := globalHaarTraceCoefficient_norm_sq
    (twoQubitPauli p) (twoQubitPauli q) (twoQubitPauli_hermitian p)
    (twoQubitPauli_involution p) (by simp [twoQubitPauli_trace, hp])
    (twoQubitPauli_hermitian q) (twoQubitPauli_involution q)
    (by simp [twoQubitPauli_trace, hq])
  norm_num at h
  exact h

/-- The paper's local observable A(G): average right-output squared weight
over X⊗I, Y⊗I, and Z⊗I. The underlying gate law is normalized Haar on U(4). -/
noncomputable def localPauliA : C(TwoQubitUnitary, ℝ) where
  toFun U := (1 / 3 : ℝ) * ∑ α : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
    ‖twoQubitPauliCoefficient (α.succ, 0) (γ, δ.succ) U‖ ^ 2
  continuous_toFun := by fun_prop

lemma twoQubitPauliCoefficient_one (p q : TwoQubitPauliLabel) :
    twoQubitPauliCoefficient p q 1 = if p = q then 1 else 0 := by
  simp only [twoQubitPauliCoefficient, globalHaarTraceCoefficient, globalHaarConjugate,
    ContinuousMap.coe_mk, OneMemClass.coe_one, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one, twoQubitPauli_trace_mul]
  by_cases h : p = q <;> norm_num [h, eq_comm]

@[simp] lemma twoQubitPauliCoefficient_zero_input (q : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    twoQubitPauliCoefficient (0, 0) q U = if q = (0, 0) then 1 else 0 := by
  have hU : globalHaarConjugate (1 : Matrix TwoQubitBasis TwoQubitBasis ℂ) U = 1 := by
    change U.val.conjTranspose * 1 * U.val = 1
    simpa only [Matrix.mul_one] using U.prop.1
  change (Fintype.card TwoQubitBasis : ℂ)⁻¹ *
    Matrix.trace (twoQubitPauli q * globalHaarConjugate (twoQubitPauli (0, 0)) U) = _
  rw [twoQubitPauli_zero, hU, Matrix.mul_one, twoQubitPauli_trace]
  by_cases h : q = (0, 0) <;> norm_num [h]

@[simp] lemma twoQubitPauliCoefficient_zero_output (p : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    twoQubitPauliCoefficient p (0, 0) U = if p = (0, 0) then 1 else 0 := by
  change (Fintype.card TwoQubitBasis : ℂ)⁻¹ *
    Matrix.trace (twoQubitPauli (0, 0) * globalHaarConjugate (twoQubitPauli p) U) = _
  rw [twoQubitPauli_zero, Matrix.one_mul, globalHaarConjugate_trace, twoQubitPauli_trace]
  by_cases h : p = (0, 0) <;> norm_num [h]

theorem twoQubitPauliCoefficient_haar_mean (p q : TwoQubitPauliLabel) :
    (∫ U, twoQubitPauliCoefficient p q U ∂globalHaar TwoQubitBasis) =
      if p = (0, 0) ∧ q = (0, 0) then 1 else 0 := by
  by_cases hp : p = (0, 0)
  · subst p
    simp
  by_cases hq : q = (0, 0)
  · subst q
    simp [hp]
  have h := twoQubitPauliCoefficient_haar_product p (0, 0) q (0, 0) hp hq
  simpa [hp] using h

/-- The exact local Markov kernel: the identity is fixed, and every other
input is uniform among the fifteen nonidentity outputs. -/
noncomputable def localPauliHaarKernel (q p : TwoQubitPauliLabel) : ℝ :=
  if p = (0, 0) then (if q = (0, 0) then 1 else 0)
  else if q = (0, 0) then 0 else 1 / 15

/-- The full coefficient covariance, including the identity sectors. -/
theorem twoQubitPauliCoefficient_haar_covariance (p s q r : TwoQubitPauliLabel) :
    (∫ U, twoQubitPauliCoefficient p q U * twoQubitPauliCoefficient s r U
      ∂globalHaar TwoQubitBasis) =
      if p = s ∧ q = r then (localPauliHaarKernel q p : ℂ) else 0 := by
  by_cases hp : p = (0, 0)
  · subst p
    by_cases hq : q = (0, 0)
    · subst q
      simpa [localPauliHaarKernel, eq_comm] using twoQubitPauliCoefficient_haar_mean s r
    · simp [hq, localPauliHaarKernel]
  by_cases hq : q = (0, 0)
  · subst q
    simp [hp, localPauliHaarKernel]
  rw [twoQubitPauliCoefficient_haar_product p s q r hp hq]
  simp [localPauliHaarKernel, hp, hq]

/-- Real Pauli transfer entries, equal to the complex entries because both
the input and output Paulis are Hermitian. -/
noncomputable def twoQubitPauliTransfer (U : TwoQubitUnitary)
    (q p : TwoQubitPauliLabel) : ℝ := (twoQubitPauliCoefficient p q U).re

lemma twoQubitPauliTransfer_cast (U : TwoQubitUnitary) (q p : TwoQubitPauliLabel) :
    (twoQubitPauliTransfer U q p : ℂ) = twoQubitPauliCoefficient p q U := by
  have h := globalHaarTraceCoefficient_star (twoQubitPauli p) (twoQubitPauli q)
    (twoQubitPauli_hermitian p) (twoQubitPauli_hermitian q) U
  have hr := congrArg Complex.im h
  have hz : (twoQubitPauliCoefficient p q U).im = 0 := by
    change -(twoQubitPauliCoefficient p q U).im = (twoQubitPauliCoefficient p q U).im at hr
    linarith
  exact Complex.ext rfl (by simp [hz])

theorem twoQubitPauliTransfer_haar_covariance (p s q r : TwoQubitPauliLabel) :
    (∫ U, twoQubitPauliTransfer U q p * twoQubitPauliTransfer U r s
      ∂globalHaar TwoQubitBasis) =
      if p = s ∧ q = r then localPauliHaarKernel q p else 0 := by
  have h := twoQubitPauliCoefficient_haar_covariance p s q r
  simp_rw [← twoQubitPauliTransfer_cast, ← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  rw [h]
  split_ifs <;> simp

lemma twoQubitPauliCoefficient_column_inner (p s : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    (∑ q, twoQubitPauliCoefficient p q U * twoQubitPauliCoefficient s q U) =
      if p = s then 1 else 0 := by
  calc
    _ = (1 / 4 : ℂ) * Matrix.trace
        (globalHaarConjugate (twoQubitPauli p) U * globalHaarConjugate (twoQubitPauli s) U) := by
      rw [twoQubitPauli_trace_mul_parseval, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [twoQubitPauliCoefficient, globalHaarTraceCoefficient, ContinuousMap.coe_mk,
        Fintype.card_prod, Fintype.card_fin]
      norm_num
      ring
    _ = _ := by
      rw [globalHaarConjugate_mul, globalHaarConjugate_trace, twoQubitPauli_trace_mul]
      split_ifs <;> norm_num

theorem twoQubitPauliTransfer_column_inner (p s : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    (∑ q, twoQubitPauliTransfer U q p * twoQubitPauliTransfer U q s) =
      if p = s then 1 else 0 := by
  have h := twoQubitPauliCoefficient_column_inner p s U
  simp_rw [← twoQubitPauliTransfer_cast, ← Complex.ofReal_mul, ← Complex.ofReal_sum] at h
  apply Complex.ofReal_injective
  rw [h]
  split_ifs <;> simp

theorem twoQubitPauliTransfer_column_sq (p : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    (∑ q, twoQubitPauliTransfer U q p ^ 2) = 1 := by
  simpa only [pow_two, if_pos rfl] using twoQubitPauliTransfer_column_inner p p U

lemma twoQubitPauliTransfer_inv (U : TwoQubitUnitary) (q p : TwoQubitPauliLabel) :
    twoQubitPauliTransfer U⁻¹ q p = twoQubitPauliTransfer U p q := by
  exact congrArg Complex.re (globalHaarTraceCoefficient_inv (twoQubitPauli p) (twoQubitPauli q) U)

theorem twoQubitPauliTransfer_row_sq (q : TwoQubitPauliLabel) (U : TwoQubitUnitary) :
    (∑ p, twoQubitPauliTransfer U q p ^ 2) = 1 := by
  simpa only [twoQubitPauliTransfer_inv] using twoQubitPauliTransfer_column_sq q U⁻¹

@[simp] theorem localPauliA_one : localPauliA 1 = 0 := by
  simp [localPauliA, twoQubitPauliCoefficient_one, Prod.mk.injEq, eq_comm]

lemma localPauliA_memLp : MemLp localPauliA 2 (globalHaar TwoQubitBasis) :=
  localPauliA.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The exact Haar average of the local right-output observable is 4/5. -/
theorem localPauliA_haar_mean : (∫ U, localPauliA U ∂globalHaar TwoQubitBasis) = 4 / 5 := by
  have hi (p q : TwoQubitPauliLabel) :
      Integrable (fun U => ‖twoQubitPauliCoefficient p q U‖ ^ 2) (globalHaar TwoQubitBasis) :=
    ((twoQubitPauliCoefficient p q).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hγ (α : Fin 3) (γ : Fin 4) :=
    integrable_finset_sum Finset.univ (fun (δ : Fin 3) _ => hi (α.succ, 0) (γ, δ.succ))
  have hα (α : Fin 3) := integrable_finset_sum Finset.univ (fun γ _ => hγ α γ)
  change (∫ U, (1 / 3 : ℝ) * ∑ α : Fin 3, ∑ γ : Fin 4, ∑ δ : Fin 3,
    ‖twoQubitPauliCoefficient (α.succ, 0) (γ, δ.succ) U‖ ^ 2
      ∂globalHaar TwoQubitBasis) = _
  rw [integral_const_mul, integral_finset_sum _ (fun α _ => hα α)]
  simp_rw [integral_finset_sum _ (fun γ _ => hγ _ γ),
    integral_finset_sum _ (fun (δ : Fin 3) _ => hi _ (_, δ.succ))]
  have hv (α : Fin 3) (γ : Fin 4) (δ : Fin 3) :
      (∫ U, ‖twoQubitPauliCoefficient (α.succ, 0) (γ, δ.succ) U‖ ^ 2
        ∂globalHaar TwoQubitBasis) = 1 / 15 :=
    twoQubitPauliCoefficient_haar_norm_sq _ _ (by simp) (by simp)
  simp_rw [hv]
  norm_num

/-- A is genuinely random under Haar measure. Its exact positive variance is
a fixed numerical constant; no nondegeneracy premise is imposed. -/
theorem localPauliA_variance_pos : 0 < variance localPauliA (globalHaar TwoQubitBasis) := by
  apply lt_of_le_of_ne (variance_nonneg _ _)
  intro hzero
  have he : evariance localPauliA (globalHaar TwoQubitBasis) = 0 := by
    rw [← localPauliA_memLp.ofReal_variance_eq, ← hzero]
    simp
  have hae := (evariance_eq_zero_iff localPauliA_memLp.aemeasurable).mp he
  have hall := Measure.eq_of_ae_eq hae localPauliA.continuous continuous_const
  have h := congrFun hall (1 : TwoQubitUnitary)
  rw [localPauliA_one, localPauliA_haar_mean] at h
  norm_num at h

end Fluctuations
