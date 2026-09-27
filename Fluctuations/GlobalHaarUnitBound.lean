import Fluctuations.GlobalHaarPauliMean

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

lemma hermitian_involution_mem_unitary (B : Matrix N N ℂ)
    (hB : B.IsHermitian) (hB2 : B * B = 1) : B ∈ Matrix.unitaryGroup N ℂ := by
  constructor <;> simpa only [Matrix.star_eq_conjTranspose, hB.eq] using hB2

lemma globalUnitary_trace_norm_le_card (U : GlobalUnitary N) :
    ‖Matrix.trace U.val‖ ≤ Fintype.card N := by
  calc
    ‖Matrix.trace U.val‖ = ‖∑ i : N, U.val i i‖ := rfl
    _ ≤ ∑ i : N, ‖U.val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : N, (1 : ℝ) := Finset.sum_le_sum fun i _ => globalUnitary_entry_norm_le_one U i i
    _ = _ := by simp

lemma globalOTOCMatrix_mem_unitary (B M : Matrix N N ℂ)
    (hB : B.IsHermitian) (hB2 : B * B = 1)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (k : ℕ) (U : GlobalUnitary N) :
    globalOTOCMatrix B M k U ∈ Matrix.unitaryGroup N ℂ := by
  let B' : GlobalUnitary N := ⟨B, hermitian_involution_mem_unitary B hB hB2⟩
  let M' : GlobalUnitary N := ⟨M, hermitian_involution_mem_unitary M hM hM2⟩
  have h := ((star U * B' * U * M') ^ (2 * k)).prop
  simpa only [SubmonoidClass.coe_pow, Matrix.UnitaryGroup.mul_val, unitary.coe_star,
    Matrix.star_eq_conjTranspose] using h

lemma globalOTOC_maximallyMixed_norm_le_one [Nonempty N]
    (B M : Matrix N N ℂ) (hB : B.IsHermitian) (hB2 : B * B = 1)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (k : ℕ) (U : GlobalUnitary N) :
    ‖globalOTOC (globalMaximallyMixedState N) B M k U‖ ≤ 1 := by
  have htrace := globalUnitary_trace_norm_le_card
    ⟨globalOTOCMatrix B M k U, globalOTOCMatrix_mem_unitary B M hB hB2 hM hM2 k U⟩
  have hD : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  change ‖Matrix.trace (((Fintype.card N : ℂ)⁻¹ • (1 : Matrix N N ℂ)) *
    globalOTOCMatrix B M k U)‖ ≤ 1
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, norm_smul, norm_inv]
  simp only [Complex.norm_natCast]
  calc
    (Fintype.card N : ℝ)⁻¹ * ‖Matrix.trace (globalOTOCMatrix B M k U)‖ ≤
        (Fintype.card N : ℝ)⁻¹ * Fintype.card N :=
      mul_le_mul_of_nonneg_left htrace (inv_nonneg.mpr hD.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hD)

/-- A dimension-free unit bound for the actual Haar mean. State independence
extends the normalized-trace unitary estimate to every trace-one matrix. -/
theorem globalHaarOTOCMean_norm_le_one [Nonempty N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0) (k : ℕ) :
    ‖globalHaarOTOCMean ρ B M k‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := globalHaarOTOCMean_state_independent_of_traceless_involution
    B M hM hM2 hMtr k
  rw [ha ρ hρ, ← ha (globalMaximallyMixedState N) globalMaximallyMixedState_trace]
  unfold globalHaarOTOCMean
  calc
    ‖∫ U, globalOTOC (globalMaximallyMixedState N) B M k U ∂globalHaar N‖ ≤
        ∫ U, ‖globalOTOC (globalMaximallyMixedState N) B M k U‖ ∂globalHaar N :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _U : GlobalUnitary N, (1 : ℝ) ∂globalHaar N :=
      integral_mono (globalOTOC_integrable (globalMaximallyMixedState N) B M k).norm
        (integrable_const 1) (fun U => globalOTOC_maximallyMixed_norm_le_one B M hB hB2 hM hM2 k U)
    _ = 1 := by simp

end Fluctuations
