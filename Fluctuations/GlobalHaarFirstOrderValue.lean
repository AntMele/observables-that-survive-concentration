import Fluctuations.UnitaryEquivariantClassification

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

lemma matrixSuperTrace_scalarTraceLinear (a b : ℂ) :
    matrixSuperTrace (scalarTraceLinear (N := N) a b) =
      a * (Fintype.card N : ℂ) ^ 2 + b * Fintype.card N := by
  have he (i j : N) : scalarTraceLinear a b (Matrix.single i j 1) i j =
      a + if i = j then b else 0 := by
    by_cases hij : i = j
    · subst j
      simp [scalarTraceLinear, Matrix.trace_single_eq_same]
    · simp [scalarTraceLinear, hij]
  unfold matrixSuperTrace
  simp_rw [he, Finset.sum_add_distrib]
  simp [mul_comm]
  ring

/-- The first-order Haar twirl acts by the exact coefficient
`−1/(D²−1)` on every traceless matrix, for any traceless butterfly involution. -/
theorem globalHaarTwirl_traceless [Nontrivial N]
    (B X : Matrix N N ℂ) (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hX : Matrix.trace X = 0) :
    globalHaarTwirl B X =
      (-1 / ((Fintype.card N : ℂ) ^ 2 - 1)) • X := by
  obtain ⟨a, b, hab⟩ := unitaryConjugationEquivariant_classification
    (globalHaarTwirlLinear B) (globalHaarTwirl_equivariant B)
  have hmaps : globalHaarTwirlLinear B = scalarTraceLinear a b := by
    ext X : 1
    exact hab X
  have hs := globalHaarTwirl_superTrace B
  rw [hmaps, matrixSuperTrace_scalarTraceLinear, hB, zero_pow (by decide)] at hs
  have ho := hab (1 : Matrix N N ℂ)
  change globalHaarTwirl B 1 = _ at ho
  rw [globalHaarTwirl_one B hBB] at ho
  let i : N := Classical.choice inferInstance
  have ho' := congrArg (fun A : Matrix N N ℂ => A i i) ho
  simp only [Matrix.one_apply_eq, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, mul_one, Matrix.trace_one] at ho'
  have hD : (2 : ℝ) ≤ Fintype.card N := by
    exact_mod_cast Fintype.one_lt_card
  have hden : (Fintype.card N : ℂ) ^ 2 - 1 ≠ 0 := by
    intro hzero
    have hr := congrArg Complex.re hzero
    simp [pow_two, Complex.mul_re] at hr
    nlinarith
  have ha : a = -1 / ((Fintype.card N : ℂ) ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    linear_combination hs + ho'
  have hx := hab X
  change globalHaarTwirl B X = _ at hx
  simpa [hX, ha] using hx

/-- Exact actual global-Haar first-order OTOC mean. No density positivity,
Pauli infrastructure, or integration identity is assumed: trace one, tracelessness,
and the two involution equations suffice. -/
theorem globalHaarOTOCMean_one_exact [Nontrivial N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hMM : M * M = 1) (hM : Matrix.trace M = 0) :
    globalHaarOTOCMean ρ B M 1 = -1 / ((Fintype.card N : ℂ) ^ 2 - 1) := by
  rw [globalHaarOTOCMean_eq_trace_matrixMean, globalHaarOTOCMatrixMean_one_eq_twirl,
    globalHaarTwirl_traceless B M hBB hB hM, Matrix.smul_mul, hMM]
  simp [hρ]

/-- The exact norm of the actual first-order global Haar mean. -/
theorem globalHaarOTOCMean_one_norm [Nontrivial N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hMM : M * M = 1) (hM : Matrix.trace M = 0) :
    ‖globalHaarOTOCMean ρ B M 1‖ = 1 / ((Fintype.card N : ℝ) ^ 2 - 1) := by
  have hD : (2 : ℝ) ≤ Fintype.card N := by
    exact_mod_cast Fintype.one_lt_card
  have hp : 0 < (Fintype.card N : ℝ) ^ 2 - 1 := by nlinarith
  rw [globalHaarOTOCMean_one_exact ρ B M hρ hBB hB hMM hM]
  have he : (Fintype.card N : ℂ) ^ 2 - 1 =
      (((Fintype.card N : ℝ) ^ 2 - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, norm_div, norm_neg, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp]

/-- Uniform dimension-decay estimate for the actual first-order global Haar mean. -/
theorem globalHaarOTOCMean_one_norm_le_two_div_dim_sq [Nontrivial N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hMM : M * M = 1) (hM : Matrix.trace M = 0) :
    ‖globalHaarOTOCMean ρ B M 1‖ ≤ 2 / (Fintype.card N : ℝ) ^ 2 := by
  rw [globalHaarOTOCMean_one_norm ρ B M hρ hBB hB hMM hM]
  have hD : (2 : ℝ) ≤ Fintype.card N := by
    exact_mod_cast Fintype.one_lt_card
  have hp : 0 < (Fintype.card N : ℝ) ^ 2 - 1 := by nlinarith
  have hp' : 0 < (Fintype.card N : ℝ) ^ 2 := by nlinarith
  apply (div_le_div_iff₀ hp hp').2
  nlinarith

/-- The small-Haar-mean hypothesis needed by the transition-window theorem is
discharged at first order as soon as the global dimension is at least three. -/
theorem globalHaarOTOCMean_one_norm_le_quarter [Nontrivial N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hMM : M * M = 1) (hM : Matrix.trace M = 0)
    (hsize : 3 ≤ Fintype.card N) :
    ‖globalHaarOTOCMean ρ B M 1‖ ≤ 1 / 4 := by
  rw [globalHaarOTOCMean_one_norm ρ B M hρ hBB hB hMM hM]
  have hD : (3 : ℝ) ≤ Fintype.card N := by exact_mod_cast hsize
  have hp : 0 < (Fintype.card N : ℝ) ^ 2 - 1 := by nlinarith
  apply (div_le_iff₀ hp).2
  nlinarith

end Fluctuations
