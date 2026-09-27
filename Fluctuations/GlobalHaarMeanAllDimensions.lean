import Fluctuations.GlobalHaarMeanBound
import Fluctuations.GlobalHaarUnitBound

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]

/-- Uniform all-dimension form of the paper's Haar-mean estimate. The explicit
constant depends only on k. Small dimensions use the actual unitary norm bound;
large dimensions use the proved inverse-Gram expansion and coefficient bound. -/
theorem globalHaarOTOCMean_norm_le_all_dimensions
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k) :
    ‖globalHaarOTOCMean ρ B M k‖ ≤
      2 * ((2 * k).factorial : ℝ) ^ 3 / (Fintype.card N : ℝ) ^ 2 := by
  by_cases hlarge : 2 * ((2 * k).factorial : ℝ) ≤ Fintype.card N
  · exact globalHaarOTOCMean_norm_le ρ B M hρ hB hB2 hBtr hM hM2 hMtr k hk hlarge
  · apply (globalHaarOTOCMean_norm_le_one ρ B M hρ hB hB2 hM hM2 hMtr k).trans
    have hD : 0 < (Fintype.card N : ℝ) := by exact_mod_cast Fintype.card_pos
    have hfNat : 2 ≤ (2 * k).factorial := by
      simpa using Nat.factorial_le (show 2 ≤ 2 * k by omega)
    have hf : (2 : ℝ) ≤ (2 * k).factorial := by exact_mod_cast hfNat
    have hsmall : (Fintype.card N : ℝ) < 2 * ((2 * k).factorial : ℝ) := lt_of_not_ge hlarge
    apply (one_le_div (sq_pos_of_pos hD)).2
    calc
      (Fintype.card N : ℝ) ^ 2 ≤ (2 * ((2 * k).factorial : ℝ)) ^ 2 := by nlinarith
      _ = 4 * ((2 * k).factorial : ℝ) ^ 2 := by ring
      _ ≤ 2 * ((2 * k).factorial : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg ((2 * k).factorial : ℝ)) (sub_nonneg.mpr hf)]

/-- A single explicit dimension inequality suffices for the Haar quarter-bound. -/
theorem globalHaarOTOCMean_norm_le_quarter_all_dimensions
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k)
    (hDimension : 8 * ((2 * k).factorial : ℝ) ^ 3 ≤ (Fintype.card N : ℝ) ^ 2) :
    ‖globalHaarOTOCMean ρ B M k‖ ≤ 1 / 4 := by
  apply (globalHaarOTOCMean_norm_le_all_dimensions ρ B M hρ hB hB2 hBtr hM hM2 hMtr k hk).trans
  have hD : 0 < (Fintype.card N : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (sq_pos_of_pos hD)).2
  linarith

end Fluctuations
