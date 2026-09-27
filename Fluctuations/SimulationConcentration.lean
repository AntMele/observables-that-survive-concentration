import Fluctuations.SimulationAveraging
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Fluctuations

set_option linter.unusedSectionVars false

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two-sided concentration, with the actual probability measure. -/
theorem simulation_subgaussian_abs_tail (X : Ω → ℝ) (c : ℝ≥0)
    (hX : HasSubgaussianMGF X c μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {x | ε ≤ |X x|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {x | ε ≤ |X x|} = {x | ε ≤ X x} ∪ {x | ε ≤ -X x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {x | ε ≤ X x} + μ.real {x | ε ≤ -X x} := measureReal_union_le _ _
    _ ≤ _ := by
      have hn : μ.real {x | ε ≤ -X x} ≤ Real.exp (-ε ^ 2 / (2 * c)) :=
        hX.neg.measure_ge_le hε
      linarith [hX.measure_ge_le hε]

/-- The paper's Hoeffding exponent for the sample average of independent
bounded sign readouts; no concentration estimate is taken as a hypothesis. -/
theorem simulation_sample_average_tail (N : ℕ) (hN : 0 < N)
    (X : Fin N → Ω → ℝ) (hindep : iIndepFun X μ)
    (hm : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, X i x ∈ Set.Icc (-1) 1)
    (m : ℝ) (hmean : ∀ i, (∫ x, X i x ∂μ) = m)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {x | ε / 2 ≤ |(∑ i, X i x) / N - m|} ≤
      2 * Real.exp (-(N : ℝ) * ε ^ 2 / 8) := by
  let Z : Fin N → Ω → ℝ := fun i x => X i x - m
  have hZ : ∀ i, HasSubgaussianMGF (Z i) 1 μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    rw [hmean i] at h
    convert h using 1; norm_num
  have hi : iIndepFun Z μ := hindep.comp (fun (_ : Fin N) (y : ℝ) => y - m) (fun _ => measurable_id.sub_const m)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.univ) (c := fun _ => (1 : ℝ≥0)) (fun i _ => hZ i)
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := simulation_subgaussian_abs_tail (fun x => ∑ i, Z i x) N
    (by simpa using hsum) ((N : ℝ) * ε / 2) (by positivity)
  have he (x : Ω) : (∑ i, Z i x) = (N : ℝ) * ((∑ i, X i x) / N - m) := by
    simp only [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  simp_rw [he, abs_mul, abs_of_pos hp] at h
  have hset : {x | (N : ℝ) * ε / 2 ≤ (N : ℝ) * |(∑ i, X i x) / N - m|} =
      {x | ε / 2 ≤ |(∑ i, X i x) / N - m|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [mul_div_assoc, mul_le_mul_iff_right₀ hp]
  rw [hset] at h
  convert h using 1
  congr 2
  push_cast
  field_simp
  ring

/-- Markov's inequality at the half-error threshold. -/
theorem simulation_bias_tail (F H : Ω → ℝ)
    (hi : Integrable (fun x => |F x - H x|) μ) (ε : ℝ) (hε : 0 < ε) :
    μ.real {x | ε / 2 ≤ |F x - H x|} ≤
      (2 / ε) * ∫ x, |F x - H x| ∂μ := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => abs_nonneg (F x - H x)) hi (ε / 2)
  calc
    _ ≤ (∫ x, |F x - H x| ∂μ) / (ε / 2) :=
      (le_div_iff₀ (half_pos hε)).2 (by nlinarith [h])
    _ = _ := by ring

end Probability

end Fluctuations
