import Fluctuations.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Fluctuations

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

lemma weighted_norm_sq {η : ℝ} (hη : 0 < η) (x y : ℂ) :
    (η / (1 + η)) * ‖x‖ ^ 2 ≤ η * ‖y - x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 1 + η)).2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (η * (y.re - x.re) + y.re),
    sq_nonneg (η * (y.im - x.im) + y.im)]

lemma complexVariance_sub_const [IsProbabilityMeasure μ] {F : Ω → ℂ}
    (hF : MemLp F 2 μ) (c : ℂ) :
    complexVariance μ (fun ω => F ω - c) = complexVariance μ F := by
  rw [complexVariance_eq_re_add_im (hF.sub (memLp_const c)),
    complexVariance_eq_re_add_im hF]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [variance_sub_const hF.re.aestronglyMeasurable,
    variance_sub_const hF.im.aestronglyMeasurable]

/-- The mean minimizes the mean squared complex distance. -/
lemma complexVariance_le_sq_distance [IsProbabilityMeasure μ] {F : Ω → ℂ}
    (hF : MemLp F 2 μ) (c : ℂ) :
    complexVariance μ F ≤ ∫ ω, ‖F ω - c‖ ^ 2 ∂μ := by
  have hc : MemLp (fun ω => F ω - c) 2 μ := hF.sub (memLp_const c)
  have hv := complexVariance_eq_secondMoment_sub hc
  rw [complexVariance_sub_const hF c] at hv
  linarith [sq_nonneg ‖∫ ω, F ω - c ∂μ‖]

/-- The optimal weighted comparison needed to carry a variance lower bound forward. -/
theorem weighted_variance_comparison [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η)
    {F M : Ω → ℂ} (hF : MemLp F 2 μ) (hM : MemLp M 2 μ) :
    (η / (1 + η)) * complexVariance μ F ≤
      η * (∫ ω, ‖M ω - F ω‖ ^ 2 ∂μ) + complexVariance μ M := by
  let c : ℂ := ∫ ω, M ω ∂μ
  have hFc : MemLp (fun ω => F ω - c) 2 μ := hF.sub (memLp_const c)
  have hMc : MemLp (fun ω => M ω - c) 2 μ := hM.sub (memLp_const c)
  have hMF : MemLp (fun ω => M ω - F ω) 2 μ := hM.sub hF
  have hint := integral_mono
    ((hFc.integrable_norm_pow (by norm_num)).const_mul (η / (1 + η)))
    (((hMF.integrable_norm_pow (by norm_num)).const_mul η).add
      (hMc.integrable_norm_pow (by norm_num)))
    (fun ω => by
      have h := weighted_norm_sq hη (F ω - c) (M ω - c)
      simpa only [sub_sub_sub_cancel_right] using h)
  rw [integral_const_mul, integral_add
    ((hMF.integrable_norm_pow (by norm_num)).const_mul η)
    (hMc.integrable_norm_pow (by norm_num)), integral_const_mul] at hint
  exact (mul_le_mul_of_nonneg_left (complexVariance_le_sq_distance hF c)
    (by positivity : 0 ≤ η / (1 + η))).trans hint

/-- An integrated local reverse-variance inequality preserves a fixed fraction
of the earlier variance. -/
theorem forward_persistence [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {η : ℝ} (hη : 0 < η) {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hlocal : LocalReverseVariance μ m η F G) :
    (η / (1 + η)) * complexVariance μ F ≤ complexVariance μ G :=
  (weighted_variance_comparison hη hF hG.condExp).trans
    (localReverseVariance_integrated hm hF hG hlocal)

end Fluctuations
