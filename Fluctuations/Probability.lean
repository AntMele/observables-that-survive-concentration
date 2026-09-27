import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Fluctuations

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The variance of a complex random variable, with squared complex modulus. -/
noncomputable def complexVariance (μ : Measure Ω) (F : Ω → ℂ) : ℝ :=
  ∫ ω, ‖F ω - ∫ ω, F ω ∂μ‖ ^ 2 ∂μ

lemma complexVariance_nonneg (F : Ω → ℂ) : 0 ≤ complexVariance μ F :=
  integral_nonneg fun _ => sq_nonneg _

lemma integral_norm_sq_re_im {F : Ω → ℂ} (hF : MemLp F 2 μ) :
    (∫ ω, ‖F ω‖ ^ 2 ∂μ) = (∫ ω, (F ω).re ^ 2 ∂μ) + ∫ ω, (F ω).im ^ 2 ∂μ := by
  have heq : (fun ω => ‖F ω‖ ^ 2) = (fun ω => (F ω).re ^ 2 + (F ω).im ^ 2) := by
    funext ω
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [heq]
  simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] using
    integral_add hF.re.integrable_sq hF.im.integrable_sq

lemma complexVariance_eq_re_add_im [IsProbabilityMeasure μ] {F : Ω → ℂ}
    (hF : MemLp F 2 μ) :
    complexVariance μ F = variance (fun ω => (F ω).re) μ +
      variance (fun ω => (F ω).im) μ := by
  have hc : MemLp (fun ω => F ω - ∫ ω, F ω ∂μ) 2 μ :=
    hF.sub (memLp_const _)
  have hFre : MemLp (fun ω => (F ω).re) 2 μ := hF.re
  have hFim : MemLp (fun ω => (F ω).im) 2 μ := hF.im
  have ire : (∫ ω, (F ω).re ∂μ) = (∫ ω, F ω ∂μ).re := integral_re (hF.integrable one_le_two)
  have iim : (∫ ω, (F ω).im ∂μ) = (∫ ω, F ω ∂μ).im := integral_im (hF.integrable one_le_two)
  rw [complexVariance, integral_norm_sq_re_im hc,
    variance_eq_integral hFre.aemeasurable, variance_eq_integral hFim.aemeasurable,
    ire, iim]
  rfl

lemma clm_condExp [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {F : Ω → ℂ} (hF : Integrable F μ) (L : ℂ →L[ℝ] ℝ) :
    (fun ω => L ((μ[F | m]) ω)) =ᵐ[μ] μ[fun ω => L (F ω) | m] := by
  letI : MeasurableSpace Ω := m₀
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (L.integrable_comp hF)
  · intro s _ _
    exact (L.integrable_comp integrable_condExp).integrableOn
  · intro s hs _
    rw [L.integral_comp_comm integrable_condExp.integrableOn,
      L.integral_comp_comm hF.integrableOn, setIntegral_condExp hm hF hs]
  · exact L.continuous.comp_aestronglyMeasurable (m := m) (m₀ := m₀)
      (stronglyMeasurable_condExp (m := m) (μ := μ) (f := F)).aestronglyMeasurable

/-- Law of total variance for complex random variables. -/
lemma complex_total_variance [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {G : Ω → ℂ} (hG : MemLp G 2 μ) :
    (∫ ω, ‖G ω - (μ[G | m]) ω‖ ^ 2 ∂μ) +
      complexVariance μ (μ[G | m]) = complexVariance μ G := by
  have hr := clm_condExp hm (hG.integrable one_le_two) Complex.reCLM
  have hi := clm_condExp hm (hG.integrable one_le_two) Complex.imCLM
  simp only [Complex.reCLM_apply] at hr
  simp only [Complex.imCLM_apply] at hi
  have hGre : MemLp (fun ω => (G ω).re) 2 μ := hG.re
  have hGim : MemLp (fun ω => (G ω).im) 2 μ := hG.im
  have vr := integral_condVar_add_variance_condExp hm hGre
  have vi := integral_condVar_add_variance_condExp hm hGim
  have hc : MemLp (fun ω => G ω - (μ[G | m]) ω) 2 μ := hG.sub hG.condExp
  rw [condVar, integral_condExp hm] at vr vi
  rw [complexVariance_eq_re_add_im hG.condExp, complexVariance_eq_re_add_im hG,
    integral_norm_sq_re_im hc]
  have er : (∫ ω, ((G ω - (μ[G | m]) ω).re) ^ 2 ∂μ) =
      ∫ ω, ((G ω).re - (μ[fun ω => (G ω).re | m]) ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hr] with ω hω
    simp only [Complex.sub_re]
    rw [show ((μ[G | m]) ω).re = _ from hω]
  have ei : (∫ ω, ((G ω - (μ[G | m]) ω).im) ^ 2 ∂μ) =
      ∫ ω, ((G ω).im - (μ[fun ω => (G ω).im | m]) ω) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hi] with ω hω
    simp only [Complex.sub_im]
    rw [show ((μ[G | m]) ω).im = _ from hω]
  rw [er, ei, variance_congr hr, variance_congr hi]
  change _ + (_ + _) = _ + _
  dsimp only [Pi.pow_apply, Pi.sub_apply] at vr vi
  linarith

lemma complexVariance_eq_secondMoment_sub [IsProbabilityMeasure μ] {F : Ω → ℂ}
    (hF : MemLp F 2 μ) :
    complexVariance μ F = (∫ ω, ‖F ω‖ ^ 2 ∂μ) - ‖∫ ω, F ω ∂μ‖ ^ 2 := by
  have hFre : MemLp (fun ω => (F ω).re) 2 μ := hF.re
  have hFim : MemLp (fun ω => (F ω).im) 2 μ := hF.im
  have ire : (∫ ω, (F ω).re ∂μ) = (∫ ω, F ω ∂μ).re := integral_re (hF.integrable one_le_two)
  have iim : (∫ ω, (F ω).im ∂μ) = (∫ ω, F ω ∂μ).im := integral_im (hF.integrable one_le_two)
  rw [complexVariance_eq_re_add_im hF, variance_eq_sub hFre, variance_eq_sub hFim,
    integral_norm_sq_re_im hF, ire, iim, Complex.sq_norm, Complex.normSq_apply]
  change _ + _ = _ - _
  simp only [Pi.pow_apply]
  ring

lemma norm_mean_sq_le_secondMoment [IsProbabilityMeasure μ] {F : Ω → ℂ}
    (hF : MemLp F 2 μ) : ‖∫ ω, F ω ∂μ‖ ^ 2 ≤ ∫ ω, ‖F ω‖ ^ 2 ∂μ := by
  have h := complexVariance_nonneg (μ := μ) F
  rw [complexVariance_eq_secondMoment_sub hF] at h
  linarith

/-- The local reverse-variance hypothesis, imposed almost everywhere. -/
def LocalReverseVariance (μ : Measure Ω) (m : MeasurableSpace Ω)
    (η : ℝ) (F G : Ω → ℂ) : Prop :=
  ∀ᵐ ω ∂μ, η * ‖(μ[G | m]) ω - F ω‖ ^ 2 ≤
    (μ[fun ω => ‖G ω - (μ[G | m]) ω‖ ^ 2 | m]) ω

/-- Integrating the local assumption and using total variance. -/
lemma localReverseVariance_integrated [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {η : ℝ} {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hlocal : LocalReverseVariance μ m η F G) :
    η * (∫ ω, ‖(μ[G | m]) ω - F ω‖ ^ 2 ∂μ) +
      complexVariance μ (μ[G | m]) ≤ complexVariance μ G := by
  letI : MeasurableSpace Ω := m₀
  have hd : MemLp (fun ω => (μ[G | m]) ω - F ω) 2 μ := hG.condExp.sub hF
  have hb := integral_mono_ae ((hd.integrable_norm_pow (by norm_num)).const_mul η)
    integrable_condExp hlocal
  rw [integral_const_mul, integral_condExp hm] at hb
  have ht := complex_total_variance hm hG
  linarith

/-- A change in the mean forces variance at the end of the interval. -/
theorem slope_to_variance [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {η : ℝ} (hη : 0 ≤ η) {F G : Ω → ℂ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hlocal : LocalReverseVariance μ m η F G) :
    η * ‖(∫ ω, G ω ∂μ) - ∫ ω, F ω ∂μ‖ ^ 2 ≤ complexVariance μ G := by
  letI : MeasurableSpace Ω := m₀
  have hd : MemLp (fun ω => (μ[G | m]) ω - F ω) 2 μ := hG.condExp.sub hF
  have hj := norm_mean_sq_le_secondMoment hd
  rw [integral_sub integrable_condExp (hF.integrable one_le_two), integral_condExp hm] at hj
  have hb := localReverseVariance_integrated hm hF hG hlocal
  have hn := complexVariance_nonneg (μ := μ) (μ[G | m])
  exact (mul_le_mul_of_nonneg_left hj hη).trans (by linarith)

end Fluctuations
