import Fluctuations.ProductVariance

/-! Single-coordinate conditional means on genuine independent product experiments. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Fluctuations

section ConditionalProjection

variable {Ω ι : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Conditional expectation is an orthogonal projection, expressed through real covariance. -/
lemma covariance_condExp_eq_variance {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    covariance X (μ[X | m]) μ = variance (μ[X | m]) μ := by
  have hi := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_condExp (m := m) (μ := μ) (f := X))
    (hX.condExp.integrable_mul hX) (hX.integrable one_le_two)
  have heq : (∫ ω, (X * μ[X | m]) ω ∂μ) =
      ∫ ω, ((μ[X | m]) ω) ^ 2 ∂μ := by
    calc
      _ = ∫ ω, ((μ[X | m]) * X) ω ∂μ := by simp only [mul_comm]
      _ = ∫ ω, μ[(μ[X | m]) * X | m] ω ∂μ := (integral_condExp hm).symm
      _ = _ := integral_congr_ae (hi.mono fun ω hω => by simpa [pow_two] using hω)
  rw [covariance_eq_sub hX hX.condExp, variance_eq_sub hX.condExp, heq,
    integral_condExp hm]
  simp only [pow_two, Pi.mul_apply]

/-- Independent sigma-algebras give an additive lower bound from all their
single-coordinate projections. Independence is derived from the product law below. -/
theorem sum_variance_condExp_le (s : Finset ι) (m : ι → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ m₀) (hind : Pairwise (fun i j => Indep (m i) (m j) μ))
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∑ i ∈ s, variance (μ[X | m i]) μ) ≤ variance X μ := by
  classical
  let Y : ι → Ω → ℝ := fun i => μ[X | m i]
  have hY (i : ι) : MemLp (Y i) 2 μ := hX.condExp
  have hsum : MemLp (∑ i ∈ s, Y i) 2 μ := memLp_finset_sum' s (fun i _ => hY i)
  have hi : Set.Pairwise (↑s) (fun i j => IndepFun (Y i) (Y j) μ) := by
    intro i _ j _ hij
    rw [IndepFun_iff_Indep]
    apply indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (hind hij)
        (stronglyMeasurable_condExp.measurable.comap_le))
    exact stronglyMeasurable_condExp.measurable.comap_le
  have hv : variance (∑ i ∈ s, Y i) μ = ∑ i ∈ s, variance (Y i) μ :=
    IndepFun.variance_sum (fun i _ => hY i) hi
  have hc : covariance X (∑ i ∈ s, Y i) μ = ∑ i ∈ s, variance (Y i) μ := by
    rw [covariance_sum_right' (fun i _ => hY i) hX]
    exact Finset.sum_congr rfl fun i _ => covariance_condExp_eq_variance (hm i) hX
  have hn := variance_nonneg (X - ∑ i ∈ s, Y i) μ
  rw [variance_sub hX hsum, hv, hc] at hn
  exact by linarith

/-- The same projection lower bound for squared complex modulus variance. -/
theorem sum_complexVariance_condExp_le (s : Finset ι) (m : ι → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ m₀) (hind : Pairwise (fun i j => Indep (m i) (m j) μ))
    {X : Ω → ℂ} (hX : MemLp X 2 μ) :
    (∑ i ∈ s, complexVariance μ (μ[X | m i])) ≤ complexVariance μ X := by
  have hr := sum_variance_condExp_le s m hm hind hX.re
  have hi := sum_variance_condExp_le s m hm hind hX.im
  have hdecomp (i : ι) : complexVariance μ (μ[X | m i]) =
      variance (μ[fun ω => (X ω).re | m i]) μ +
      variance (μ[fun ω => (X ω).im | m i]) μ := by
    rw [complexVariance_eq_re_add_im hX.condExp]
    have hre := clm_condExp (hm i) (hX.integrable one_le_two) Complex.reCLM
    have him := clm_condExp (hm i) (hX.integrable one_le_two) Complex.imCLM
    simp only [Complex.reCLM_apply] at hre
    simp only [Complex.imCLM_apply] at him
    rw [variance_congr hre, variance_congr him]
  simp_rw [hdecomp]
  rw [Finset.sum_add_distrib, complexVariance_eq_re_add_im hX]
  exact add_le_add hr hi

end ConditionalProjection

section ProductCoordinates

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [mE : ∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The information carried by one physical gate in the product experiment. -/
def coordinateMeasurableSpace (i : ι) : MeasurableSpace (∀ j, E j) :=
  (mE i).comap (Function.eval i)

omit [Fintype ι] in
lemma coordinateMeasurableSpace_le (i : ι) :
    coordinateMeasurableSpace (E := E) i ≤ (inferInstance : MeasurableSpace (∀ j, E j)) :=
  (measurable_pi_apply i).comap_le

/-- The variance of a complex function bounds the sum of its single-gate
conditional variances. The measure is the actual independent product law;
no orthogonality or conditional-correlation premise is supplied. -/
theorem pi_sum_complexVariance_condExp_le (s : Finset ι)
    {X : (∀ i, E i) → ℂ} (hX : MemLp X 2 (Measure.pi μ)) :
    (∑ i ∈ s, complexVariance (Measure.pi μ)
      ((Measure.pi μ)[X | coordinateMeasurableSpace i])) ≤
      complexVariance (Measure.pi μ) X := by
  apply sum_complexVariance_condExp_le s _ coordinateMeasurableSpace_le _ hX
  intro i j hij
  have hcoords : iIndepFun (fun i (x : ∀ i, E i) => x i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  exact (IndepFun_iff_Indep _ _ _).mp (hcoords.indepFun hij)

end ProductCoordinates

section AffineVariance

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
lemma complexVariance_congr_ae {X Y : Ω → ℂ} (h : X =ᵐ[ν] Y) :
    complexVariance ν X = complexVariance ν Y := by
  unfold complexVariance
  rw [integral_congr_ae h]
  exact integral_congr_ae (h.mono fun ω hω => by dsimp only; rw [hω])

/-- The exact variance transformation for a complex affine function. -/
lemma complexVariance_affine {A : Ω → ℂ} (hA : MemLp A 2 ν) (c a b : ℂ) :
    complexVariance ν (fun g => c + a * (A g - b)) = ‖a‖ ^ 2 * complexVariance ν A := by
  have hAi := hA.integrable one_le_two
  have hm : (∫ g, c + a * (A g - b) ∂ν) = c + a * ((∫ g, A g ∂ν) - b) := by
    calc
      _ = (∫ g : Ω, c ∂ν) + ∫ g, a * (A g - b) ∂ν :=
        integral_add (integrable_const c) ((hAi.sub (integrable_const b)).const_mul a)
      _ = c + a * ((∫ g, A g ∂ν) - b) := by
        rw [integral_const_mul]
        have hsub : (∫ g, A g - b ∂ν) = (∫ g, A g ∂ν) - ∫ _g : Ω, b ∂ν :=
          integral_sub hAi (integrable_const b)
        rw [hsub]
        simp
  unfold complexVariance
  rw [hm]
  have heq (g : Ω) : c + a * (A g - b) - (c + a * ((∫ x, A x ∂ν) - b)) =
      a * (A g - ∫ x, A x ∂ν) := by ring
  simp_rw [heq, norm_mul, mul_pow]
  exact integral_const_mul _ _

lemma complexVariance_ofReal {A : Ω → ℝ} (hA : MemLp A 2 ν) :
    complexVariance ν (fun g => (A g : ℂ)) = variance A ν := by
  have hAc : MemLp (fun g => (A g : ℂ)) 2 ν := hA.ofReal
  rw [complexVariance_eq_re_add_im hAc]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  change variance A ν + variance (0 : Ω → ℝ) ν = variance A ν
  rw [variance_zero, add_zero]

/-- The manuscript's exact affine single-gate coefficient. Neither the mean of
`A` nor a variance value for `A` is assumed in this identity. -/
theorem gate_affine_variance {A : Ω → ℝ} (hA : MemLp A 2 ν)
    (c : ℂ) (P F : ℝ) :
    complexVariance ν (fun g => c - (16 / 15 : ℂ) * (P : ℂ) * (F : ℂ) *
      ((A g : ℂ) - 4 / 5)) =
      (256 / 225 : ℝ) * (P * F) ^ 2 * variance A ν := by
  have heq (g : Ω) : c - (16 / 15 : ℂ) * (P : ℂ) * (F : ℂ) * ((A g : ℂ) - 4 / 5) =
      c + (((-16 / 15 : ℝ) * P * F : ℝ) : ℂ) * ((A g : ℂ) - 4 / 5) := by
    push_cast
    ring
  simp_rw [heq]
  have hAc : MemLp (fun g => (A g : ℂ)) 2 ν := hA.ofReal
  rw [complexVariance_affine hAc, complexVariance_ofReal hA]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end AffineVariance

section ProductInfluences

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, MeasurableSpace (E i)]
  (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

lemma complexVariance_comp_eval (i : ι) {f : E i → ℂ} (hf : MemLp f 2 (μ i)) :
    complexVariance (Measure.pi μ) (fun x => f (x i)) = complexVariance (μ i) f := by
  unfold complexVariance
  rw [integral_comp_eval hf.aestronglyMeasurable]
  exact integral_comp_eval ((hf.sub (memLp_const _)).aestronglyMeasurable.norm.pow 2)

/-- Accumulate genuine one-coordinate conditional influences. -/
theorem pi_variance_ge_sum_gate_influences (s : Finset ι)
    {X : (∀ i, E i) → ℂ} (hX : MemLp X 2 (Measure.pi μ))
    (A : ∀ i, E i → ℝ) (hA : ∀ i, MemLp (A i) 2 (μ i))
    (c : ι → ℂ) (P F : ι → ℝ)
    (hconditional : ∀ i ∈ s, (Measure.pi μ)[X | coordinateMeasurableSpace i] =ᵐ[Measure.pi μ]
      fun x => c i - (16 / 15 : ℂ) * (P i : ℂ) * (F i : ℂ) * ((A i (x i) : ℂ) - 4 / 5)) :
    (∑ i ∈ s, (256 / 225 : ℝ) * (P i * F i) ^ 2 * variance (A i) (μ i)) ≤
      complexVariance (Measure.pi μ) X := by
  have hbound := pi_sum_complexVariance_condExp_le μ s hX
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [complexVariance_congr_ae (hconditional i hi)]
  have hAc : MemLp (fun g => (A i g : ℂ)) 2 (μ i) := (hA i).ofReal
  have hfun : MemLp (fun g => c i - (16 / 15 : ℂ) * (P i : ℂ) * (F i : ℂ) *
      ((A i g : ℂ) - 4 / 5)) 2 (μ i) :=
    (memLp_const (c i)).sub ((hAc.sub (memLp_const (4 / 5))).const_mul _)
  exact (gate_affine_variance (hA i) (c i) (P i) (F i)).symm.trans
    (complexVariance_comp_eval μ i hfun).symm

/-- Counting gates and a uniform one-gate lower bound give a full variance bound. -/
theorem pi_variance_ge_card_mul (s : Finset ι)
    {X : (∀ i, E i) → ℂ} (hX : MemLp X 2 (Measure.pi μ)) (v : ℝ)
    (hinfluence : ∀ i ∈ s, v ≤ complexVariance (Measure.pi μ)
      ((Measure.pi μ)[X | coordinateMeasurableSpace i])) :
    (s.card : ℝ) * v ≤ complexVariance (Measure.pi μ) X := by
  calc
    (s.card : ℝ) * v = ∑ _i ∈ s, v := by simp
    _ ≤ ∑ i ∈ s, complexVariance (Measure.pi μ)
        ((Measure.pi μ)[X | coordinateMeasurableSpace i]) := Finset.sum_le_sum hinfluence
    _ ≤ _ := pi_sum_complexVariance_condExp_le μ s hX

/-- The finite numerical accumulation behind the front-window exponent:
`a*n*sqrt(n)` coordinates, each contributing at least `b/n²`, give
`a*b/sqrt(n)`. This theorem alone does not claim the required physical
conditional-mean or propagation estimates. -/
theorem pi_variance_ge_inv_sqrt (s : Finset ι)
    {X : (∀ i, E i) → ℂ} (hX : MemLp X 2 (Measure.pi μ))
    (n a b : ℝ) (hn : 0 < n) (hb : 0 ≤ b)
    (hcard : a * n * Real.sqrt n ≤ (s.card : ℝ))
    (hinfluence : ∀ i ∈ s, b / n ^ 2 ≤ complexVariance (Measure.pi μ)
      ((Measure.pi μ)[X | coordinateMeasurableSpace i])) :
    a * b / Real.sqrt n ≤ complexVariance (Measure.pi μ) X := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  calc
    a * b / Real.sqrt n = (a * n * Real.sqrt n) * (b / n ^ 2) := by
      field_simp
      rw [hsq]
    _ ≤ (s.card : ℝ) * (b / n ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hb (sq_nonneg n))
    _ ≤ _ := pi_variance_ge_card_mul μ s hX _ hinfluence

end ProductInfluences

end Fluctuations
