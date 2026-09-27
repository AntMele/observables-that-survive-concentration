import Fluctuations.Probability

open MeasureTheory
open scoped ENNReal

namespace Fluctuations

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X}

/-- A continuous observable on a compact finite-measure space belongs to L². -/
lemma continuousMap_memLp_two [IsFiniteMeasure μ] (f : C(X, ℂ)) : MemLp f 2 μ :=
  (Lp.memLp (ContinuousMap.toLp 2 μ ℂ f)).ae_eq (ContinuousMap.coeFn_toLp μ f)

/-- The L² norm of the continuous-function embedding is the second moment. -/
lemma continuousMap_toLp_norm_sq [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp (𝕜 := ℂ) μ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [Complex.mul_conj, ← Complex.sq_norm] at h
  rw [integral_complex_ofReal] at h
  have hr := congrArg Complex.re h
  simpa only [← RCLike.ofReal_pow, ← RCLike.re_eq_complex_re, RCLike.ofReal_re] using hr

/-- Subtracting the mean, as a linear map on continuous observables. -/
noncomputable def centerContinuousMap [IsFiniteMeasure μ] : C(X, ℂ) →ₗ[ℂ] C(X, ℂ) where
  toFun f := f - ContinuousMap.const X (∫ x, f x ∂μ)
  map_add' f g := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.const_apply]
    rw [integral_add ((continuousMap_memLp_two f).integrable one_le_two)
      ((continuousMap_memLp_two g).integrable one_le_two)]
    ring
  map_smul' c f := by
    ext x
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [integral_const_mul]
    ring

/-- A finite-dimensional family of continuous observables under a full-support
probability law satisfies a common reverse-variance bound at any chosen point.
The constant is uniform over the whole family. Constants need not belong to it. -/
theorem finiteDimensional_reverseVariance (μ : Measure X) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (S : Submodule ℂ C(X, ℂ)) [FiniteDimensional ℂ S] (x₀ : X) :
    ∃ η : ℝ, 0 < η ∧ ∀ f : S,
      η * ‖(∫ x, (f : C(X, ℂ)) x ∂μ) - (f : C(X, ℂ)) x₀‖ ^ 2 ≤
        complexVariance μ (f : C(X, ℂ)) := by
  let A : S →ₗ[ℂ] C(X, ℂ) := (centerContinuousMap (μ := μ)).comp S.subtype
  let T : Submodule ℂ C(X, ℂ) := LinearMap.range A
  letI : FiniteDimensional ℂ T := A.finiteDimensional_range
  let J : T →ₗ[ℂ] Lp ℂ 2 μ :=
    (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp T.subtype
  have hJ : Function.Injective J := by
    intro f g h
    apply Subtype.ext
    exact ContinuousMap.toLp_injective μ h
  obtain ⟨K, hK, hbound⟩ := J.injective_iff_antilipschitz.mp hJ
  refine ⟨((K : ℝ) ^ 2)⁻¹, by positivity, ?_⟩
  intro f
  let g : T := ⟨A f, LinearMap.mem_range_self A f⟩
  have hnorm : ‖(g : C(X, ℂ))‖ ≤ (K : ℝ) * ‖J g‖ := by
    simpa only [dist_zero_right, map_zero] using hbound.le_mul_dist g 0
  have heval : ‖(g : C(X, ℂ)) x₀‖ ≤ (K : ℝ) * ‖J g‖ :=
    (ContinuousMap.norm_coe_le_norm _ _).trans hnorm
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (K : ℝ) * ‖J g‖)).2 heval
  have hLp : ‖J g‖ ^ 2 = complexVariance μ (f : C(X, ℂ)) := by
    change ‖ContinuousMap.toLp 2 μ ℂ (A f)‖ ^ 2 = _
    rw [continuousMap_toLp_norm_sq]
    rfl
  have heq : ‖(g : C(X, ℂ)) x₀‖ =
      ‖(∫ x, (f : C(X, ℂ)) x ∂μ) - (f : C(X, ℂ)) x₀‖ := by
    change ‖(f : C(X, ℂ)) x₀ - ∫ x, (f : C(X, ℂ)) x ∂μ‖ = _
    exact norm_sub_rev _ _
  rw [heq, mul_pow, hLp] at hsquare
  apply (inv_mul_le_iff₀ (by positivity : 0 < (K : ℝ) ^ 2)).2
  exact hsquare

end Fluctuations
