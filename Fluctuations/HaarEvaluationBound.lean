import Fluctuations.FiniteDimensionalVariance

open MeasureTheory
open scoped BigOperators ENNReal

namespace Fluctuations

section Evaluation

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]

omit [IsTopologicalGroup G] [Measure.IsMulLeftInvariant μ] in
/-- The evaluation kernel of a finite-dimensional translation-invariant
Hilbert space of continuous functions has constant diagonal equal to its dimension. -/
theorem haar_evaluation_bound_of_translation
    (J : E →ₗ[ℂ] C(G, ℂ))
    (hnorm : ∀ f, ‖f‖ ^ 2 = ∫ x, ‖J f x‖ ^ 2 ∂μ)
    (htrans : ∀ a f, ∃ g : E, ‖g‖ = ‖f‖ ∧ ∀ x, J g x = J f (a * x))
    (f : E) (x : G) :
    ‖J f x‖ ^ 2 ≤ (Module.finrank ℂ E : ℝ) * ∫ y, ‖J f y‖ ^ 2 ∂μ := by
  let ev (a : G) : E →L[ℂ] ℂ :=
    (((ContinuousMap.evalCLM ℂ a).toLinearMap.comp J).toContinuousLinearMap)
  have hev (a : G) (v : E) : ev a v = J v a := rfl
  have hle (a b : G) : ‖ev (a * b)‖ ≤ ‖ev b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    obtain ⟨w, hw, heq⟩ := htrans a v
    rw [hev, ← heq, ← hev, ← hw]
    exact (ev b).le_opNorm w
  have heq (a : G) : ‖ev a‖ = ‖ev 1‖ := by
    apply le_antisymm
    · simpa using hle a 1
    · simpa using hle a⁻¹ a
  let b := stdOrthonormalBasis ℂ E
  have hsum (a : G) : ∑ i, ‖J (b i) a‖ ^ 2 = ‖ev 1‖ ^ 2 := by
    let v := (InnerProductSpace.toDual ℂ E).symm (ev a)
    have hv : ∀ i, inner ℂ v (b i) = J (b i) a := by
      intro i
      exact InnerProductSpace.toDual_symm_apply
    calc
      ∑ i, ‖J (b i) a‖ ^ 2 = ∑ i, ‖inner ℂ v (b i)‖ ^ 2 := by simp_rw [hv]
      _ = ‖v‖ ^ 2 := b.sum_sq_norm_inner_left v
      _ = ‖ev a‖ ^ 2 := by rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
      _ = ‖ev 1‖ ^ 2 := by rw [heq]
  have hdim : ‖ev 1‖ ^ 2 = (Module.finrank ℂ E : ℝ) := by
    calc
      ‖ev 1‖ ^ 2 = ∫ a, ∑ i, ‖J (b i) a‖ ^ 2 ∂μ := by simp_rw [hsum]; simp
      _ = ∑ i, ∫ a, ‖J (b i) a‖ ^ 2 ∂μ := by
        apply integral_finset_sum
        intro i _
        exact (((J (b i)).continuous.norm.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      _ = ∑ i : Fin (Module.finrank ℂ E), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hnorm, b.orthonormal.norm_eq_one i]
        norm_num
      _ = _ := by simp
  have hh := (sq_le_sq₀ (norm_nonneg (ev x f))
    (mul_nonneg (norm_nonneg (ev x)) (norm_nonneg f))).2 ((ev x).le_opNorm f)
  simpa only [hev, mul_pow, heq, hdim, hnorm] using hh

end Evaluation

section Subspace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
  [μ.IsOpenPosMeasure]

/-- Left translation on continuous functions. -/
def leftTranslate (a : G) : C(G, ℂ) →ₐ[ℂ] C(G, ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ ⟨fun x => a * x, continuous_const.mul continuous_id⟩

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
@[simp] lemma leftTranslate_apply (a : G) (f : C(G, ℂ)) (x : G) :
    leftTranslate a f x = f (a * x) := rfl

/-- Point evaluation is bounded by the dimension for any finite-dimensional
left-translation-invariant space under normalized Haar measure. -/
theorem haar_subspace_evaluation_bound
    (S : Submodule ℂ C(G, ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ a f, f ∈ S → leftTranslate a f ∈ S)
    (f : C(G, ℂ)) (hf : f ∈ S) (x : G) :
    ‖f x‖ ^ 2 ≤ (Module.finrank ℂ S : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂μ := by
  let A : S →ₗ[ℂ] Lp ℂ 2 μ :=
    (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp S.subtype
  have hA : Function.Injective A := by
    intro f g h
    apply Subtype.ext
    exact ContinuousMap.toLp_injective μ h
  let T := LinearMap.range A
  letI : FiniteDimensional ℂ T := A.finiteDimensional_range
  let e : S ≃ₗ[ℂ] T := LinearEquiv.ofInjective A hA
  let J : T →ₗ[ℂ] C(G, ℂ) := S.subtype.comp e.symm.toLinearMap
  have hAJ (v : T) : ContinuousMap.toLp 2 μ ℂ (J v) = (v : Lp ℂ 2 μ) := by
    exact congrArg Subtype.val (e.apply_symm_apply v)
  have hnorm (v : T) : ‖v‖ ^ 2 = ∫ y, ‖J v y‖ ^ 2 ∂μ := by
    rw [← continuousMap_toLp_norm_sq, hAJ]
    rfl
  have htrans (a : G) (v : T) :
      ∃ w : T, ‖w‖ = ‖v‖ ∧ ∀ y, J w y = J v (a * y) := by
    let u : S := ⟨leftTranslate a (J v), hS a (J v) (e.symm v).prop⟩
    refine ⟨e u, ?_, ?_⟩
    · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [hnorm, hnorm]
      change (∫ y, ‖(e.symm (e u) : C(G, ℂ)) y‖ ^ 2 ∂μ) = _
      rw [e.symm_apply_apply]
      exact integral_mul_left_eq_self (fun y => ‖J v y‖ ^ 2) a
    · intro y
      change (e.symm (e u) : C(G, ℂ)) y = _
      rw [e.symm_apply_apply]
      rfl
  have hh := haar_evaluation_bound_of_translation μ J hnorm htrans (e ⟨f, hf⟩) x
  have hJ : J (e ⟨f, hf⟩) = f := by
    change (e.symm (e ⟨f, hf⟩) : C(G, ℂ)) = f
    rw [e.symm_apply_apply]
  rw [hJ, ← e.finrank_eq] at hh
  exact hh

omit [μ.IsOpenPosMeasure] in
/-- Centering commutes with Haar translation. -/
lemma centerContinuousMap_leftTranslate (a : G) (f : C(G, ℂ)) :
    centerContinuousMap (μ := μ) (leftTranslate a f) =
      leftTranslate a (centerContinuousMap (μ := μ) f) := by
  ext x
  change f (a * x) - (∫ y, f (a * y) ∂μ) = f (a * x) - (∫ y, f y ∂μ)
  rw [integral_mul_left_eq_self]

/-- Finite-dimensional translation invariance gives a dimension-explicit
reverse variance inequality. Constants need not be present in the original space. -/
theorem haar_subspace_reverseVariance
    (S : Submodule ℂ C(G, ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ a f, f ∈ S → leftTranslate a f ∈ S)
    (f : C(G, ℂ)) (hf : f ∈ S) (x : G) :
    ‖(∫ y, f y ∂μ) - f x‖ ^ 2 ≤
      (Module.finrank ℂ S : ℝ) * complexVariance μ f := by
  let A := (centerContinuousMap (μ := μ)).comp S.subtype
  let T := LinearMap.range A
  letI : FiniteDimensional ℂ T := A.finiteDimensional_range
  have hT : ∀ a g, g ∈ T → leftTranslate a g ∈ T := by
    intro a g hg
    obtain ⟨v, rfl⟩ := hg
    refine ⟨⟨leftTranslate a v.val, hS a v.val v.prop⟩, ?_⟩
    exact centerContinuousMap_leftTranslate μ a v.val
  have hh := haar_subspace_evaluation_bound μ T hT
    (A ⟨f, hf⟩) (LinearMap.mem_range_self A ⟨f, hf⟩) x
  have heval : ‖A ⟨f, hf⟩ x‖ = ‖(∫ y, f y ∂μ) - f x‖ := norm_sub_rev _ _
  rw [heval] at hh
  have hdim : Module.finrank ℂ T ≤ Module.finrank ℂ S :=
    LinearMap.finrank_range_le A
  have hvar : 0 ≤ complexVariance μ f := integral_nonneg fun _ => sq_nonneg _
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hdim) hvar)

end Subspace

end Fluctuations
