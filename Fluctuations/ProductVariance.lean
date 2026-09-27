import Fluctuations.WeightedVariance

open MeasureTheory Filter
open scoped ENNReal

namespace Fluctuations

lemma complexVariance_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → ℂ) :
    complexVariance (μ.prod ν) (fun p => g p.1) = complexVariance μ g := by
  unfold complexVariance
  rw [integral_fun_fst g, measureReal_univ_eq_one, one_smul]
  simpa using (integral_fun_fst (μ := μ) (ν := ν)
    (fun x => ‖g x - ∫ x, g x ∂μ‖ ^ 2))

section Product

variable {X Y E : Type*}
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [mX : MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [mY : MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit mX [BorelSpace X] [CompleteSpace E] in
/-- Averaging a continuous function over an independent compact factor. -/
lemma continuous_product_average (f : X × Y → E) (hf : Continuous f) :
    Continuous (fun x => ∫ y, f (x, y) ∂ν) := by
  simpa using (continuous_parametric_integral_of_continuous
    (μ := ν) (f := fun x y => f (x, y)) hf isCompact_univ)

/-- On a product probability space, conditioning on the first factor integrates
out the independent second factor. -/
lemma product_condExp (f : X × Y → E) (hf : Continuous f) :
    (fun p : X × Y => ∫ y, f (p.1, y) ∂ν) =ᵐ[μ.prod ν]
      (μ.prod ν)[f | (inferInstance : MeasurableSpace X).comap Prod.fst] := by
  have hm : mX.comap (Prod.fst : X × Y → X) ≤ mX.prod mY :=
    measurable_iff_comap_le.mp measurable_fst
  have hc := continuous_product_average (ν := ν) f hf
  have hi : Integrable f (μ.prod ν) := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun p : X × Y => ∫ y, f (p.1, y) ∂ν) (μ.prod ν) :=
    (hc.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hi
  · intro s _ _
    exact hg.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have heq : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set Y) := by ext p; simp
    rw [heq, setIntegral_prod _ hg.integrableOn, setIntegral_prod _ hi.integrableOn]
    simp
  · exact (hc.stronglyMeasurable.comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable

end Product

section LocalProduct

variable {X Y : Type*}
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [mX : MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [mY : MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A bound for every fixed earlier circuit implies the conditional
reverse-variance bound on the independent product experiment. -/
theorem product_localReverseVariance (f : X × Y → ℂ) (hf : Continuous f)
    (y₀ : Y) (η : ℝ)
    (hlocal : ∀ x, η * ‖(∫ y, f (x, y) ∂ν) - f (x, y₀)‖ ^ 2 ≤
      complexVariance ν (fun y => f (x, y))) :
    LocalReverseVariance (μ.prod ν) (mX.comap Prod.fst) η
      (fun p => f (p.1, y₀)) f := by
  let avg : X → ℂ := fun x => ∫ y, f (x, y) ∂ν
  have havg := continuous_product_average (ν := ν) f hf
  have he := product_condExp (μ := μ) (ν := ν) f hf
  have hc : Continuous (fun p : X × Y => ‖f p - avg p.1‖ ^ 2) := by
    exact (hf.sub (havg.comp continuous_fst)).norm.pow 2
  have hv := product_condExp (μ := μ) (ν := ν) _ hc
  have heq : (fun p : X × Y => ‖f p - avg p.1‖ ^ 2) =ᵐ[μ.prod ν]
      (fun p => ‖f p - ((μ.prod ν)[f | mX.comap Prod.fst]) p‖ ^ 2) := by
    filter_upwards [he] with p hp
    rw [← hp]
  have hce := condExp_congr_ae (m := mX.comap Prod.fst) heq
  unfold LocalReverseVariance
  filter_upwards [he, hv, hce] with p hp hvp hcp
  rw [← hp, ← hcp, ← hvp]
  exact hlocal p.1

/-- Slope and persistence for an independent local gate experiment. The old
observable is obtained by replacing the new gate by the identity `y₀`. -/
theorem product_step_bounds (f : X × Y → ℂ) (hf : Continuous f)
    (y₀ : Y) {η : ℝ} (hη : 0 < η)
    (hlocal : ∀ x, η * ‖(∫ y, f (x, y) ∂ν) - f (x, y₀)‖ ^ 2 ≤
      complexVariance ν (fun y => f (x, y))) :
    (η * ‖(∫ p, f p ∂μ.prod ν) - ∫ x, f (x, y₀) ∂μ‖ ^ 2 ≤
      complexVariance (μ.prod ν) f) ∧
    ((η / (1 + η)) * complexVariance μ (fun x => f (x, y₀)) ≤
      complexVariance (μ.prod ν) f) := by
  have hm : mX.comap (Prod.fst : X × Y → X) ≤ mX.prod mY :=
    measurable_iff_comap_le.mp measurable_fst
  have hF : MemLp (fun p : X × Y => f (p.1, y₀)) 2 (μ.prod ν) :=
    (hf.comp (continuous_fst.prodMk continuous_const)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG : MemLp f 2 (μ.prod ν) :=
    hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl := product_localReverseVariance (μ := μ) f hf y₀ η hlocal
  have hmean : (∫ p : X × Y, f (p.1, y₀) ∂μ.prod ν) = ∫ x, f (x, y₀) ∂μ := by
    simpa using integral_fun_fst (μ := μ) (ν := ν) (fun x => f (x, y₀))
  have hvar := complexVariance_fst (μ := μ) (ν := ν) (fun x => f (x, y₀))
  constructor
  · simpa only [hmean] using
      slope_to_variance hm hη.le hF hG hl
  · simpa only [hvar] using forward_persistence hm hη hF hG hl

end LocalProduct

end Fluctuations
