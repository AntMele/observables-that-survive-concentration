import Fluctuations.GateInfluence

/-! Integrating all other gates is the genuine one-coordinate conditional mean. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Fluctuations

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
  [mE : ∀ i, MeasurableSpace (E i)]

/-- Split a coordinate from the actual product space. -/
def coordinateSplit (i : ι) : (∀ j, E j) ≃ᵐ E i × (∀ j : {j // j ≠ i}, E j) where
  toEquiv := Equiv.piSplitAt i E
  measurable_toFun := (measurable_pi_apply i).prodMk
    (measurable_pi_iff.2 fun j => measurable_pi_apply j.val)
  measurable_invFun := by
    apply measurable_pi_iff.2
    intro j
    by_cases hj : j = i
    · subst j
      simpa [Equiv.piSplitAt] using measurable_fst
    · simpa [Equiv.piSplitAt, hj] using (measurable_pi_apply (⟨j, hj⟩ : {j // j ≠ i})).comp measurable_snd

omit [Fintype ι] in
@[simp] lemma coordinateSplit_fst (i : ι) (x : ∀ j, E j) :
    (coordinateSplit i x).1 = x i := rfl

omit [Fintype ι] in
@[simp] lemma coordinateSplit_symm_apply_self (i : ι) (a : E i)
    (y : ∀ j : {j // j ≠ i}, E j) : (coordinateSplit i).symm (a, y) i = a := by
  simp [coordinateSplit, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] lemma coordinateSplit_symm_apply_ne (i : ι) (a : E i)
    (y : ∀ j : {j // j ≠ i}, E j) {j : ι} (hj : j ≠ i) :
    (coordinateSplit i).symm (a, y) j = y ⟨j, hj⟩ := by
  simp [coordinateSplit, Equiv.piSplitAt, hj]

variable (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem coordinateSplit_measurePreserving (i : ι) :
    MeasurePreserving (coordinateSplit (E := E) i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) := by
  let e := coordinateSplit (E := E) i
  have hinv : MeasurePreserving e.symm
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) (Measure.pi μ) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
    have he : e.symm ⁻¹' Set.univ.pi s = s i ×ˢ Set.univ.pi (fun j : {j // j ≠ i} => s j) := by
      ext p
      rcases p with ⟨a, y⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [e] using h i
        · intro j
          simpa [e, j.prop] using h j.val
      · rintro ⟨hi, hj⟩ j
        by_cases hji : j = i
        · subst j
          simpa [e] using hi
        · simpa [e, hji] using hj ⟨j, hji⟩
    rw [MeasurableEquiv.map_apply, he, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i]
  exact hinv.symm e.symm

/-- Average over precisely the other coordinates, keeping gate `i` equal to `a`. -/
noncomputable def coordinateAverage (i : ι) (X : (∀ j, E j) → ℂ) (a : E i) : ℂ :=
  ∫ y, X ((coordinateSplit i).symm (a, y)) ∂(Measure.pi fun j : {j // j ≠ i} => μ j)

omit [Fintype ι] in
lemma coordinateSplit_update (i : ι) (a : E i) (b : E i)
    (y : ∀ j : {j // j ≠ i}, E j) :
    Function.update ((coordinateSplit i).symm (b, y)) i a =
      (coordinateSplit i).symm (a, y) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [coordinateSplit_symm_apply_ne, hj]

/-- Fixing a gate and integrating all others is equally the full product
integral with that one coordinate overwritten. -/
theorem coordinateAverage_eq_integral_update (i : ι) (X : (∀ j, E j) → ℂ) (a : E i) :
    coordinateAverage μ i X a = ∫ x, X (Function.update x i a) ∂Measure.pi μ := by
  let e := coordinateSplit (E := E) i
  have hp := (coordinateSplit_measurePreserving μ i).symm e
  symm
  calc
    _ = ∫ p : E i × (∀ j : {j // j ≠ i}, E j),
        X (Function.update (e.symm p) i a)
        ∂(μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j) :=
      (hp.integral_comp' (fun x => X (Function.update x i a))).symm
    _ = ∫ p : E i × (∀ j : {j // j ≠ i}, E j), X (e.symm (a, p.2))
        ∂(μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        rcases p with ⟨b, y⟩
        change X (Function.update ((coordinateSplit i).symm (b, y)) i a) =
          X ((coordinateSplit i).symm (a, y))
        rw [coordinateSplit_update]
    _ = coordinateAverage μ i X a := by
      simpa [coordinateAverage, e] using
        (integral_fun_snd (μ := μ i) (ν := Measure.pi fun j : {j // j ≠ i} => μ j)
          (fun y => X (e.symm (a, y))))

section Continuous

variable [∀ i, TopologicalSpace (E i)]

omit [Fintype ι] in
lemma coordinateSplit_symm_continuous (i : ι) : Continuous (coordinateSplit (E := E) i).symm := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simpa [coordinateSplit, Equiv.piSplitAt] using continuous_fst
  · simpa [coordinateSplit, Equiv.piSplitAt, hj] using
      (continuous_apply (⟨j, hj⟩ : {j // j ≠ i})).comp continuous_snd

variable [∀ i, CompactSpace (E i)] [∀ i, T2Space (E i)]
  [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]

lemma coordinateAverage_continuous (i : ι) (X : (∀ j, E j) → ℂ) (hX : Continuous X) :
    Continuous (coordinateAverage μ i X) :=
  continuous_product_average _ (hX.comp (coordinateSplit_symm_continuous i))

/-- Integrating all other independent gates is an actual version of the
conditional expectation with respect to the selected gate. -/
theorem coordinateAverage_condExp (i : ι) (X : (∀ j, E j) → ℂ) (hX : Continuous X) :
    (fun x => coordinateAverage μ i X (x i)) =ᵐ[Measure.pi μ]
      (Measure.pi μ)[X | coordinateMeasurableSpace i] := by
  let e := coordinateSplit (E := E) i
  let ν := Measure.pi (fun j : {j // j ≠ i} => μ j)
  have hp := coordinateSplit_measurePreserving μ i
  have hc := coordinateAverage_continuous μ i X hX
  have hi : Integrable X (Measure.pi μ) := hX.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun x => coordinateAverage μ i X (x i)) (Measure.pi μ) :=
    (hc.comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfi : Integrable (fun p => X (e.symm p)) ((μ i).prod ν) :=
    (hX.comp (coordinateSplit_symm_continuous i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun p : E i × (∀ j : {j // j ≠ i}, E j) =>
      coordinateAverage μ i X p.1) ((μ i).prod ν) :=
    (hc.comp continuous_fst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply ae_eq_condExp_of_forall_setIntegral_eq (coordinateMeasurableSpace_le i) hi
  · intro s _ _
    exact hg.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have hpre : e ⁻¹' (t ×ˢ Set.univ) = (Function.eval i) ⁻¹' t := by
      ext x
      simp [e]
    have h1 := setIntegral_map_equiv (μ := Measure.pi μ) e
      (fun p : E i × (∀ j : {j // j ≠ i}, E j) => coordinateAverage μ i X p.1)
      (t ×ˢ Set.univ)
    have h2 := setIntegral_map_equiv (μ := Measure.pi μ) e (fun p => X (e.symm p)) (t ×ˢ Set.univ)
    rw [hp.map_eq, hpre] at h1 h2
    simp only [e, coordinateSplit_fst, MeasurableEquiv.symm_apply_apply] at h1 h2
    rw [← h1, ← h2, setIntegral_prod _ hgi.integrableOn, setIntegral_prod _ hfi.integrableOn]
    simp [coordinateAverage, ν, e]
  · exact (hc.stronglyMeasurable.comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable

/-- The manuscript's single-gate variance sum, with each summand explicitly
integrating out every other gate of the actual product experiment. -/
theorem sum_coordinateAverage_variance_le (s : Finset ι)
    (X : (∀ j, E j) → ℂ) (hX : Continuous X) :
    (∑ i ∈ s, complexVariance (μ i) (coordinateAverage μ i X)) ≤
      complexVariance (Measure.pi μ) X := by
  have hl := pi_sum_complexVariance_condExp_le μ s
    (hX.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  convert hl using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← complexVariance_congr_ae (coordinateAverage_condExp μ i X hX)]
  exact (complexVariance_comp_eval μ i
    ((coordinateAverage_continuous μ i X hX).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm

end Continuous

end Fluctuations
