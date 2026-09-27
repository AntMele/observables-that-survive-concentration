import Fluctuations.CoordinateAverages

/-! Error control for actually integrating out an arbitrary list of independent gates. -/

open MeasureTheory
open scoped BigOperators

namespace Fluctuations

set_option linter.unusedSectionVars false

section CompactProduct

variable {ι G : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [IsProbabilityMeasure ν]

/-- Integrate this coordinate, keeping every other coordinate fixed. -/
noncomputable def eraseGateAverage (i : ι) (F : (ι → G) → ℝ) (x : ι → G) : ℝ :=
  ∫ g, F (Function.update x i g) ∂ν

lemma eraseGateAverage_continuous (i : ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    Continuous (eraseGateAverage ν i F) :=
  continuous_product_average (fun p : (ι → G) × G => F (Function.update p.1 i p.2))
    (hF.comp (continuous_fst.update i continuous_snd))

lemma eraseGateAverage_integral (i : ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    (∫ x, eraseGateAverage ν i F x ∂Measure.pi (fun _ => ν)) =
      ∫ x, F x ∂Measure.pi (fun _ : ι => ν) := by
  let e := coordinateSplit (E := fun _ : ι => G) i
  let μ := Measure.pi (fun _ : {j : ι // j ≠ i} => ν)
  have hp := (coordinateSplit_measurePreserving (fun _ : ι => ν) i).symm e
  have hc : Continuous (fun p : G × ({j : ι // j ≠ i} → G) => F (e.symm p)) :=
    hF.comp (coordinateSplit_symm_continuous i)
  have hi := hc.integrable_of_hasCompactSupport (μ := ν.prod μ) (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ p : G × ({j : ι // j ≠ i} → G), eraseGateAverage ν i F (e.symm p)
        ∂ν.prod μ := (hp.integral_comp' _).symm
    _ = ∫ p : G × ({j : ι // j ≠ i} → G), (∫ g, F (e.symm (g, p.2)) ∂ν)
        ∂ν.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        rcases p with ⟨a, y⟩
        unfold eraseGateAverage
        simp only [e, coordinateSplit_update]
    _ = ∫ y, ∫ g, F (e.symm (g, y)) ∂ν ∂μ := by
      simpa using integral_fun_snd (μ := ν) (ν := μ)
        (fun y => ∫ g, F (e.symm (g,y)) ∂ν)
    _ = ∫ g, ∫ y, F (e.symm (g,y)) ∂μ ∂ν := (integral_integral_swap hi).symm
    _ = ∫ p, F (e.symm p) ∂ν.prod μ := (integral_prod _ hi).symm
    _ = _ := hp.integral_comp' F

lemma eraseGateAverage_sub (i : ι) (F H : (ι → G) → ℝ)
    (hF : Continuous F) (hH : Continuous H) (x : ι → G) :
    eraseGateAverage ν i (fun x => F x - H x) x =
      eraseGateAverage ν i F x - eraseGateAverage ν i H x := by
  exact integral_sub
    ((hF.comp (continuous_const.update i continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((hH.comp (continuous_const.update i continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

lemma eraseGateAverage_abs_le (i : ι) (F : (ι → G) → ℝ) (x : ι → G) :
    |eraseGateAverage ν i F x| ≤ eraseGateAverage ν i (fun x => |F x|) x := by
  simpa only [eraseGateAverage, Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun g => F (Function.update x i g))

theorem eraseGateAverage_L1_contraction (i : ι) (F H : (ι → G) → ℝ)
    (hF : Continuous F) (hH : Continuous H) :
    (∫ x, |eraseGateAverage ν i F x - eraseGateAverage ν i H x|
      ∂Measure.pi (fun _ => ν)) ≤ ∫ x, |F x - H x| ∂Measure.pi (fun _ : ι => ν) := by
  simp_rw [← eraseGateAverage_sub ν i F H hF hH]
  calc
    _ ≤ ∫ x, eraseGateAverage ν i (fun x => |F x - H x|) x
        ∂Measure.pi (fun _ : ι => ν) := by
      apply integral_mono
      · exact ((eraseGateAverage_continuous ν i _ (hF.sub hH)).abs).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (eraseGateAverage_continuous ν i _ (hF.sub hH).abs).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact fun x => eraseGateAverage_abs_le ν i _ x
    _ = _ := eraseGateAverage_integral ν i _ (hF.sub hH).abs

/-- The operational partial Haar average: integrate each listed gate. -/
noncomputable def eraseGatesAverage : List ι → ((ι → G) → ℝ) → (ι → G) → ℝ
  | [], F => F
  | i :: is, F => eraseGateAverage ν i (eraseGatesAverage is F)

lemma eraseGatesAverage_continuous (is : List ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    Continuous (eraseGatesAverage ν is F) := by
  induction is with
  | nil => exact hF
  | cons i is ih => exact eraseGateAverage_continuous ν i _ ih

/-- Telescoping the actual partial average costs at most the sum of the
original observable's individual-coordinate averaging errors. -/
theorem eraseGatesAverage_L1_error (is : List ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    (∫ x, |F x - eraseGatesAverage ν is F x| ∂Measure.pi (fun _ => ν)) ≤
      (is.map fun i => ∫ x, |F x - eraseGateAverage ν i F x|
        ∂Measure.pi (fun _ : ι => ν)).sum := by
  induction is with
  | nil => simp [eraseGatesAverage]
  | cons i is ih =>
    have hc := eraseGatesAverage_continuous ν is F hF
    have hi (H : (ι → G) → ℝ) (hH : Continuous H) :
        Integrable H (Measure.pi (fun _ : ι => ν)) :=
      hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    change (∫ x, |F x - eraseGateAverage ν i (eraseGatesAverage ν is F) x|
      ∂Measure.pi (fun _ : ι => ν)) ≤ _
    calc
      _ ≤ ∫ x, |F x - eraseGateAverage ν i F x| +
          |eraseGateAverage ν i F x - eraseGateAverage ν i (eraseGatesAverage ν is F) x|
          ∂Measure.pi (fun _ : ι => ν) := by
        apply integral_mono
        · exact hi _ (hF.sub (eraseGateAverage_continuous ν i _ hc)).abs
        · exact hi _ ((hF.sub (eraseGateAverage_continuous ν i F hF)).abs.add
            ((eraseGateAverage_continuous ν i F hF).sub (eraseGateAverage_continuous ν i _ hc)).abs)
        · exact fun x => abs_sub_le _ _ _
      _ = (∫ x, |F x - eraseGateAverage ν i F x| ∂Measure.pi (fun _ : ι => ν)) +
          ∫ x, |eraseGateAverage ν i F x - eraseGateAverage ν i (eraseGatesAverage ν is F) x|
          ∂Measure.pi (fun _ : ι => ν) := integral_add
            (hi _ (hF.sub (eraseGateAverage_continuous ν i F hF)).abs)
            (hi _ ((eraseGateAverage_continuous ν i F hF).sub
              (eraseGateAverage_continuous ν i _ hc)).abs)
      _ ≤ _ := by
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add_left ((eraseGateAverage_L1_contraction ν i F _ hF hc).trans ih) _

/-- Replace exactly the listed coordinates by an independent circuit sample. -/
def replaceGateSubset (s : Finset ι) (x y : ι → G) : ι → G :=
  fun i => if i ∈ s then y i else x i

lemma replaceGateSubset_continuous (s : Finset ι) :
    Continuous (fun p : (ι → G) × (ι → G) => replaceGateSubset s p.1 p.2) := by
  apply continuous_pi
  intro i
  by_cases h : i ∈ s <;> simp only [replaceGateSubset, h, ↓reduceIte] <;> fun_prop

noncomputable def eraseSubsetAverage (s : Finset ι) (F : (ι → G) → ℝ) (x : ι → G) : ℝ :=
  ∫ y, F (replaceGateSubset s x y) ∂Measure.pi (fun _ => ν)

lemma eraseSubsetAverage_continuous (s : Finset ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    Continuous (eraseSubsetAverage ν s F) :=
  continuous_product_average _ (hF.comp (replaceGateSubset_continuous s))

lemma eraseSubsetAverage_empty (F : (ι → G) → ℝ) : eraseSubsetAverage ν ∅ F = F := by
  funext x
  have he (y : ι → G) : replaceGateSubset ∅ x y = x := by
    funext i
    simp [replaceGateSubset]
  simp only [eraseSubsetAverage, he]
  simp

lemma eraseSubsetAverage_insert (i : ι) (s : Finset ι) (F : (ι → G) → ℝ)
    (hF : Continuous F) :
    eraseGateAverage ν i (eraseSubsetAverage ν s F) = eraseSubsetAverage ν (insert i s) F := by
  funext x
  by_cases his : i ∈ s
  · have he (g : G) (y : ι → G) : replaceGateSubset s (Function.update x i g) y =
        replaceGateSubset s x y := by
      funext j
      by_cases hj : j ∈ s
      · simp [replaceGateSubset, hj]
      · have hji : j ≠ i := by rintro rfl; exact hj his
        simp [replaceGateSubset, hj, hji]
    simp [eraseGateAverage, eraseSubsetAverage, he, Finset.insert_eq_of_mem his]
  · have he (g : G) (y : ι → G) : replaceGateSubset s (Function.update x i g) y =
        replaceGateSubset (insert i s) x (Function.update y i g) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [replaceGateSubset, his]
      · simp [replaceGateSubset, hji]
    let H : (ι → G) → ℝ := fun y => F (replaceGateSubset (insert i s) x y)
    have hH : Continuous H := hF.comp
      ((replaceGateSubset_continuous (insert i s)).comp (continuous_const.prodMk continuous_id))
    change (∫ g, ∫ y, F (replaceGateSubset s (Function.update x i g) y)
      ∂Measure.pi (fun _ => ν) ∂ν) = _
    simp_rw [he]
    have hcont : Continuous (fun p : G × (ι → G) => H (Function.update p.2 i p.1)) :=
      hH.comp (continuous_snd.update i continuous_fst)
    rw [integral_integral_swap (hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    exact eraseGateAverage_integral ν i H hH

/-- Iterated coordinate averaging equals the literal product-Haar partial
integral, independently of the ordering or repetition of erased coordinates. -/
theorem eraseGatesAverage_eq_subset (is : List ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    eraseGatesAverage ν is F = eraseSubsetAverage ν is.toFinset F := by
  induction is with
  | nil => exact (eraseSubsetAverage_empty ν F).symm
  | cons i is ih =>
    simp only [eraseGatesAverage, List.toFinset_cons, ih]
    exact eraseSubsetAverage_insert ν i is.toFinset F hF

/-- Finite-set form of the replacement bound, with no ordering assumptions. -/
theorem eraseSubsetAverage_L1_error (s : Finset ι) (F : (ι → G) → ℝ) (hF : Continuous F) :
    (∫ x, |F x - eraseSubsetAverage ν s F x| ∂Measure.pi (fun _ => ν)) ≤
      ∑ i ∈ s, ∫ x, |F x - eraseGateAverage ν i F x| ∂Measure.pi (fun _ : ι => ν) := by
  have h := eraseGatesAverage_L1_error ν s.toList F hF
  rw [eraseGatesAverage_eq_subset ν s.toList F hF, Finset.toList_toFinset] at h
  have he := List.sum_toFinset (fun i => ∫ x, |F x - eraseGateAverage ν i F x|
    ∂Measure.pi (fun _ : ι => ν)) s.nodup_toList
  rw [Finset.toList_toFinset] at he
  rwa [← he] at h

theorem eraseSubsetAverage_L1_error_uniform (s : Finset ι) (F : (ι → G) → ℝ)
    (hF : Continuous F) (b : ℝ)
    (hb : ∀ i ∈ s, (∫ x, |F x - eraseGateAverage ν i F x|
      ∂Measure.pi (fun _ : ι => ν)) ≤ b) :
    (∫ x, |F x - eraseSubsetAverage ν s F x| ∂Measure.pi (fun _ => ν)) ≤ s.card * b := by
  apply (eraseSubsetAverage_L1_error ν s F hF).trans
  calc
    _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum hb
    _ = _ := by simp

/-- Pointwise sensitivity to replacing one gate bounds the actual averaging error. -/
theorem eraseGateAverage_error_le (i : ι) (F : (ι → G) → ℝ) (hF : Continuous F)
    (H : (ι → G) → ℝ) (h : ∀ x g, |F x - F (Function.update x i g)| ≤ H x)
    (x : ι → G) : |F x - eraseGateAverage ν i F x| ≤ H x := by
  have hi : Integrable (fun g => F (Function.update x i g)) ν :=
    (hF.comp (continuous_const.update i continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : F x - eraseGateAverage ν i F x =
      ∫ g, F x - F (Function.update x i g) ∂ν := by
    rw [integral_sub (integrable_const _) hi]
    simp [eraseGateAverage]
  rw [he]
  calc
    _ ≤ ∫ g, |F x - F (Function.update x i g)| ∂ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun g => F x - F (Function.update x i g))
    _ ≤ ∫ _g : G, H x ∂ν := integral_mono ((integrable_const _).sub hi).abs
      (integrable_const _) (h x)
    _ = H x := by simp

end CompactProduct

section SqrtMean

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Jensen's square-root bound with all integrability discharged by continuity. -/
theorem simulation_integral_sqrt_le (w : Ω → ℝ) (hw : Continuous w) (hn : ∀ x, 0 ≤ w x) :
    (∫ x, Real.sqrt (w x) ∂μ) ≤ Real.sqrt (∫ x, w x ∂μ) := by
  have hlp : MemLp (fun x => Real.sqrt (w x)) 2 μ :=
    hw.sqrt.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv := ProbabilityTheory.variance_eq_sub hlp
  have hvar := ProbabilityTheory.variance_nonneg (fun x => Real.sqrt (w x)) μ
  simp only [Pi.pow_apply] at hv
  simp_rw [Real.sq_sqrt (hn _)] at hv
  have hmean : 0 ≤ ∫ x, w x ∂μ := integral_nonneg hn
  nlinarith [Real.sq_sqrt hmean, Real.sqrt_nonneg (∫ x, w x ∂μ)]

end SqrtMean

end Fluctuations
