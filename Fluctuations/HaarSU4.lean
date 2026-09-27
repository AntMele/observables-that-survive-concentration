import Mathlib

open MeasureTheory Set
open scoped Matrix

namespace Fluctuations

/-- The genuine special unitary group of two-qubit gates. -/
abbrev SU4 := Matrix.specialUnitaryGroup (Fin 4) ℂ
/-- A block of `m` two-qubit special unitary gates. -/
abbrev SU4Block (m : ℕ) := Fin m → SU4

lemma su4_entry_norm_le_one (A : SU4) (i j : Fin 4) : ‖A.val i j‖ ≤ 1 := by
  have hrow := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℂ => (T i i).re) A.prop.1.2
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.re_sum] at hrow
  have heq : (∑ k : Fin 4, Complex.normSq (A.val i k)) = 1 := by
    simpa only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Matrix.one_apply_eq, Complex.one_re] using hrow
  have hle := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => Complex.normSq_nonneg (A.val i k))
    (Finset.mem_univ j)
  rw [heq, Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (A.val i j)]

lemma isClosed_su4 : IsClosed (Matrix.specialUnitaryGroup (Fin 4) ℂ : Set (Matrix (Fin 4) (Fin 4) ℂ)) := by
  have heq : (Matrix.specialUnitaryGroup (Fin 4) ℂ : Set (Matrix (Fin 4) (Fin 4) ℂ)) =
      {A | A * star A = 1} ∩ {A | A.det = 1} := by
    ext A
    change (A ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ) ↔ _
    simp only [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff,
      Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [heq]
  exact (isClosed_eq (continuous_id.mul continuous_star) continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)

instance : CompactSpace SU4 := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_su4
  intro A hA i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact su4_entry_norm_le_one ⟨A, hA⟩ i j

instance : ContinuousInv SU4 where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

instance : IsTopologicalGroup SU4 where



instance : SecondCountableTopology SU4 := by
  letI : SecondCountableTopology (Matrix (Fin 4) (Fin 4) ℂ) := by
    change SecondCountableTopology (Fin 4 → Fin 4 → ℂ)
    infer_instance
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrix.specialUnitaryGroup (Fin 4) ℂ : Set (Matrix (Fin 4) (Fin 4) ℂ))

instance : MeasurableSpace SU4 := borel SU4
instance : BorelSpace SU4 := ⟨rfl⟩

/-- Normalized Haar measure on the compact group SU(4). -/
noncomputable def su4SingleHaar : Measure SU4 :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance : IsProbabilityMeasure su4SingleHaar where
  measure_univ := Measure.haarMeasure_self

instance : Measure.IsHaarMeasure su4SingleHaar :=
  Measure.isHaarMeasure_haarMeasure _

/-- The product law of `m` independent normalized Haar SU(4) gates. -/
noncomputable def su4Haar (m : ℕ) : Measure (SU4Block m) :=
  Measure.pi fun _ => su4SingleHaar

instance (m : ℕ) : IsProbabilityMeasure (su4Haar m) := by
  unfold su4Haar
  infer_instance

instance (m : ℕ) : Measure.IsHaarMeasure (su4Haar m) := by
  unfold su4Haar
  infer_instance

instance (m : ℕ) : Measure.IsOpenPosMeasure (su4Haar m) := by
  infer_instance

/-- The actual gate coordinates are independent under the block measure. -/
lemma su4Haar_independent (m : ℕ) :
    ProbabilityTheory.iIndepFun (fun i : Fin m => fun x : SU4Block m => x i) (su4Haar m) := by
  exact ProbabilityTheory.iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- A matrix entry of a gate is a continuous coordinate function. -/
def su4Entry (m : ℕ) (g : Fin m) (i j : Fin 4) : C(SU4Block m, ℂ) where
  toFun x := (x g).val i j
  continuous_toFun := (continuous_apply j).comp
    ((continuous_apply i).comp (continuous_subtype_val.comp (continuous_apply g)))

@[simp] lemma su4Entry_apply (m : ℕ) (g : Fin m) (i j : Fin 4) (x : SU4Block m) :
    su4Entry m g i j x = (x g).val i j := rfl


/-- Matrix entries and their complex conjugates, independent of all observables
and all spectator systems. There are `32*m` raw coordinates. -/
def rawSU4Features (m : ℕ) : (Fin m × Fin 4 × Fin 4 × Bool) → C(SU4Block m, ℂ) :=
  fun p => if p.2.2.2 then star (su4Entry m p.1 p.2.1 p.2.2.1)
    else su4Entry m p.1 p.2.1 p.2.2.1

@[simp] lemma rawSU4Features_false (m : ℕ) (g : Fin m) (i j : Fin 4) :
    rawSU4Features m (g, i, j, false) = su4Entry m g i j := rfl

@[simp] lemma rawSU4Features_true (m : ℕ) (g : Fin m) (i j : Fin 4) :
    rawSU4Features m (g, i, j, true) = star (su4Entry m g i j) := rfl

lemma star_rawSU4Features (m : ℕ) (p : Fin m × Fin 4 × Fin 4 × Bool) :
    star (rawSU4Features m p) = rawSU4Features m (p.1, p.2.1, p.2.2.1, !p.2.2.2) := by
  rcases p with ⟨g, i, j, b⟩
  cases b <;> simp [rawSU4Features]

/-- The actual SU(4) gate matrix, with continuous-function entries. -/
def su4CoordinateMatrix (m : ℕ) (g : Fin m) :
    Matrix (Fin 4) (Fin 4) C(SU4Block m, ℂ) :=
  fun i j => su4Entry m g i j

@[simp] lemma su4CoordinateMatrix_apply (m : ℕ) (g : Fin m) (i j : Fin 4)
    (x : SU4Block m) : su4CoordinateMatrix m g i j x = (x g).val i j := rfl

lemma su4CoordinateMatrix_entry_mem (m : ℕ) (g : Fin m) (i j : Fin 4) :
    su4CoordinateMatrix m g i j ∈ Submodule.span ℂ (Set.range (rawSU4Features m)) :=
  Submodule.subset_span ⟨(g, i, j, false), rfl⟩

lemma su4CoordinateMatrix_star_entry_mem (m : ℕ) (g : Fin m) (i j : Fin 4) :
    star (su4CoordinateMatrix m g i j) ∈
      Submodule.span ℂ (Set.range (rawSU4Features m)) :=
  Submodule.subset_span ⟨(g, i, j, true), rfl⟩

end Fluctuations
