import Fluctuations.ProductVariance
import Fluctuations.FiniteDimensionalVariance
import Fluctuations.Window

open MeasureTheory
open scoped ENNReal

namespace Fluctuations

universe u

/-- A depth-`d` circuit history, constructed by adjoining a fresh gate at each step. -/
def GateHistory (Y : Type u) : ℕ → Type u
  | 0 => PUnit
  | d + 1 => GateHistory Y d × Y

instance gateHistoryTopologicalSpace {Y : Type u} [TopologicalSpace Y] (d : ℕ) :
    TopologicalSpace (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (TopologicalSpace PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (TopologicalSpace (GateHistory Y d × Y))

instance gateHistoryMeasurableSpace {Y : Type u} [MeasurableSpace Y] (d : ℕ) :
    MeasurableSpace (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (GateHistory Y d × Y))

instance gateHistoryCompactSpace {Y : Type u} [TopologicalSpace Y] [CompactSpace Y]
    (d : ℕ) : CompactSpace (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (CompactSpace PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (CompactSpace (GateHistory Y d × Y))

instance gateHistoryT2Space {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (d : ℕ) : T2Space (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (T2Space PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (T2Space (GateHistory Y d × Y))

instance gateHistorySecondCountableTopology {Y : Type u} [TopologicalSpace Y]
    [SecondCountableTopology Y] (d : ℕ) : SecondCountableTopology (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (SecondCountableTopology PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (SecondCountableTopology (GateHistory Y d × Y))

instance gateHistoryBorelSpace {Y : Type u} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (d : ℕ) : BorelSpace (GateHistory Y d) := by
  induction d with
  | zero => exact inferInstanceAs (BorelSpace PUnit.{u + 1})
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (BorelSpace (GateHistory Y d × Y))

/-- Independent gate sampling at every depth; the initial history is deterministic. -/
noncomputable def historyMeasure {Y : Type u} [MeasurableSpace Y]
    (ν : Measure Y) : (d : ℕ) → Measure (GateHistory Y d)
  | 0 => Measure.dirac PUnit.unit
  | d + 1 => (historyMeasure ν d).prod ν

instance historyMeasure_isProbabilityMeasure {Y : Type u} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (d : ℕ) :
    IsProbabilityMeasure (historyMeasure ν d) := by
  induction d with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((historyMeasure ν d).prod ν))

/-- The function of the newly adjoined gate, with the earlier history fixed. -/
def historySection {Y : Type u} [TopologicalSpace Y] {d : ℕ}
    (f : C(GateHistory Y (d + 1), ℂ)) (x : GateHistory Y d) : C(Y, ℂ) where
  toFun y := f (x, y)
  continuous_toFun := f.continuous.comp (continuous_const.prodMk continuous_id)

section IndependentProcess

variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A common finite-dimensional local feature space yields one positive constant
for all continuous history observables, before choosing the process or depth.
No reverse-variance condition is assumed. -/
theorem exists_history_step_bounds (ν : Measure Y) [IsProbabilityMeasure ν]
    [ν.IsOpenPosMeasure] (S : Submodule ℂ C(Y, ℂ)) [FiniteDimensional ℂ S] (y₀ : Y) :
    ∃ η : ℝ, 0 < η ∧ ∀ (F : (d : ℕ) → C(GateHistory Y d, ℂ)),
      (∀ d x, historySection (F (d + 1)) x ∈ S) →
      (∀ d x, F (d + 1) (x, y₀) = F d x) → ∀ d,
        (η * ‖(∫ x, F (d + 1) x ∂historyMeasure ν (d + 1)) -
          ∫ x, F d x ∂historyMeasure ν d‖ ^ 2 ≤
            complexVariance (historyMeasure ν (d + 1)) (F (d + 1))) ∧
        ((η / (1 + η)) * complexVariance (historyMeasure ν d) (F d) ≤
          complexVariance (historyMeasure ν (d + 1)) (F (d + 1))) := by
  obtain ⟨η, hη, hlocal⟩ := finiteDimensional_reverseVariance ν S y₀
  refine ⟨η, hη, ?_⟩
  intro F hS hidentity d
  have hb := product_step_bounds (μ := historyMeasure ν d) (ν := ν)
    (F (d + 1)) (F (d + 1)).continuous y₀ hη
    (fun x => hlocal ⟨historySection (F (d + 1)) x, hS d x⟩)
  have heq : (fun x => F (d + 1) (x, y₀)) = (F d : GateHistory Y d → ℂ) :=
    funext (hidentity d)
  simpa only [heq] using hb

/-- An independent-gate transition window, with local reverse variance proved
from full support and a fixed finite-dimensional feature space. -/
theorem history_transition_window (ν : Measure Y) [IsProbabilityMeasure ν]
    [ν.IsOpenPosMeasure] (S : Submodule ℂ C(Y, ℂ)) [FiniteDimensional ℂ S] (y₀ : Y) :
    ∃ η : ℝ, 0 < η ∧ ∀ (F : (d : ℕ) → C(GateHistory Y d, ℂ)),
      (∀ d x, historySection (F (d + 1)) x ∈ S) →
      (∀ d x, F (d + 1) (x, y₀) = F d x) →
      ∀ {a b : ℕ} {Δ : ℝ}, 0 ≤ Δ → a < b →
      Δ ≤ ‖(∫ x, F b x ∂historyMeasure ν b) -
        ∫ x, F a x ∂historyMeasure ν a‖ →
      ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ,
        η * (η / (1 + η)) ^ r * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) ≤
          complexVariance (historyMeasure ν (d + r)) (F (d + r)) := by
  obtain ⟨η, hη, hstep⟩ := exists_history_step_bounds ν S y₀
  refine ⟨η, hη, ?_⟩
  intro F hS hidentity a b Δ hΔ hab hchange
  exact transition_window_of_step_bounds
    (fun d => ∫ x, F d x ∂historyMeasure ν d)
    (fun d => complexVariance (historyMeasure ν d) (F d)) hη hΔ
    (fun d => (hstep F hS hidentity d).1)
    (fun d => (hstep F hS hidentity d).2) hab hchange

/-- Theorem VI.14 for recursively independent gates. The same `η` works for
every process whose local sections belong to `S`, including families indexed
by system size. Only the mean gap, section membership, and identity
compatibility remain as inputs. -/
theorem history_theorem_VI_14 (ν : Measure Y) [IsProbabilityMeasure ν]
    [ν.IsOpenPosMeasure] (S : Submodule ℂ C(Y, ℂ)) [FiniteDimensional ℂ S] (y₀ : Y) :
    ∃ η : ℝ, 0 < η ∧ ∀ (F : (d : ℕ) → C(GateHistory Y d, ℂ)),
      (∀ d x, historySection (F (d + 1)) x ∈ S) →
      (∀ d x, F (d + 1) (x, y₀) = F d x) →
      ∀ {a b : ℕ}, a < b →
      (1 / 2 : ℝ) ≤ ‖(∫ x, F b x ∂historyMeasure ν b) -
        ∫ x, F a x ∂historyMeasure ν a‖ →
      ∀ (R : ℕ) {P : ℝ}, ((b - a : ℕ) : ℝ) ≤ P →
      ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
        η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤
          complexVariance (historyMeasure ν (d + r)) (F (d + r)) := by
  obtain ⟨η, hη, hwindow⟩ := history_transition_window ν S y₀
  refine ⟨η, hη, ?_⟩
  intro F hS hidentity a b hab hchange R P hwidth
  obtain ⟨d, had, hdb, hv⟩ := hwindow F hS hidentity (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hab hchange
  refine ⟨d, had, hdb, ?_⟩
  intro r hr
  have hW : (0 : ℝ) < ((b - a : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hab)
  have hP : 0 < P := hW.trans_le hwidth
  have hk : 0 ≤ η / (1 + η) := by positivity
  have hk1 : η / (1 + η) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 + η)).2
    linarith
  have hpow : (η / (1 + η)) ^ R ≤ (η / (1 + η)) ^ r :=
    pow_le_pow_of_le_one hk hk1 hr
  have hsquare : (((b - a : ℕ) : ℝ) ^ 2) ≤ P ^ 2 :=
    (sq_le_sq₀ hW.le hP.le).2 hwidth
  calc
    η * (η / (1 + η)) ^ R / (4 * P ^ 2)
      = (η * (η / (1 + η)) ^ R * (1 / 2 : ℝ) ^ 2) / P ^ 2 := by ring
    _ ≤ (η * (η / (1 + η)) ^ R * (1 / 2 : ℝ) ^ 2) /
        (((b - a : ℕ) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsquare
    _ ≤ (η * (η / (1 + η)) ^ r * (1 / 2 : ℝ) ^ 2) /
        (((b - a : ℕ) : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hη.le)
        (sq_nonneg _)
    _ ≤ complexVariance (historyMeasure ν (d + r)) (F (d + r)) := hv r

end IndependentProcess

end Fluctuations
