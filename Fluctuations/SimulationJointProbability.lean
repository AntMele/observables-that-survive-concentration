import Fluctuations.SimulationConcentration
import Fluctuations.SimulationParameters
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! The error event is measured under the genuine joint law of the random
circuit and its conditional randomized sampler, not an informal iterated
probability. The only analytic inputs are the circuit bias integral and the
conditional sampling tail; both are supplied by the surrounding modules. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Fluctuations

variable {C Y : Type*} [MeasurableSpace C] [MeasurableSpace Y]

/-- A uniform conditional tail bound integrates to the same joint-law bound. -/
theorem simulation_joint_section_bound (μ : Measure C) [IsProbabilityMeasure μ]
    (κ : Kernel C Y) [IsMarkovKernel κ] (A : Set (C × Y)) (hA : MeasurableSet A)
    {s : ℝ} (hs : 0 ≤ s)
    (hsection : ∀ x, (κ x).real {y | (x,y) ∈ A} ≤ s) :
    (μ ⊗ₘ κ).real A ≤ s := by
  have hle : (μ ⊗ₘ κ) A ≤ ENNReal.ofReal s := by
    rw [Measure.compProd_apply hA]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal s ∂μ := by
        apply lintegral_mono
        intro x
        have h := ENNReal.ofReal_le_ofReal (hsection x)
        simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
      _ = _ := by simp
  have h := ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top |>.mpr hle
  simpa only [Measure.real,ENNReal.toReal_ofReal hs] using h

/-- Circuit-only events retain their original probability under the joint law. -/
theorem simulation_joint_circuit_event (μ : Measure C) [IsProbabilityMeasure μ]
    (κ : Kernel C Y) [IsMarkovKernel κ] (A : Set C) (hA : MeasurableSet A) :
    (μ ⊗ₘ κ).real (A ×ˢ Set.univ) = μ.real A := by
  unfold Measure.real
  rw [Measure.compProd_apply_prod hA MeasurableSet.univ]
  simp

/-- Union of the two half-error events, under the actual circuit/sampler joint
law. `F` is the target, `H` its eye conditional mean, and `f` the sample readout. -/
theorem simulation_joint_failure (μ : Measure C) [IsProbabilityMeasure μ]
    (κ : Kernel C Y) [IsMarkovKernel κ]
    (F H : C → ℝ) (f : Y → ℝ)
    (hF : Measurable F) (hH : Measurable H) (hf : Measurable f)
    (hi : Integrable (fun x => |F x-H x|) μ)
    (ε : ℝ) (hε : 0<ε) (b s : ℝ) (hs : 0≤s)
    (hb : (∫ x, |F x-H x| ∂μ) ≤ b)
    (hconditional : ∀ x, (κ x).real {y | ε/2 ≤ |f y-H x|} ≤ s) :
    (μ ⊗ₘ κ).real {z | ε ≤ |f z.2-F z.1|} ≤ 2*b/ε+s := by
  let B : Set C := {x | ε/2 ≤ |F x-H x|}
  let S : Set (C × Y) := {z | ε/2 ≤ |f z.2-H z.1|}
  have hB : MeasurableSet B := measurableSet_le measurable_const ((hF.sub hH).abs)
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (((hf.comp measurable_snd).sub (hH.comp measurable_fst)).abs)
  have hsubset : {z : C × Y | ε ≤ |f z.2-F z.1|} ⊆ (B ×ˢ Set.univ) ∪ S := by
    intro z hz
    by_contra h
    have hnot : ¬ (ε/2 ≤ |F z.1-H z.1|) ∧ ¬ (ε/2 ≤ |f z.2-H z.1|) := by
      simpa only [B,S,Set.mem_union,Set.mem_prod,Set.mem_univ,and_true,
        Set.mem_setOf_eq,not_or] using h
    have ht := abs_sub_le (f z.2) (H z.1) (F z.1)
    rw [abs_sub_comm (H z.1) (F z.1)] at ht
    dsimp only [Set.mem_setOf_eq] at hz
    push_neg at hnot
    linarith
  have hsample := simulation_joint_section_bound μ κ S hS hs hconditional
  have hbias := simulation_bias_tail F H hi ε hε
  have hbm := mul_le_mul_of_nonneg_left hb (show 0≤2/ε by positivity)
  calc
    _ ≤ (μ ⊗ₘ κ).real ((B ×ˢ Set.univ) ∪ S) := measureReal_mono hsubset
    _ ≤ (μ ⊗ₘ κ).real (B ×ˢ Set.univ)+(μ ⊗ₘ κ).real S := measureReal_union_le _ _
    _ = μ.real B+(μ ⊗ₘ κ).real S := by rw [simulation_joint_circuit_event μ κ B hB]
    _ ≤ (2/ε)*b+s := add_le_add (hbias.trans hbm) hsample
    _ = 2*b/ε+s := by ring

/-- Substituting the paper's proved bias and sample tail yields total failure
at most delta, with the exact specified R and N. -/
theorem simulation_joint_failure_parameters (μ : Measure C) [IsProbabilityMeasure μ]
    (κ : Kernel C Y) [IsMarkovKernel κ]
    (F H : C → ℝ) (f : Y → ℝ)
    (hF : Measurable F) (hH : Measurable H) (hf : Measurable f)
    (hi : Integrable (fun x => |F x-H x|) μ)
    (n : ℕ) (hn : 0<n) (ε δ : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1)
    (hb : (∫ x, |F x-H x| ∂μ) ≤
      (100/3)*(n:ℝ)^2*Real.exp (-(simulationRadius n ε δ)^2/100))
    (hconditional : ∀ x, (κ x).real {y | ε/2 ≤ |f y-H x|} ≤
      2*Real.exp (-(simulationSampleCount ε δ:ℝ)*ε^2/8)) :
    (μ ⊗ₘ κ).real {z | ε ≤ |f z.2-F z.1|} ≤ δ := by
  have h := simulation_joint_failure μ κ F H f hF hH hf hi ε hε _ _
    (by positivity) hb hconditional
  have hp := simulationParameter_failure_sum hn hε hε1 hδ hδ1
  have he : 2*((100/3)*(n:ℝ)^2*Real.exp (-(simulationRadius n ε δ)^2/100))/ε =
      200*(n:ℝ)^2/(3*ε)*Real.exp (-(simulationRadius n ε δ)^2/100) := by ring
  rw [he] at h
  exact h.trans hp

/-- Translate the proved joint failure event into the paper's success form. -/
theorem simulation_joint_success_of_failure (μ : Measure C) [IsProbabilityMeasure μ]
    (κ : Kernel C Y) [IsMarkovKernel κ] (F : C → ℝ) (f : Y → ℝ)
    (hF : Measurable F) (hf : Measurable f) (ε δ : ℝ)
    (hfailure : (μ ⊗ₘ κ).real {z | ε ≤ |f z.2-F z.1|} ≤ δ) :
    1-δ ≤ (μ ⊗ₘ κ).real {z | |f z.2-F z.1| ≤ ε} := by
  have hm : MeasurableSet {z : C × Y | ε ≤ |f z.2-F z.1|} :=
    measurableSet_le measurable_const (((hf.comp measurable_snd).sub (hF.comp measurable_fst)).abs)
  have hc := measureReal_compl (μ:=μ ⊗ₘ κ) hm
  have hs : {z : C × Y | ε ≤ |f z.2-F z.1|}ᶜ ⊆
      {z | |f z.2-F z.1| ≤ ε} := by
    intro z hz
    simp only [Set.mem_compl_iff,Set.mem_setOf_eq,not_le] at hz
    exact hz.le
  have hmono := measureReal_mono (μ:=μ ⊗ₘ κ) hs
  rw [hc] at hmono
  have huniv : (μ ⊗ₘ κ).real Set.univ = 1 := by simp [measureReal_def]
  rw [huniv] at hmono
  linarith

end Fluctuations
