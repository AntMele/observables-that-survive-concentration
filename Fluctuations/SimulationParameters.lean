import Fluctuations.SimulationCost
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact arithmetic for the manuscript's radius and sample-count choices.
These theorems can be combined with the Haar eye-bias bound, Markov, and
Hoeffding without leaving an unverified numerical choice of constants. -/
namespace Fluctuations
noncomputable section

lemma simulationLogArgument_gt_one {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    1 < 400*(n:ℝ)^2/(3*ε*δ) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hεδ : ε*δ < 1 := by nlinarith
  apply (lt_div_iff₀ (by positivity : 0<3*ε*δ)).mpr
  nlinarith [sq_nonneg ((n:ℝ)-1)]

theorem simulationRadius_squared {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    (simulationRadius n ε δ)^2 = 100*Real.log (400*(n:ℝ)^2/(3*ε*δ)) := by
  have hlog := Real.log_nonneg (simulationLogArgument_gt_one hn hε hε1 hδ hδ1).le
  unfold simulationRadius
  rw [mul_pow,Real.sq_sqrt hlog]
  norm_num

/-- The chosen radius meets the `R ≥ 1` premise of the geometric eye bound. -/
theorem simulationRadius_ge_one {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    1 ≤ simulationRadius n ε δ := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hεδ : ε*δ < 1 := by nlinarith
  have ha : (2:ℝ) ≤ 400*(n:ℝ)^2/(3*ε*δ) := by
    apply (le_div_iff₀ (by positivity : 0<3*ε*δ)).mpr
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) ha
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h2
  have hs := simulationRadius_squared hn hε hε1 hδ hδ1
  have hR : 0 ≤ simulationRadius n ε δ := by unfold simulationRadius; positivity
  nlinarith

theorem simulationRadius_exponential {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    Real.exp (-(simulationRadius n ε δ)^2/100) = 3*ε*δ/(400*(n:ℝ)^2) := by
  rw [simulationRadius_squared hn hε hε1 hδ hδ1]
  have he : -(100*Real.log (400*(n:ℝ)^2/(3*ε*δ)))/100 =
      -Real.log (400*(n:ℝ)^2/(3*ε*δ)) := by ring
  rw [he,Real.exp_neg,Real.exp_log (by positivity)]
  simp [inv_div]

/-- Markov's eye-averaging failure probability is exactly `delta/2`. -/
theorem simulationRadius_bias_probability {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    200*(n:ℝ)^2/(3*ε)*Real.exp (-(simulationRadius n ε δ)^2/100) = δ/2 := by
  rw [simulationRadius_exponential hn hε hε1 hδ hδ1]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

theorem simulationSampleCount_positive {ε δ : ℝ} (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ<1) : 0 < simulationSampleCount ε δ := by
  have h4 : 1 < 4/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  have hraw : 0 < 8/ε^2*Real.log (4/δ) := mul_pos (by positivity) (Real.log_pos h4)
  have hc := Nat.le_ceil (8/ε^2*Real.log (4/δ))
  have hpos : (0:ℝ)<simulationSampleCount ε δ := hraw.trans_le hc
  exact_mod_cast hpos

/-- The ceiling sample count gives Hoeffding failure at most `delta/2`. -/
theorem simulationSampleCount_tail {ε δ : ℝ} (hε : 0<ε)
    (hδ : 0<δ) :
    2*Real.exp (-(simulationSampleCount ε δ:ℝ)*ε^2/8) ≤ δ/2 := by
  have hc := Nat.le_ceil (8/ε^2*Real.log (4/δ))
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ ε^2/8 by positivity)
  have he : (8/ε^2*Real.log (4/δ))*(ε^2/8)=Real.log (4/δ) := by
    field_simp
  rw [he] at hm
  have harg : -(simulationSampleCount ε δ:ℝ)*ε^2/8 ≤ -Real.log (4/δ) := by
    change Real.log (4/δ) ≤ (simulationSampleCount ε δ:ℝ)*(ε^2/8) at hm
    nlinarith
  have hx := Real.exp_le_exp.mpr harg
  have hv : Real.exp (-Real.log (4/δ))=δ/4 := by
    rw [Real.exp_neg,Real.exp_log (by positivity)]
    field_simp
  rw [hv] at hx
  linarith

/-- The two failure contributions fit within the requested total error. -/
theorem simulationParameter_failure_sum {n : ℕ} {ε δ : ℝ} (hn : 0<n)
    (hε : 0<ε) (hε1 : ε<1) (hδ : 0<δ) (hδ1 : δ<1) :
    200*(n:ℝ)^2/(3*ε)*Real.exp (-(simulationRadius n ε δ)^2/100)+
      2*Real.exp (-(simulationSampleCount ε δ:ℝ)*ε^2/8) ≤ δ := by
  rw [simulationRadius_bias_probability hn hε hε1 hδ hδ1]
  linarith [simulationSampleCount_tail hε hδ]

end
end Fluctuations
