import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Local lower estimates for the biased binomial probabilities occurring in
the endpoint front. The estimates follow from proved Stirling bounds. -/

open Real

namespace Fluctuations

noncomputable def endpointBinomialMass (M r : ℕ) : ℝ :=
  (M.choose r : ℝ) * (1 / 5 : ℝ) ^ r * (4 / 5 : ℝ) ^ (M - r)

lemma endpointBinomialMass_pos {M r : ℕ} (hr : r ≤ M) :
    0 < endpointBinomialMass M r := by
  unfold endpointBinomialMass
  have hc : (0 : ℝ) < M.choose r := by exact_mod_cast Nat.choose_pos hr
  positivity

lemma log_factorial_upper {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply, Nat.zero_add, Nat.succ_eq_add_one] at h
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (ne_of_gt (Real.exp_pos 1)) (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h
  rw [Real.log_mul (by norm_num) (ne_of_gt hnp),
    Real.log_div (ne_of_gt hnp) (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at h
  push_cast at h ⊢
  nlinarith

lemma log_factorial_lower {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 ≤
      Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hn)
  have hp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

lemma log_endpointBinomialMass {M r : ℕ} (hr : r ≤ M) :
    Real.log (endpointBinomialMass M r) =
      Real.log (M.factorial : ℝ) - Real.log (r.factorial : ℝ) -
      Real.log ((M-r).factorial : ℝ) +
      r * Real.log (1/5 : ℝ) + (M-r : ℕ) * Real.log (4/5 : ℝ) := by
  unfold endpointBinomialMass
  rw [Nat.cast_choose ℝ hr]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  ring

lemma binomial_entropy_identity {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (hrm : r < m) :
    m * Real.log m - r * Real.log r - (m-r) * Real.log (m-r) +
      r * Real.log (1/5 : ℝ) + (m-r) * Real.log (4/5 : ℝ) =
      -(r * Real.log (5*r/m) + (m-r) * Real.log (5*(m-r)/(4*m))) := by
  have hq : 0 < m-r := sub_pos.mpr hrm
  have h₁ : Real.log (5*r/m) = Real.log 5 + Real.log r - Real.log m := by
    rw [Real.log_div (by positivity) (ne_of_gt hm),
      Real.log_mul (by norm_num) (ne_of_gt hr)]
  have h₂ : Real.log (5*(m-r)/(4*m)) =
      Real.log 5 + Real.log (m-r) - (Real.log 4 + Real.log m) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt hq),
      Real.log_mul (by norm_num) (ne_of_gt hm)]
  rw [h₁,h₂]
  norm_num [Real.log_div]; ring

lemma binomial_entropy_upper {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (hrm : r < m) :
    r * Real.log (5*r/m) + (m-r) * Real.log (5*(m-r)/(4*m)) ≤
      (25/4 : ℝ) * (r-m/5)^2 / m := by
  have hq : 0 < m-r := sub_pos.mpr hrm
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < 5*r/m by positivity)) hr.le
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < 5*(m-r)/(4*m) by positivity)) hq.le
  have hid : r * (5*r/m-1) + (m-r)*(5*(m-r)/(4*m)-1) =
      (25/4 : ℝ)*(r-m/5)^2/m := by field_simp; ring
  linarith

/-- A logarithmic Gaussian lower estimate, uniform over all interior indices. -/
theorem log_endpointBinomialMass_lower {M r : ℕ} (hr : 0 < r) (hrM : r < M) :
    -2 - Real.log M / 2 - (25/4 : ℝ)*((r:ℝ)-M/5)^2/M ≤
      Real.log (endpointBinomialMass M r) := by
  have hM : 0 < M := lt_trans hr hrM
  have hq : 0 < M-r := Nat.sub_pos_of_lt hrM
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hrc : (r:ℝ) < M := by exact_mod_cast hrM
  have hqc : ((M-r:ℕ):ℝ) = (M:ℝ)-r := Nat.cast_sub hrM.le
  have hlo := log_factorial_lower hM
  have hru := log_factorial_upper hr
  have hqu := log_factorial_upper hq
  have hlr := Real.log_le_log hrp hrc.le
  have hlq := Real.log_le_log (show (0:ℝ) < (M-r:ℕ) by exact_mod_cast hq)
    (show ((M-r:ℕ):ℝ) ≤ M by exact_mod_cast Nat.sub_le M r)
  rw [hqc] at hqu hlq
  have he := binomial_entropy_identity hMp hrp hrc
  have hb := binomial_entropy_upper hMp hrp hrc
  rw [log_endpointBinomialMass hrM.le, hqc]
  nlinarith

/-- Explicit local Gaussian lower bound at every interior binomial index. -/
theorem endpointBinomialMass_lower {M r : ℕ} (hr : 0 < r) (hrM : r < M) :
    Real.exp (-2 - (25/4 : ℝ)*((r:ℝ)-M/5)^2/M) / Real.sqrt M ≤
      endpointBinomialMass M r := by
  have hMp : (0:ℝ) < M := by exact_mod_cast lt_trans hr hrM
  have h := Real.exp_le_exp.mpr (log_endpointBinomialMass_lower hr hrM)
  rw [Real.exp_log (endpointBinomialMass_pos hrM.le)] at h
  have hid : -2 - Real.log M / 2 - (25/4 : ℝ)*((r:ℝ)-M/5)^2/M =
      (-2 - (25/4 : ℝ)*((r:ℝ)-M/5)^2/M) - Real.log (Real.sqrt M) := by
    rw [Real.log_sqrt hMp.le]
    ring
  rwa [hid, Real.exp_sub, Real.exp_log (Real.sqrt_pos.mpr hMp)] at h

/-- Within a fixed diffusive distance of the mean, the probability is bounded
below by a positive constant times the inverse square root of the size. -/
theorem endpointBinomialMass_diffusive_lower {M r : ℕ} (hr : 0 < r) (hrM : r < M)
    {H : ℝ} (hH : 0 ≤ H) (hnear : |(r:ℝ)-M/5| ≤ H * Real.sqrt M) :
    Real.exp (-2 - (25/4 : ℝ)*H^2) / Real.sqrt M ≤ endpointBinomialMass M r := by
  have hMp : (0:ℝ) < M := by exact_mod_cast lt_trans hr hrM
  have hs := Real.sq_sqrt hMp.le
  have hsq : ((r:ℝ)-M/5)^2 ≤ H^2 * M := by
    have hh := sq_le_sq₀ (abs_nonneg ((r:ℝ)-M/5)) (mul_nonneg hH (Real.sqrt_nonneg _)) |>.mpr hnear
    rw [sq_abs, mul_pow, hs] at hh
    exact hh
  have hd : ((r:ℝ)-M/5)^2 / M ≤ H^2 := (div_le_iff₀ hMp).mpr hsq
  apply le_trans ?_ (endpointBinomialMass_lower hr hrM)
  apply div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [mul_div_assoc]
  nlinarith

end Fluctuations
