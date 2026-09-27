import Mathlib

/-!
# The deterministic depth-window argument

This module proves only the scalar part of the variance lower bound.  The
one-step variance and persistence hypotheses below are intermediate facts;
the probability module establishes them from local reverse variance.
-/

namespace Fluctuations

/-- Telescoping forces an increment at least the average endpoint change.
The sequence is complex-valued, as are OTOCs for arbitrary input states. -/
theorem exists_large_increment (μseq : ℕ → ℂ) {a b : ℕ} (hab : a < b)
    {Δ : ℝ} (hchange : Δ ≤ ‖μseq b - μseq a‖) :
    ∃ i, a ≤ i ∧ i < b ∧
      Δ / ((b - a : ℕ) : ℝ) ≤ ‖μseq (i + 1) - μseq i‖ := by
  have hW : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hab
  have hsum :
      ∑ i ∈ Finset.Ico a b, Δ / ((b - a : ℕ) : ℝ) ≤
        ∑ i ∈ Finset.Ico a b, ‖μseq (i + 1) - μseq i‖ := by
    calc
      ∑ i ∈ Finset.Ico a b, Δ / ((b - a : ℕ) : ℝ) = Δ := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        field_simp
      _ ≤ ‖μseq b - μseq a‖ := hchange
      _ = ‖∑ i ∈ Finset.Ico a b, (μseq (i + 1) - μseq i)‖ := by
        rw [Finset.sum_Ico_sub μseq hab.le]
      _ ≤ ∑ i ∈ Finset.Ico a b, ‖μseq (i + 1) - μseq i‖ := norm_sum_le _ _
  obtain ⟨i, hi, hinc⟩ := Finset.exists_le_of_sum_le
    (show (Finset.Ico a b).Nonempty from ⟨a, by simp [hab]⟩) hsum
  exact ⟨i, (Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2, hinc⟩

/-- A scalar depth-window lemma.  Its step and persistence assumptions are
proved probabilistically elsewhere, rather than assumed in the final theorem. -/
theorem window_of_step_bounds (μseq : ℕ → ℂ) (v : ℕ → ℝ)
    {η κ Δ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hΔ : 0 ≤ Δ)
    (hstep : ∀ d, η * ‖μseq (d + 1) - μseq d‖ ^ 2 ≤ v (d + 1))
    (hpersist : ∀ d, κ * v d ≤ v (d + 1))
    {a b : ℕ} (hab : a < b) (hchange : Δ ≤ ‖μseq b - μseq a‖) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ,
      η * κ ^ r * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) ≤ v (d + r) := by
  have hW : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hab
  obtain ⟨i, hai, hib, hinc⟩ := exists_large_increment μseq hab hchange
  have hsquare : (Δ / ((b - a : ℕ) : ℝ)) ^ 2 ≤
      ‖μseq (i + 1) - μseq i‖ ^ 2 :=
    (sq_le_sq₀ (div_nonneg hΔ hW.le) (norm_nonneg _)).2 hinc
  have hbase : η * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) ≤ v (i + 1) := by
    have := (mul_le_mul_of_nonneg_left hsquare hη).trans (hstep i)
    simpa only [div_pow, mul_div_assoc] using this
  refine ⟨i + 1, by omega, by omega, ?_⟩
  intro r
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
    calc
      η * κ ^ (r + 1) * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) =
          κ * (η * κ ^ r * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2)) := by
            rw [pow_succ]
            ring
      _ ≤ κ * v (i + 1 + r) := mul_le_mul_of_nonneg_left ih hκ
      _ ≤ v (i + 1 + (r + 1)) := by
        simpa only [Nat.add_assoc] using hpersist (i + 1 + r)

/-- The quantitative sequence conclusion with the sharp persistence factor
`η / (1 + η)`.  The chosen depth works for every forward offset. -/
theorem transition_window_of_step_bounds (μseq : ℕ → ℂ) (v : ℕ → ℝ)
    {η Δ : ℝ} (hη : 0 < η) (hΔ : 0 ≤ Δ)
    (hstep : ∀ d, η * ‖μseq (d + 1) - μseq d‖ ^ 2 ≤ v (d + 1))
    (hpersist : ∀ d, (η / (1 + η)) * v d ≤ v (d + 1))
    {a b : ℕ} (hab : a < b) (hchange : Δ ≤ ‖μseq b - μseq a‖) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ,
      η * (η / (1 + η)) ^ r * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) ≤
        v (d + r) :=
  window_of_step_bounds μseq v hη.le
    (div_nonneg hη.le (by linarith)) hΔ hstep hpersist hab hchange

/-- The half-unit mean-gap version, with a common lower bound throughout a
chosen forward window and an upper bound on the transition width. -/
theorem theorem_VI_14_of_step_bounds (μseq : ℕ → ℂ) (v : ℕ → ℝ)
    {η : ℝ} (hη : 0 < η)
    (hstep : ∀ d, η * ‖μseq (d + 1) - μseq d‖ ^ 2 ≤ v (d + 1))
    (hpersist : ∀ d, (η / (1 + η)) * v d ≤ v (d + 1))
    {a b : ℕ} (hab : a < b) (hchange : (1 / 2 : ℝ) ≤ ‖μseq b - μseq a‖)
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤ v (d + r) := by
  obtain ⟨d, had, hdb, hv⟩ := transition_window_of_step_bounds μseq v hη
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hstep hpersist hab hchange
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
    _ ≤ v (d + r) := hv r

end Fluctuations
