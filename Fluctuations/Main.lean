import Fluctuations.Probability
import Fluctuations.WeightedVariance
import Fluctuations.Window

open MeasureTheory
open scoped ENNReal

namespace Fluctuations

section Process

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The quantitative probabilistic content of Remark VI.15. The only substantive
inputs are the mean gap and local reverse variance; slope and persistence are
both derived from that local assumption. -/
theorem transition_window (F : ℕ → Ω → ℂ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ d, G d ≤ mΩ) (hF : ∀ d, MemLp (F d) 2 μ)
    {η Δ : ℝ} (hη : 0 < η) (hΔ : 0 ≤ Δ)
    (hlocal : ∀ d, LocalReverseVariance μ (G d) η (F d) (F (d + 1)))
    {a b : ℕ} (hab : a < b)
    (hchange : Δ ≤ ‖(∫ ω, F b ω ∂μ) - ∫ ω, F a ω ∂μ‖) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ,
      η * (η / (1 + η)) ^ r * Δ ^ 2 / (((b - a : ℕ) : ℝ) ^ 2) ≤
        complexVariance μ (F (d + r)) := by
  apply transition_window_of_step_bounds (fun d => ∫ ω, F d ω ∂μ)
    (fun d => complexVariance μ (F d)) hη hΔ
  · intro d
    exact slope_to_variance (hG d) hη.le (hF d) (hF (d + 1)) (hlocal d)
  · intro d
    exact forward_persistence (hG d) hη (hF d) (hF (d + 1)) (hlocal d)
  · exact hab
  · exact hchange

/-- Theorem VI.14, with its explicit constant from equation (119).
`P` is any upper bound on the transition width; it will be `p(n)` in the family
corollary. The same positive `η` is used at all depths. -/
theorem theorem_VI_14 (F : ℕ → Ω → ℂ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ d, G d ≤ mΩ) (hF : ∀ d, MemLp (F d) 2 μ)
    {η : ℝ} (hη : 0 < η)
    (hlocal : ∀ d, LocalReverseVariance μ (G d) η (F d) (F (d + 1)))
    {a b : ℕ} (hab : a < b)
    (hchange : (1 / 2 : ℝ) ≤ ‖(∫ ω, F b ω ∂μ) - ∫ ω, F a ω ∂μ‖)
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤ complexVariance μ (F (d + r)) := by
  obtain ⟨d, had, hdb, hv⟩ := transition_window F G hG hF hη
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hlocal hab hchange
  refine ⟨d, had, hdb, ?_⟩
  intro r hr
  have hW : (0 : ℝ) < ((b - a : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hab)
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
    _ ≤ complexVariance μ (F (d + r)) := hv r

/-- The consecutive interval and its cardinality, explicitly matching the
interval formulation in Theorem VI.14. -/
theorem theorem_VI_14_interval (F : ℕ → Ω → ℂ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ d, G d ≤ mΩ) (hF : ∀ d, MemLp (F d) 2 μ)
    {η : ℝ} (hη : 0 < η)
    (hlocal : ∀ d, LocalReverseVariance μ (G d) η (F d) (F (d + 1)))
    {a b : ℕ} (hab : a < b)
    (hchange : (1 / 2 : ℝ) ≤ ‖(∫ ω, F b ω ∂μ) - ∫ ω, F a ω ∂μ‖)
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, let I := Finset.Icc d (d + R)
      I.card = R + 1 ∧ I ⊆ Finset.Icc (a + 1) (b + R) ∧
      ∀ t ∈ I, η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤ complexVariance μ (F t) := by
  obtain ⟨d, had, hdb, hv⟩ := theorem_VI_14 F G hG hF hη hlocal hab hchange R hwidth
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [Nat.card_Icc]
    omega
  · intro t ht
    simp only [Finset.mem_Icc] at ht ⊢
    omega
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hr : t - d ≤ R := by omega
    have heq : d + (t - d) = t := by omega
    simpa only [heq] using hv (t - d) hr

end Process

/-- The asymptotic quantifiers in Theorem VI.14, made explicit: a fixed
polynomial bounds the transition widths, and one positive constant works for
all sufficiently large system sizes. The sample spaces may depend on `n`.
The constant constructed by the proof is `η * (η / (1 + η)) ^ R / 4`. -/
theorem theorem_VI_14_family
    {Ω : ℕ → Type*} [mΩ : ∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : (n : ℕ) → ℕ → Ω n → ℂ)
    (G : (n : ℕ) → ℕ → MeasurableSpace (Ω n))
    (a b : ℕ → ℕ) (p : Polynomial ℝ) {η : ℝ} (hη : 0 < η) (R n₀ : ℕ)
    (hG : ∀ n, n₀ ≤ n → ∀ d, G n d ≤ mΩ n)
    (hF : ∀ n, n₀ ≤ n → ∀ d, MemLp (F n d) 2 (μ n))
    (hlocal : ∀ n, n₀ ≤ n → ∀ d,
      LocalReverseVariance (μ n) (G n d) η (F n d) (F n (d + 1)))
    (hab : ∀ n, n₀ ≤ n → a n < b n)
    (hchange : ∀ n, n₀ ≤ n → (1 / 2 : ℝ) ≤
      ‖(∫ ω, F n (b n) ω ∂(μ n)) - ∫ ω, F n (a n) ω ∂(μ n)‖)
    (hwidth : ∀ n, n₀ ≤ n → ((b n - a n : ℕ) : ℝ) ≤ p.eval (n : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, n₀ ≤ n →
      ∃ d, a n < d ∧ d ≤ b n ∧ ∀ r : ℕ, r ≤ R →
        c / (p.eval (n : ℝ)) ^ 2 ≤ complexVariance (μ n) (F n (d + r)) := by
  refine ⟨η * (η / (1 + η)) ^ R / 4, by positivity, ?_⟩
  intro n hn
  obtain ⟨d, had, hdb, hv⟩ := theorem_VI_14 (F n) (G n) (hG n hn) (hF n hn)
    hη (hlocal n hn) (hab n hn) (hchange n hn) R (hwidth n hn)
  refine ⟨d, had, hdb, ?_⟩
  intro r hr
  simpa only [div_div] using hv r hr

end Fluctuations
