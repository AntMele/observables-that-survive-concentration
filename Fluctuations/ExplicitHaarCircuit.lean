import Fluctuations.ActiveHaarCircuit
import Fluctuations.ExplicitHaarVariance

/-!
# Full Haar circuit with the numerical local constant

The paper's explicit choice η = 4^(-8km) propagates through both the slope
bound and forward persistence. The global Haar mean estimate is kept visible
as an input until it is independently proved.
-/

open MeasureTheory

namespace Fluctuations

section Circuit

variable {N : Type*} [Fintype N] [DecidableEq N] {m q : ℕ}

/-- The local inequality for the full fresh layer uses the active-block constant. -/
theorem activeHaarCircuit_explicit_localReverseVariance
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ)
    (hI : ∀ i (U : SU4), Commute (I d i U.val) B)
    (x : GateHistory (ActiveHaarLayer m q) d) :
    explicitHaarConstant m k *
      ‖(∫ g, activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, g)
          ∂activeHaarLayerMeasure m q) - activeHaarCircuitOTOC A I ρ B M k d x‖ ^ 2 ≤
      complexVariance (activeHaarLayerMeasure m q)
        (fun g => activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, g)) := by
  simp_rw [activeHaarCircuitOTOC_section A I ρ B M k d hI x]
  unfold activeHaarLayerMeasure
  rw [complexVariance_fst, integral_fun_fst, measureReal_univ_eq_one, one_smul]
  exact haarLocalOTOC_explicit_reverseVariance_identity
    (fun i => (A d i).toAlgHom.toLinearMap) (fun i => (A d i).map_one)
    ρ B (activeHaarCircuitMatrix A I d x) M k

set_option maxHeartbeats 800000 in
/-- Slope and persistence for full layers, uniformly in the inactive gate count. -/
theorem activeHaarCircuit_explicit_step_bounds
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k : ℕ)
    (hI : ∀ d i (U : SU4), Commute (I d i U.val) B) (d : ℕ) :
    (explicitHaarConstant m k *
      ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k (d + 1) x
          ∂historyMeasure (activeHaarLayerMeasure m q) (d + 1)) -
        ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
          ∂historyMeasure (activeHaarLayerMeasure m q) d‖ ^ 2 ≤
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + 1))
        (activeHaarCircuitOTOC A I ρ B M k (d + 1))) ∧
    ((explicitHaarConstant m k / (1 + explicitHaarConstant m k)) *
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
        (activeHaarCircuitOTOC A I ρ B M k d) ≤
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + 1))
        (activeHaarCircuitOTOC A I ρ B M k (d + 1))) := by
  have hb := product_step_bounds (μ := historyMeasure (activeHaarLayerMeasure m q) d)
    (ν := activeHaarLayerMeasure m q)
    (activeHaarCircuitOTOC A I ρ B M k (d + 1))
    (activeHaarCircuitOTOC A I ρ B M k (d + 1)).continuous (1, 1)
    (explicitHaarConstant_pos m k) (fun x => by
      rw [activeHaarCircuitOTOC_identity]
      exact activeHaarCircuit_explicit_localReverseVariance A I ρ B M k d (hI d) x)
  simpa only [activeHaarCircuitOTOC_identity] using hb

end Circuit

/-- A bound on the active gate count gives a common explicit coefficient. -/
theorem explicitHaarConstant_antitone {m s : ℕ} (hms : m ≤ s) (k : ℕ) :
    explicitHaarConstant s k ≤ explicitHaarConstant m k := by
  unfold explicitHaarConstant
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (8 * k) hms)

theorem explicitHaarWindowConstant_antitone {m s : ℕ} (hms : m ≤ s)
    (k R : ℕ) (P : ℝ) :
    explicitHaarConstant s k * (explicitHaarConstant s k / (1 + explicitHaarConstant s k)) ^ R /
        (4 * P ^ 2) ≤
      explicitHaarConstant m k * (explicitHaarConstant m k / (1 + explicitHaarConstant m k)) ^ R /
        (4 * P ^ 2) := by
  have hs := explicitHaarConstant_pos s k
  have hm := explicitHaarConstant_pos m k
  have hη := explicitHaarConstant_antitone hms k
  have hκ : explicitHaarConstant s k / (1 + explicitHaarConstant s k) ≤
      explicitHaarConstant m k / (1 + explicitHaarConstant m k) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    nlinarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul hη (pow_le_pow_left₀ (by positivity) hκ R)
    (by positivity) (le_of_lt hm)

set_option maxHeartbeats 800000 in
/-- The numerical variance window when the endpoint mean change is given. -/
theorem activeHaarCircuit_explicit_variance_window
    {N : Type*} [Fintype N] [DecidableEq N] {m q : ℕ}
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k : ℕ)
    (hI : ∀ d i (U : SU4), Commute (I d i U.val) B)
    {a b : ℕ} (hab : a < b)
    (hchange : (1 / 2 : ℝ) ≤
      ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k b x
        ∂historyMeasure (activeHaarLayerMeasure m q) b) -
        ∫ x, activeHaarCircuitOTOC A I ρ B M k a x
        ∂historyMeasure (activeHaarLayerMeasure m q) a‖)
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant m k * (explicitHaarConstant m k / (1 + explicitHaarConstant m k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC A I ρ B M k (d + r)) := by
  exact theorem_VI_14_of_step_bounds
    (fun d => ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
      ∂historyMeasure (activeHaarLayerMeasure m q) d)
    (fun d => complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
      (activeHaarCircuitOTOC A I ρ B M k d)) (explicitHaarConstant_pos m k)
    (fun d => (activeHaarCircuit_explicit_step_bounds A I ρ B M k hI d).1)
    (fun d => (activeHaarCircuit_explicit_step_bounds A I ρ B M k hI d).2)
    hab hchange R hwidth

set_option maxHeartbeats 800000 in
/-- The variance theorem with the mean gap derived from the paper's two
quarter-unit estimates. `referenceMean` is intended to be the global Haar
mean; the moment-control and reference-mean estimates are explicit inputs.
The early commutation and inactive-gate commutation certificates encode the
remaining geometric connection to a particular spatial architecture. -/
theorem activeHaarCircuit_explicit_theorem_of_moment_control
    {N : Type*} [Fintype N] [DecidableEq N] {m q : ℕ}
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k : ℕ)
    (hI : ∀ d i (U : SU4), Commute (I d i U.val) B)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1)
    {a b : ℕ} (hab : a < b)
    (hpre : ∀ x : GateHistory (ActiveHaarLayer m q) a,
      Commute ((activeHaarCircuitMatrix A I a x).conjTranspose * B *
        activeHaarCircuitMatrix A I a x) M)
    (referenceMean : ℂ)
    (hcontrol : ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k b x
      ∂historyMeasure (activeHaarLayerMeasure m q) b) - referenceMean‖ ≤ (1 / 4 : ℝ))
    (href : ‖referenceMean‖ ≤ (1 / 4 : ℝ))
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant m k * (explicitHaarConstant m k / (1 + explicitHaarConstant m k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC A I ρ B M k (d + r)) := by
  have hchange := mean_gap_one_half
    (activeHaarCircuit_early_mean A I ρ B M k a hρ hB hM hpre) hcontrol href
  exact theorem_VI_14_of_step_bounds
    (fun d => ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
      ∂historyMeasure (activeHaarLayerMeasure m q) d)
    (fun d => complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
      (activeHaarCircuitOTOC A I ρ B M k d)) (explicitHaarConstant_pos m k)
    (fun d => (activeHaarCircuit_explicit_step_bounds A I ρ B M k hI d).1)
    (fun d => (activeHaarCircuit_explicit_step_bounds A I ρ B M k hI d).2)
    hab hchange R hwidth


end Fluctuations
