import Fluctuations.Probability

open MeasureTheory Filter

namespace Fluctuations

/-- The product of commuting involutions has every even power equal to one. -/
lemma commuting_involutions_even_power {A : Type*} [Monoid A]
    (a b : A) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) (k : ℕ) :
    (a * b) ^ (2 * k) = 1 := by
  rw [pow_mul, hab.mul_pow 2]
  simp only [pow_two, ha, hb, one_mul, one_pow]

section Matrices

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The algebraic core of the pre-light-cone identity. Spatial separation is
used only to supply the displayed commutation hypothesis. -/
lemma normalized_trace_commuting_involutions (ρ A M : Matrix N N ℂ)
    (hρ : Matrix.trace ρ = 1) (hA : A * A = 1) (hM : M * M = 1)
    (hcomm : Commute A M) (k : ℕ) :
    Matrix.trace (ρ * (A * M) ^ (2 * k)) = 1 := by
  rw [commuting_involutions_even_power A M hA hM hcomm k, mul_one, hρ]

/-- Unitary conjugation preserves the involution relation. -/
lemma unitary_conjugate_involution (U B : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) (hB : B * B = 1) :
    (U.conjTranspose * B * U) * (U.conjTranspose * B * U) = 1 := by
  have hleft : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hright : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  calc
    (U.conjTranspose * B * U) * (U.conjTranspose * B * U)
      = U.conjTranspose * (B * (U * U.conjTranspose) * B) * U := by simp only [mul_assoc]
    _ = 1 := by rw [hright, mul_one, hB, mul_one, hleft]

/-- The OTOC equals one when the evolved involution commutes with the probe.
The geometric light-cone argument yielding commutation is a separate input. -/
lemma preLightCone_otoc_eq_one (ρ U B M : Matrix N N ℂ)
    (hρ : Matrix.trace ρ = 1) (hU : U ∈ Matrix.unitaryGroup N ℂ)
    (hB : B * B = 1) (hM : M * M = 1)
    (hcomm : Commute (U.conjTranspose * B * U) M) (k : ℕ) :
    Matrix.trace (ρ * (U.conjTranspose * B * U * M) ^ (2 * k)) = 1 :=
  normalized_trace_commuting_involutions ρ (U.conjTranspose * B * U) M hρ
    (unitary_conjugate_involution U B hU hB) hM hcomm k

/-- The pointwise pre-light-cone algebra identity gives an initial mean of one
on any probability space. No integrability premise is needed for an a.e.
constant random variable. -/
lemma integral_preLightCone_otoc_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ B M : Matrix N N ℂ)
    (U : Ω → Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hU : ∀ᵐ ω ∂μ, U ω ∈ Matrix.unitaryGroup N ℂ)
    (hB : B * B = 1) (hM : M * M = 1)
    (hcomm : ∀ᵐ ω ∂μ, Commute ((U ω).conjTranspose * B * U ω) M) (k : ℕ) :
    (∫ ω, Matrix.trace (ρ * ((U ω).conjTranspose * B * U ω * M) ^ (2 * k)) ∂μ) = 1 := by
  calc
    (∫ ω, Matrix.trace (ρ * ((U ω).conjTranspose * B * U ω * M) ^ (2 * k)) ∂μ)
      = ∫ _ : Ω, (1 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hU, hcomm] with ω hUω hcommω
        exact preLightCone_otoc_eq_one ρ (U ω) B M hρ hUω hB hM hcommω k
    _ = 1 := by simp

end Matrices

/-- A general triangle-inequality budget for an endpoint mean change.
The later mean is within `ε` of a reference whose norm is at most `δ`. -/
lemma mean_gap_of_error_budget {μa μb reference : ℂ} {A ε δ : ℝ}
    (hstart : A ≤ ‖μa‖) (happrox : ‖μb - reference‖ ≤ ε)
    (href : ‖reference‖ ≤ δ) : A - ε - δ ≤ ‖μb - μa‖ := by
  have hend : ‖μb‖ ≤ ε + δ := by
    calc
      ‖μb‖ = ‖(μb - reference) + reference‖ := by rw [sub_add_cancel]
      _ ≤ ‖μb - reference‖ + ‖reference‖ := norm_add_le _ _
      _ ≤ ε + δ := add_le_add happrox href
  have htriangle : ‖μa‖ ≤ ‖μb - μa‖ + ‖μb‖ := by
    calc
      ‖μa‖ = ‖(μa - μb) + μb‖ := by rw [sub_add_cancel]
      _ ≤ ‖μa - μb‖ + ‖μb‖ := norm_add_le _ _
      _ = ‖μb - μa‖ + ‖μb‖ := by rw [norm_sub_rev μa μb]
  linarith

/-- The paper's half-unit mean gap follows from an initial mean of one,
quarter-unit moment control, and a quarter-unit reference mean. The design
and Haar-average estimates are explicit premises, not conclusions here. -/
theorem mean_gap_one_half {μa μb haarMean : ℂ} (hstart : μa = 1)
    (happrox : ‖μb - haarMean‖ ≤ (1 / 4 : ℝ))
    (hhaar : ‖haarMean‖ ≤ (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖μb - μa‖ := by
  have h := mean_gap_of_error_budget (μa := μa) (μb := μb) (A := (1 : ℝ))
    (by simp [hstart]) happrox hhaar
  norm_num at h ⊢
  exact h

end Fluctuations
