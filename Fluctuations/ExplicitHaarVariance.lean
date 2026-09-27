import Fluctuations.BalancedHaarFeatures

open MeasureTheory
open scoped ENNReal

namespace Fluctuations

/-- The explicit reverse-variance coefficient for `m` Haar SU(4) gates. -/
noncomputable def explicitHaarConstant (m k : ℕ) : ℝ :=
  1 / (4 : ℝ) ^ (8 * k * m)

theorem explicitHaarConstant_pos (m k : ℕ) : 0 < explicitHaarConstant m k := by
  unfold explicitHaarConstant
  positivity

/-- The balanced local feature family has the quantitative Haar bound
`4^(-8*k*m)`, uniformly over all its coefficients. -/
theorem balancedSU4_reverseVariance (m k : ℕ) (f : C(SU4Block m, ℂ))
    (hf : f ∈ polynomialFeatureSpace (balancedSU4Features m) (2 * k)) :
    explicitHaarConstant m k * ‖(∫ x, f x ∂su4Haar m) - f 1‖ ^ 2 ≤
      complexVariance (su4Haar m) f := by
  have hh := haar_subspace_reverseVariance (su4Haar m)
    (polynomialFeatureSpace (balancedSU4Features m) (2 * k))
    (balancedSU4_polynomial_translate_mem m (2 * k)) f hf 1
  have hdim :
      (Module.finrank ℂ (polynomialFeatureSpace (balancedSU4Features m) (2 * k)) : ℝ) ≤
        (4 : ℝ) ^ (8 * k * m) := by
    exact_mod_cast balancedSU4_polynomial_finrank_le m k
  have hvar : 0 ≤ complexVariance (su4Haar m) f := integral_nonneg fun _ => sq_nonneg _
  have hbound := hh.trans (mul_le_mul_of_nonneg_right hdim hvar)
  rw [explicitHaarConstant, one_div]
  exact (inv_mul_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ (8 * k * m))).2 hbound

section EmbeddedGates

variable {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- The unconditional exact local reverse-variance bound for the matrix OTOC
of any block of `m` independent Haar SU(4) gates. -/
theorem haarLocalOTOC_explicit_reverseVariance
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    explicitHaarConstant m k *
      ‖(∫ x, haarLocalOTOC E ρ B V M k x ∂su4Haar m) -
        haarLocalOTOC E ρ B V M k 1‖ ^ 2 ≤
      complexVariance (su4Haar m) (haarLocalOTOC E ρ B V M k) :=
  balancedSU4_reverseVariance m k _ (haarLocalOTOC_balanced_mem E ρ B V M k)

/-- Explicit coefficient with the no-new-gate OTOC written as a trace. -/
theorem haarLocalOTOC_explicit_reverseVariance_identity
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    explicitHaarConstant m k *
      ‖(∫ x, haarLocalOTOC E ρ B V M k x ∂su4Haar m) -
        Matrix.trace (ρ * (V.conjTranspose * B * V * M) ^ (2 * k))‖ ^ 2 ≤
      complexVariance (su4Haar m) (haarLocalOTOC E ρ B V M k) := by
  simpa only [haarLocalOTOC_one E hE] using
    haarLocalOTOC_explicit_reverseVariance E ρ B V M k

end EmbeddedGates

section Conditional

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [SecondCountableTopology X] [mX : MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- The exact product-Haar local coefficient also holds for the genuine
conditional variance given the already-built circuit. -/
theorem haarLocalOTOC_explicit_conditional_reverseVariance
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) (ρ B M : Matrix N N ℂ)
    (V : X → Matrix N N ℂ) (hV : Continuous V) (k : ℕ) :
    LocalReverseVariance (μ.prod (su4Haar m)) (mX.comap Prod.fst)
      (explicitHaarConstant m k)
      (fun p : X × SU4Block m =>
        Matrix.trace (ρ * ((V p.1).conjTranspose * B * V p.1 * M) ^ (2 * k)))
      (fun p : X × SU4Block m => haarLocalOTOC E ρ B (V p.1) M k p.2) := by
  have hh := product_localReverseVariance (μ := μ) (ν := su4Haar m)
    (fun p : X × SU4Block m => haarLocalOTOC E ρ B (V p.1) M k p.2)
    (haarLocalOTOC_joint_continuous E ρ B M V hV k) (1 : SU4Block m)
    (explicitHaarConstant m k)
    (fun x => haarLocalOTOC_explicit_reverseVariance E ρ B (V x) M k)
  simpa only [haarLocalOTOC_one E hE] using hh

end Conditional

end Fluctuations
