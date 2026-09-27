import Fluctuations.HaarWeingartenProjection
import Fluctuations.HaarOTOCTraceIdentity

/-! Actual all-order global Haar OTOC means and their inverse-square bound.
The Haar integration identity is derived from the tensor projection theorem;
the inverse-Gram estimates and the finite permutation sum then apply. -/

open scoped BigOperators Matrix

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

@[simp] lemma evenCyclePerms_inv_iff {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    σ⁻¹ ∈ evenCyclePerms r ↔ σ ∈ evenCyclePerms r := by
  simp [evenCyclePerms, Equiv.Perm.support_inv, Equiv.Perm.cycleType_inv]

@[simp] lemma haarCycleCount_inv {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    haarCycleCount σ⁻¹ = haarCycleCount σ := by
  simp [haarCycleCount, Equiv.Perm.cycleType_inv]

lemma tensorPowerMatrix_traceless_involution_trace_star_permutation
    (B : Matrix N N ℂ) (hB : B.IsHermitian) (hB2 : B * B = 1)
    (htr : Matrix.trace B = 0) {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Matrix.trace ((tensorPositionPermutation N σ).conjTranspose * tensorPowerMatrix r B) =
      if σ ∈ evenCyclePerms r then (Fintype.card N : ℂ) ^ haarCycleCount σ else 0 := by
  rw [Matrix.trace_mul_comm]
  change Matrix.trace (tensorPowerMatrix r B * star (tensorPositionPermutation N σ)) = _
  rw [tensorPositionPermutation_star,
    tensorPowerMatrix_traceless_involution_trace_permutation B hB hB2 htr]
  simp

lemma tensorPowerMatrix_traceless_involution_trace_cycle
    (M : Matrix N N ℂ) (hM : M.IsHermitian) (hM2 : M * M = 1)
    (htr : Matrix.trace M = 0) {r : ℕ} (σ γ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPositionPermutation N σ * tensorPowerMatrix r M *
      tensorPositionPermutation N γ) =
      if γ * σ ∈ evenCyclePerms r then
        (Fintype.card N : ℂ) ^ haarCycleCount (γ * σ) else 0 := by
  rw [(tensorPositionPermutation_commute r σ M).eq, Matrix.mul_assoc,
    tensorPositionPermutation_mul,
    tensorPowerMatrix_traceless_involution_trace_permutation M hM hM2 htr]

/-- The anti-representation convention for position permutations gives exactly
the coefficient argument in the finite OTOC sum after changing the outer index. -/
lemma weingarten_contraction_sum_eq (D : ℝ) (k : ℕ)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ) :
    (D : ℂ)⁻¹ * (∑ a : Equiv.Perm (Fin (2 * k)),
      (∑ b : Equiv.Perm (Fin (2 * k)),
        W (a⁻¹ * b) *
          (if b ∈ evenCyclePerms (2 * k) then (D : ℂ) ^ haarCycleCount b else 0)) *
      (if finRotate (2 * k) * a ∈ evenCyclePerms (2 * k) then
        (D : ℂ) ^ haarCycleCount (finRotate (2 * k) * a) else 0)) =
      weingartenOTOCSum D k W := by
  classical
  let γ := finRotate (2 * k)
  let F : Equiv.Perm (Fin (2 * k)) → ℂ := fun a =>
    (∑ b : Equiv.Perm (Fin (2 * k)), W (a⁻¹ * b) *
      (if b ∈ evenCyclePerms (2 * k) then (D : ℂ) ^ haarCycleCount b else 0)) *
    (if γ * a ∈ evenCyclePerms (2 * k) then (D : ℂ) ^ haarCycleCount (γ * a) else 0)
  change (D : ℂ)⁻¹ * (∑ a, F a) = _
  rw [← Equiv.sum_comp (Equiv.mulLeft γ⁻¹) F]
  simp only [F, Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold weingartenOTOCSum
  have hsum (f : Equiv.Perm (Fin (2 * k)) → ℂ) :
      (∑ σ ∈ evenCyclePerms (2 * k), f σ) =
        ∑ σ, if σ ∈ evenCyclePerms (2 * k) then f σ else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ ∈ evenCyclePerms (2 * k)
  · rw [if_pos hσ, hsum]
    simp only [if_pos hσ]
    apply Finset.sum_congr rfl
    intro η _
    by_cases hη : η ∈ evenCyclePerms (2 * k)
    · simp only [if_pos hη, pow_add, div_eq_mul_inv, γ]
      ring
    · simp [hη]
  · simp [hσ]

/-- The actual maximally mixed Haar mean is the finite inverse-Gram sum.
Both observables have the Hermitian traceless involution properties of the
nonidentity Pauli observables in the fluctuation theorem. -/
theorem globalHaarOTOCMean_maximallyMixed_eq_weingarten [Nonempty N]
    (B M : Matrix N N ℂ)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ Fintype.card N) :
    globalHaarOTOCMean (globalMaximallyMixedState N) B M k =
      weingartenOTOCSum (Fintype.card N) k
        (gramWeingartenCoefficient (Fintype.card N) (2 * k)) := by
  classical
  have hD : 1 ≤ (Fintype.card N : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlargeNat : 2 * (2 * k).factorial ≤ Fintype.card N := by
    exact_mod_cast hlarge
  have hcard : 2 * k ≤ Fintype.card N := by
    have hf := Nat.self_le_factorial (2 * k)
    omega
  rw [globalHaarOTOCMean_maximallyMixed_eq_tensor B M k hk,
    globalHaarTensorMean_weingarten hcard hD hlarge]
  rw [Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp_rw [tensorPowerMatrix_traceless_involution_trace_star_permutation B hB hB2 hBtr,
    tensorPowerMatrix_traceless_involution_trace_cycle M hM hM2 hMtr]
  simpa only [Complex.ofReal_natCast] using
    weingarten_contraction_sum_eq (Fintype.card N) k
      (gramWeingartenCoefficient (Fintype.card N) (2 * k))

/-- Unconditional identification of the actual Haar mean for every trace-one
state with the explicit inverse-Gram Weingarten sum. -/
theorem globalHaarOTOCMean_eq_weingarten [Nonempty N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ Fintype.card N) :
    globalHaarOTOCMean ρ B M k =
      weingartenOTOCSum (Fintype.card N) k
        (gramWeingartenCoefficient (Fintype.card N) (2 * k)) := by
  obtain ⟨α, hα⟩ :=
    globalHaarOTOCMean_state_independent_of_traceless_involution B M hM hM2 hMtr k
  rw [hα ρ hρ, ← hα (globalMaximallyMixedState N) globalMaximallyMixedState_trace]
  exact globalHaarOTOCMean_maximallyMixed_eq_weingarten B M hB hB2 hBtr hM hM2 hMtr
    k hk hlarge

/-- Actual all-order inverse-square Haar mean bound, with an explicit constant
depending only on the OTOC order and no assumed integration identity. -/
theorem globalHaarOTOCMean_norm_le [Nonempty N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ Fintype.card N) :
    ‖globalHaarOTOCMean ρ B M k‖ ≤
      2 * ((2 * k).factorial : ℝ) ^ 3 / (Fintype.card N : ℝ) ^ 2 := by
  rw [globalHaarOTOCMean_eq_weingarten ρ B M hρ hB hB2 hBtr hM hM2 hMtr k hk hlarge]
  exact gramWeingartenOTOCSum_norm_le (by exact_mod_cast Fintype.card_pos) hk hlarge

/-- The quarter bound needed by the actual circuit variance window, for every
positive OTOC order and all trace-one states. -/
theorem globalHaarOTOCMean_norm_le_quarter [Nonempty N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hB : B.IsHermitian) (hB2 : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (hMtr : Matrix.trace M = 0)
    (k : ℕ) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ Fintype.card N)
    (hDimension : 8 * ((2 * k).factorial : ℝ) ^ 3 ≤ (Fintype.card N : ℝ) ^ 2) :
    ‖globalHaarOTOCMean ρ B M k‖ ≤ 1 / 4 := by
  apply (globalHaarOTOCMean_norm_le ρ B M hρ hB hB2 hBtr hM hM2 hMtr k hk hlarge).trans
  have hD : 0 < (Fintype.card N : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (sq_pos_of_pos hD)).2
  linarith

end Fluctuations
