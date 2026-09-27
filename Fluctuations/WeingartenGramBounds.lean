import Fluctuations.HaarMeanCombinatorics

open scoped BigOperators Matrix.Norms.Elementwise

namespace Fluctuations

section MatrixBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma smallEntries_mulVec_norm (R : Matrix ι ι ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, ‖R i j‖ ≤ ε) (v : ι → ℂ) :
    ‖R.mulVec v‖ ≤ (Fintype.card ι : ℝ) * ε * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  calc
    ‖R.mulVec v i‖ ≤ ∑ j, ‖R i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, ε * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hR i j) (norm_le_pi_norm v j) (norm_nonneg _) hε
    _ = _ := by simp; ring

/-- A finite matrix whose perturbation from identity is small in every entry
is invertible. The proof is a maximum-coordinate contraction, not a Haar theorem. -/
theorem smallEntries_one_add_isUnit (R : Matrix ι ι ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, ‖R i j‖ ≤ ε) (hsmall : (Fintype.card ι : ℝ) * ε < 1) :
    IsUnit ((1 : Matrix ι ι ℂ) + R) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : ((1 : Matrix ι ι ℂ) + R).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  have heq : v - w = -R.mulVec (v - w) := by
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg] using hz
  have hnorm := congrArg norm heq
  rw [norm_neg] at hnorm
  have hh := smallEntries_mulVec_norm R ε hε hR (v - w)
  rw [← hnorm] at hh
  have hn : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

omit [DecidableEq ι] in
lemma smallEntries_mul_entry_norm (R V : Matrix ι ι ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, ‖R i j‖ ≤ ε) (i j : ι) :
    ‖(R * V) i j‖ ≤ (Fintype.card ι : ℝ) * ε * ‖V‖ := by
  rw [Matrix.mul_apply]
  calc
    ‖∑ u, R i u * V u j‖ ≤ ∑ u, ‖R i u * V u j‖ := norm_sum_le _ _
    _ ≤ ∑ _u : ι, ε * ‖V‖ := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_mul]
      exact mul_le_mul (hR i u) (Matrix.norm_entry_le_entrywise_sup_norm V)
        (norm_nonneg _) hε
    _ = _ := by simp; ring

/-- Uniform and off-diagonal bounds for an actual inverse near identity. -/
theorem smallEntries_inverse_entry_bounds (R V : Matrix ι ι ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, ‖R i j‖ ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 2)
    (hinverse : ((1 : Matrix ι ι ℂ) + R) * V = 1) :
    (∀ i j, ‖V i j‖ ≤ 2) ∧
      (∀ i j, i ≠ j → ‖V i j‖ ≤ 2 * (Fintype.card ι : ℝ) * ε) := by
  have hentry (i j : ι) : V i j = (1 : Matrix ι ι ℂ) i j - (R * V) i j := by
    have hh := congrArg (fun A : Matrix ι ι ℂ => A i j) hinverse
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply] at hh
    exact eq_sub_iff_add_eq.mpr hh
  have hnorm : ‖V‖ ≤ 1 + (Fintype.card ι : ℝ) * ε * ‖V‖ := by
    apply (Matrix.norm_le_iff (by positivity)).2
    intro i j
    rw [hentry]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ (smallEntries_mul_entry_norm R V ε hε hR i j)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have htwo : ‖V‖ ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg V)
    nlinarith
  refine ⟨fun i j => (Matrix.norm_entry_le_entrywise_sup_norm V).trans htwo, ?_⟩
  intro i j hij
  rw [hentry, Matrix.one_apply_ne hij, zero_sub, norm_neg]
  apply (smallEntries_mul_entry_norm R V ε hε hR i j).trans
  nlinarith [mul_le_mul_of_nonneg_left htwo
    (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hε)]

end MatrixBounds

/-- Total cycle count, now including fixed points, for the permutation Gram matrix. -/
def permutationTotalCycles {r : ℕ} (π : Equiv.Perm (Fin r)) : ℕ :=
  r - π.support.card + π.cycleType.card

@[simp] lemma permutationTotalCycles_one (r : ℕ) :
    permutationTotalCycles (1 : Equiv.Perm (Fin r)) = r := by
  simp [permutationTotalCycles]

lemma permutationTotalCycles_lt_of_ne_one {r : ℕ} (π : Equiv.Perm (Fin r))
    (hπ : π ≠ 1) : permutationTotalCycles π < r := by
  have hs : π.support.card ≤ r := by
    simpa using Finset.card_le_card (Finset.subset_univ π.support)
  have hc : 0 < π.cycleType.card := Equiv.Perm.card_cycleType_pos.mpr hπ
  have hh := Multiset.card_nsmul_le_sum (s := π.cycleType) (a := 2)
    (fun d hd => Equiv.Perm.two_le_of_mem_cycleType hd)
  rw [Equiv.Perm.sum_cycleType] at hh
  have ht : 2 * π.cycleType.card ≤ π.support.card := by simpa [mul_comm] using hh
  unfold permutationTotalCycles
  omega

/-- The normalized Gram matrix of unitary permutation tensors. Its entries
are explicit powers of dimension; no representation or integration is assumed. -/
noncomputable def normalizedPermutationGram (D : ℝ) (r : ℕ) :
    Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℂ :=
  fun σ τ => (D : ℂ) ^ permutationTotalCycles (σ⁻¹ * τ) / (D : ℂ) ^ r

lemma normalizedPermutationGram_diag {D : ℝ} (hD : 0 < D) (r : ℕ)
    (σ : Equiv.Perm (Fin r)) : normalizedPermutationGram D r σ σ = 1 := by
  simp [normalizedPermutationGram, ne_of_gt hD]

lemma normalizedPermutationGram_sub_one_entry {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (σ τ : Equiv.Perm (Fin r)) :
    ‖(normalizedPermutationGram D r - 1) σ τ‖ ≤ 1 / D := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hστ : σ = τ
  · subst τ
    simp [normalizedPermutationGram_diag hDp]
    positivity
  · have hπ : σ⁻¹ * τ ≠ 1 := by
      intro hh
      apply hστ
      have hh' := congrArg (fun p => σ * p) hh
      simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using hh'.symm
    have hc := permutationTotalCycles_lt_of_ne_one (σ⁻¹ * τ) hπ
    simp only [Matrix.sub_apply, Matrix.one_apply_ne hστ, sub_zero,
      normalizedPermutationGram, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hDp]
    apply (div_le_div_iff₀ (pow_pos hDp r) hDp).2
    simpa only [one_mul, ← pow_succ] using
      pow_le_pow_right₀ hD (Nat.succ_le_of_lt hc)

lemma factorial_div_dimension_le_half {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (hlarge : 2 * (r.factorial : ℝ) ≤ D) :
    (Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (1 / D) ≤ 1 / 2 := by
  simp only [Fintype.card_perm, Fintype.card_fin, mul_one_div]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hD)).2
  linarith

/-- The explicit permutation Gram matrix is invertible once dimension is at
least twice the number of permutations. No Haar integral formula is needed. -/
theorem normalizedPermutationGram_isUnit {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (hlarge : 2 * (r.factorial : ℝ) ≤ D) :
    IsUnit (normalizedPermutationGram D r) := by
  have hh := smallEntries_one_add_isUnit (normalizedPermutationGram D r - 1) (1 / D)
    (by positivity) (normalizedPermutationGram_sub_one_entry hD r)
    ((factorial_div_dimension_le_half hD r hlarge).trans_lt (by norm_num))
  simpa only [add_sub_cancel] using hh

theorem normalizedPermutationGram_inverse_bounds {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (hlarge : 2 * (r.factorial : ℝ) ≤ D) :
    (∀ σ τ, ‖(normalizedPermutationGram D r)⁻¹ σ τ‖ ≤ 2) ∧
      (∀ σ τ, σ ≠ τ →
        ‖(normalizedPermutationGram D r)⁻¹ σ τ‖ ≤ 2 * (r.factorial : ℝ) / D) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedPermutationGram_isUnit hD r hlarge)
  have hh := smallEntries_inverse_entry_bounds (normalizedPermutationGram D r - 1)
    ((normalizedPermutationGram D r)⁻¹) (1 / D) (by positivity)
    (normalizedPermutationGram_sub_one_entry hD r)
    (factorial_div_dimension_le_half hD r hlarge) (by
      simpa only [add_sub_cancel] using
        Matrix.mul_nonsing_inv (normalizedPermutationGram D r) hdet)
  simpa only [Fintype.card_perm, Fintype.card_fin, mul_one_div] using hh

/-- Coefficients obtained from the actual inverse of the finite permutation
Gram matrix. Identifying them with Haar moments is a separate theorem. -/
noncomputable def gramWeingartenCoefficient (D : ℝ) (r : ℕ)
    (π : Equiv.Perm (Fin r)) : ℂ :=
  (normalizedPermutationGram D r)⁻¹ 1 π / (D : ℂ) ^ r

lemma normalizedPermutationGram_leftTranslate (D : ℝ) (r : ℕ)
    (a : Equiv.Perm (Fin r)) :
    (normalizedPermutationGram D r).submatrix (Equiv.mulLeft a) (Equiv.mulLeft a) =
      normalizedPermutationGram D r := by
  ext σ τ
  simp [normalizedPermutationGram, Matrix.submatrix, mul_inv_rev, mul_assoc]

lemma normalizedPermutationGram_inverse_leftTranslate (D : ℝ) (r : ℕ)
    (a : Equiv.Perm (Fin r)) :
    ((normalizedPermutationGram D r)⁻¹).submatrix (Equiv.mulLeft a) (Equiv.mulLeft a) =
      (normalizedPermutationGram D r)⁻¹ := by
  rw [← Matrix.inv_submatrix_equiv, normalizedPermutationGram_leftTranslate]

/-- Translation invariance recovers every inverse entry from its identity row. -/
lemma normalizedPermutationGram_inverse_entry (D : ℝ) (r : ℕ)
    (σ τ : Equiv.Perm (Fin r)) :
    (normalizedPermutationGram D r)⁻¹ σ τ =
      (normalizedPermutationGram D r)⁻¹ 1 (σ⁻¹ * τ) := by
  have hh := congrArg (fun A : Matrix _ _ ℂ => A σ τ)
    (normalizedPermutationGram_inverse_leftTranslate D r σ⁻¹)
  simpa [Matrix.submatrix] using hh.symm

lemma normalizedPermutationGram_inverse_entry_scaled {D : ℝ} (hD : 0 < D) (r : ℕ)
    (σ τ : Equiv.Perm (Fin r)) :
    (normalizedPermutationGram D r)⁻¹ σ τ =
      (D : ℂ) ^ r * gramWeingartenCoefficient D r (σ⁻¹ * τ) := by
  rw [normalizedPermutationGram_inverse_entry, gramWeingartenCoefficient]
  have hpow : (D : ℂ) ^ r ≠ 0 := by exact_mod_cast (ne_of_gt (pow_pos hD r))
  field_simp

/-- The actual inverse-Gram coefficients satisfy the full finite inversion
identity. This is an algebraic theorem; the missing Haar theorem must identify
the averaged tensor projection with these coefficients. -/
theorem gramWeingarten_inverse_identity {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (hlarge : 2 * (r.factorial : ℝ) ≤ D) (σ η : Equiv.Perm (Fin r)) :
    (∑ τ : Equiv.Perm (Fin r),
      (D : ℂ) ^ permutationTotalCycles (σ⁻¹ * τ) *
        gramWeingartenCoefficient D r (τ⁻¹ * η)) = if σ = η then 1 else 0 := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hpow : (D : ℂ) ^ r ≠ 0 := by exact_mod_cast (ne_of_gt (pow_pos hDp r))
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedPermutationGram_isUnit hD r hlarge)
  have hh := congrArg (fun A : Matrix _ _ ℂ => A σ η)
    (Matrix.mul_nonsing_inv (normalizedPermutationGram D r) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro τ _
  rw [normalizedPermutationGram_inverse_entry_scaled hDp]
  unfold normalizedPermutationGram
  field_simp

lemma gramWeingartenCoefficient_scaled_norm {D : ℝ} (hD : 0 < D) (r : ℕ)
    (π : Equiv.Perm (Fin r)) :
    D ^ r * ‖gramWeingartenCoefficient D r π‖ =
      ‖(normalizedPermutationGram D r)⁻¹ 1 π‖ := by
  simp only [gramWeingartenCoefficient, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hD]
  exact mul_div_cancel₀ _ (ne_of_gt (pow_pos hD r))

/-- Elementary explicit Weingarten coefficient estimates obtained solely
from the inverse Gram matrix. The common coefficient is `2*r!`. -/
theorem gramWeingartenCoefficient_bounds {D : ℝ} (hD : 1 ≤ D) (r : ℕ)
    (hlarge : 2 * (r.factorial : ℝ) ≤ D) :
    WeingartenCoefficientBounds D (2 * (r.factorial : ℝ)) r
      (gramWeingartenCoefficient D r) := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hb := normalizedPermutationGram_inverse_bounds hD r hlarge
  refine ⟨by positivity, ?_, ?_⟩
  · intro π
    rw [gramWeingartenCoefficient_scaled_norm hDp]
    apply (hb.1 1 π).trans
    have hp : (1 : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos r
    linarith
  · intro π hπ
    calc
      D ^ (r + 1) * ‖gramWeingartenCoefficient D r π‖ =
          D * (D ^ r * ‖gramWeingartenCoefficient D r π‖) := by rw [pow_succ]; ring
      _ = D * ‖(normalizedPermutationGram D r)⁻¹ 1 π‖ := by
        rw [gramWeingartenCoefficient_scaled_norm hDp]
      _ ≤ D * (2 * (r.factorial : ℝ) / D) :=
        mul_le_mul_of_nonneg_left (hb.2 1 π hπ.symm) hDp.le
      _ = 2 * (r.factorial : ℝ) := by field_simp

/-- The inverse-Gram finite sum satisfies the all-order inverse-square bound
without assuming coefficient asymptotics. A Haar integration identity is still needed
to transfer this theorem to an actual Haar OTOC mean. -/
theorem gramWeingartenOTOCSum_norm_le {D : ℝ} {k : ℕ} (hD : 1 ≤ D) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ D) :
    ‖weingartenOTOCSum D k (gramWeingartenCoefficient D (2 * k))‖ ≤
      2 * ((2 * k).factorial : ℝ) ^ 3 / D ^ 2 := by
  have hh := weingartenOTOCSum_norm_le_factorial hD hk
    (gramWeingartenCoefficient D (2 * k)) (gramWeingartenCoefficient_bounds hD (2 * k) hlarge)
  convert hh using 1
  ring

/-- Actual Haar means can use this estimate once the explicitly named
integration identity has been supplied; no coefficient estimates are assumed. -/
theorem norm_le_of_gramWeingartenHaarIdentity {h : ℂ} {D : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ D)
    (hIdentity : WeingartenHaarIdentity h D k (gramWeingartenCoefficient D (2 * k))) :
    ‖h‖ ≤ 2 * ((2 * k).factorial : ℝ) ^ 3 / D ^ 2 := by
  rw [hIdentity]
  exact gramWeingartenOTOCSum_norm_le hD hk hlarge

theorem quarter_bound_of_gramWeingartenHaarIdentity {h : ℂ} {D : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (hlarge : 2 * ((2 * k).factorial : ℝ) ≤ D)
    (hIdentity : WeingartenHaarIdentity h D k (gramWeingartenCoefficient D (2 * k)))
    (hDimension : 8 * ((2 * k).factorial : ℝ) ^ 3 ≤ D ^ 2) :
    ‖h‖ ≤ 1 / 4 := by
  apply (norm_le_of_gramWeingartenHaarIdentity hD hk hlarge hIdentity).trans
  apply (div_le_iff₀ (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hD))).2
  linarith

end Fluctuations
