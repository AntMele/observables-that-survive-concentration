import Mathlib

open scoped BigOperators

namespace Fluctuations

/-- The permutations that survive the trace contraction of a traceless
involution: every point lies in a cycle, and all cycle lengths are even. -/
def evenCyclePerms (r : ℕ) : Finset (Equiv.Perm (Fin r)) :=
  Finset.univ.filter fun σ =>
    σ.support = Finset.univ ∧ ∀ d ∈ σ.cycleType, Even d

/-- Number of nontrivial cycles. On `evenCyclePerms` there are no fixed points,
so this is the total cycle count in the Weingarten formula. -/
def haarCycleCount {r : ℕ} (σ : Equiv.Perm (Fin r)) : ℕ := σ.cycleType.card

lemma evenCyclePerms_support {r : ℕ} {σ : Equiv.Perm (Fin r)}
    (hσ : σ ∈ evenCyclePerms r) : σ.support = Finset.univ :=
  (Finset.mem_filter.mp hσ).2.1

lemma evenCyclePerms_cycle_sum {r : ℕ} {σ : Equiv.Perm (Fin r)}
    (hσ : σ ∈ evenCyclePerms r) : σ.cycleType.sum = r := by
  rw [Equiv.Perm.sum_cycleType, evenCyclePerms_support hσ]
  simp

lemma evenCyclePerms_twice_cycleCount_le {r : ℕ} {σ : Equiv.Perm (Fin r)}
    (hσ : σ ∈ evenCyclePerms r) : 2 * haarCycleCount σ ≤ r := by
  have hh := Multiset.card_nsmul_le_sum
    (s := σ.cycleType) (a := 2) (fun d hd => Equiv.Perm.two_le_of_mem_cycleType hd)
  simpa only [nsmul_eq_mul, Nat.mul_comm, haarCycleCount, evenCyclePerms_cycle_sum hσ] using hh

lemma evenCyclePerms_card_le_factorial (r : ℕ) :
    (evenCyclePerms r).card ≤ r.factorial := by
  have hh := Finset.card_le_card (Finset.subset_univ (evenCyclePerms r))
  simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using hh

/-- At maximal total cycle count, the permutation entering the Weingarten
coefficient is odd. This gives the additional inverse dimension in the bound. -/
theorem maximal_cycles_weingarten_argument_ne_one {k : ℕ}
    (γ σ η : Equiv.Perm (Fin (2 * k)))
    (hγ : Equiv.Perm.sign γ = -1)
    (hσ : σ ∈ evenCyclePerms (2 * k)) (hη : η ∈ evenCyclePerms (2 * k))
    (hcount : haarCycleCount σ + haarCycleCount η = 2 * k) :
    η⁻¹ * γ * σ ≠ 1 := by
  have hsbound := evenCyclePerms_twice_cycleCount_le hσ
  have hebound := evenCyclePerms_twice_cycleCount_le hη
  have hcounts : haarCycleCount σ = haarCycleCount η := by omega
  have hsign : Equiv.Perm.sign σ = Equiv.Perm.sign η := by
    rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sign_of_cycleType,
      evenCyclePerms_cycle_sum hσ, evenCyclePerms_cycle_sum hη]
    exact congrArg (fun n => (-1 : ℤˣ) ^ (2 * k + n)) hcounts
  intro heq
  have hh := congrArg Equiv.Perm.sign heq
  simp only [map_mul, map_inv, map_one, hγ, hsign] at hh
  have hodd : (Equiv.Perm.sign η)⁻¹ * (-1 : ℤˣ) * Equiv.Perm.sign η = -1 := by
    calc
      _ = (-1 : ℤˣ) * ((Equiv.Perm.sign η)⁻¹ * Equiv.Perm.sign η) := by ac_rfl
      _ = -1 := by simp
  rw [hodd] at hh
  exact (by decide : (-1 : ℤˣ) ≠ 1) hh

lemma sign_finRotate_even {k : ℕ} (hk : 0 < k) :
    Equiv.Perm.sign (finRotate (2 * k)) = -1 := by
  rw [show 2 * k = (2 * (k - 1) + 1) + 1 by omega, sign_finRotate, pow_add, pow_mul]
  norm_num

/-- The two quantitative Weingarten estimates required by the combinatorial
argument. These are hypotheses, not an established Haar-integration theorem. -/
structure WeingartenCoefficientBounds (D C : ℝ) (r : ℕ)
    (W : Equiv.Perm (Fin r) → ℂ) : Prop where
  constant_nonneg : 0 ≤ C
  all_coefficients : ∀ π, D ^ r * ‖W π‖ ≤ C
  nonidentity_coefficients : ∀ π, π ≠ 1 → D ^ (r + 1) * ‖W π‖ ≤ C

/-- The explicit finite sum appearing after the Haar moment identity and
Pauli trace contractions. This definition alone asserts no Haar identity. -/
noncomputable def weingartenOTOCSum (D : ℝ) (k : ℕ)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ) : ℂ :=
  ∑ σ ∈ evenCyclePerms (2 * k), ∑ η ∈ evenCyclePerms (2 * k),
    (D : ℂ) ^ (haarCycleCount σ + haarCycleCount η) *
      W (η⁻¹ * finRotate (2 * k) * σ) / (D : ℂ)

/-- This is the missing analytic identification when `h` is an actual global
Haar OTOC mean. It is deliberately a named assumption, not an axiom or theorem. -/
def WeingartenHaarIdentity (h : ℂ) (D : ℝ) (k : ℕ)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ) : Prop :=
  h = weingartenOTOCSum D k W

lemma weingartenOTOC_term_bound {D C : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ)
    (hW : WeingartenCoefficientBounds D C (2 * k) W)
    (σ η : Equiv.Perm (Fin (2 * k)))
    (hσ : σ ∈ evenCyclePerms (2 * k)) (hη : η ∈ evenCyclePerms (2 * k)) :
    ‖(D : ℂ) ^ (haarCycleCount σ + haarCycleCount η) *
      W (η⁻¹ * finRotate (2 * k) * σ) / (D : ℂ)‖ ≤ C / D ^ 2 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hsbound := evenCyclePerms_twice_cycleCount_le hσ
  have hebound := evenCyclePerms_twice_cycleCount_le hη
  have hcount : haarCycleCount σ + haarCycleCount η ≤ 2 * k := by omega
  have hp : D ^ (haarCycleCount σ + haarCycleCount η + 1) *
      ‖W (η⁻¹ * finRotate (2 * k) * σ)‖ ≤ C := by
    by_cases heq : haarCycleCount σ + haarCycleCount η = 2 * k
    · rw [heq]
      exact hW.nonidentity_coefficients _
        (maximal_cycles_weingarten_argument_ne_one _ σ η (sign_finRotate_even hk) hσ hη heq)
    · have hlt : haarCycleCount σ + haarCycleCount η + 1 ≤ 2 * k := by omega
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hlt) (norm_nonneg _)).trans
        (hW.all_coefficients _)
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hDpos]
  apply (le_div_iff₀ (sq_pos_of_pos hDpos)).2
  convert hp using 1
  rw [pow_succ]
  field_simp
  simp only [pow_succ]
  ring

/-- The complete finite-permutation estimate in the manuscript. Its analytic
inputs are only the visibly named coefficient bounds; no Haar identity is assumed here. -/
theorem weingartenOTOCSum_norm_le {D C : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ)
    (hW : WeingartenCoefficientBounds D C (2 * k) W) :
    ‖weingartenOTOCSum D k W‖ ≤
      ((evenCyclePerms (2 * k)).card : ℝ) ^ 2 * C / D ^ 2 := by
  classical
  unfold weingartenOTOCSum
  calc
    ‖∑ σ ∈ evenCyclePerms (2 * k), ∑ η ∈ evenCyclePerms (2 * k),
        (D : ℂ) ^ (haarCycleCount σ + haarCycleCount η) *
          W (η⁻¹ * finRotate (2 * k) * σ) / (D : ℂ)‖ ≤
        ∑ σ ∈ evenCyclePerms (2 * k),
          ‖∑ η ∈ evenCyclePerms (2 * k),
            (D : ℂ) ^ (haarCycleCount σ + haarCycleCount η) *
              W (η⁻¹ * finRotate (2 * k) * σ) / (D : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ ∈ evenCyclePerms (2 * k), ∑ _η ∈ evenCyclePerms (2 * k), C / D ^ 2 := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun η hη =>
        weingartenOTOC_term_bound hD hk W hW σ η hσ hη)
    _ = _ := by simp [pow_two]; ring

/-- A coarser bound whose constant depends only on the OTOC order and the
Weingarten coefficient constant. -/
theorem weingartenOTOCSum_norm_le_factorial {D C : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ)
    (hW : WeingartenCoefficientBounds D C (2 * k) W) :
    ‖weingartenOTOCSum D k W‖ ≤ ((2 * k).factorial : ℝ) ^ 2 * C / D ^ 2 := by
  apply (weingartenOTOCSum_norm_le hD hk W hW).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg D)
  apply mul_le_mul_of_nonneg_right _ hW.constant_nonneg
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast evenCyclePerms_card_le_factorial (2 * k)

/-- Transfer to any scalar identified with the explicit sum. When instantiated
with the actual Haar OTOC mean, `hIdentity` is precisely an outstanding analytic obligation. -/
theorem norm_le_of_weingartenHaarIdentity {h : ℂ} {D C : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ)
    (hCoefficients : WeingartenCoefficientBounds D C (2 * k) W)
    (hIdentity : WeingartenHaarIdentity h D k W) :
    ‖h‖ ≤ ((2 * k).factorial : ℝ) ^ 2 * C / D ^ 2 := by
  rw [hIdentity]
  exact weingartenOTOCSum_norm_le_factorial hD hk W hCoefficients

/-- A quantitative quarter-bound, conditional on the stated integration and
coefficient inputs and an explicit dimension threshold. -/
theorem quarter_bound_of_weingartenHaarIdentity {h : ℂ} {D C : ℝ} {k : ℕ}
    (hD : 1 ≤ D) (hk : 0 < k)
    (W : Equiv.Perm (Fin (2 * k)) → ℂ)
    (hCoefficients : WeingartenCoefficientBounds D C (2 * k) W)
    (hIdentity : WeingartenHaarIdentity h D k W)
    (hDimension : 4 * (((2 * k).factorial : ℝ) ^ 2 * C) ≤ D ^ 2) :
    ‖h‖ ≤ 1 / 4 := by
  apply (norm_le_of_weingartenHaarIdentity hD hk W hCoefficients hIdentity).trans
  apply (div_le_iff₀ (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hD))).2
  linarith

end Fluctuations
