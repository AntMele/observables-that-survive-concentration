import Fluctuations.EndpointMarkov
import Fluctuations.EndpointBinomial

open scoped BigOperators Matrix
namespace Fluctuations

lemma endpointKilled_mul_apply {c : ℕ} {J : Type*} [Fintype J]
    (A : Matrix (Fin c) J ℝ) (i : Fin c) (j : J) :
    (endpointKilled c * A) i j =
      (8 / 25) * A i j +
      (16 / 25) * (if h : 0 < i.val then A ⟨i.val - 1, by omega⟩ j else 0) +
      (1 / 25) * (if h : i.val + 1 < c then A ⟨i.val + 1, h⟩ j else 0) := by
  simp only [Matrix.mul_apply, endpointKilled_apply, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp
    · by_cases hi : 0 < i.val
      · rw [dif_pos hi]
        have he (a : Fin c) : i.val = a.val + 1 ↔ a.val = i.val - 1 := by omega
        simp_rw [he]
        rw [show (∑ x : Fin c, if x.val = i.val - 1 then (16 / 25 : ℝ) * A x j else 0) =
          if h : i.val - 1 < c then (16 / 25 : ℝ) * A ⟨i.val - 1, h⟩ j else 0 from
            sum_fin_value c (i.val - 1) (fun x => (16 / 25 : ℝ) * A x j)]
        simp [show i.val - 1 < c by omega]
      · rw [dif_neg hi, mul_zero]
        apply Finset.sum_eq_zero
        intro a _
        simp [show i.val ≠ a.val + 1 by omega]
  · rw [show (∑ x : Fin c, if x.val = i.val + 1 then (1 / 25 : ℝ) * A x j else 0) =
      if h : i.val + 1 < c then (1 / 25 : ℝ) * A ⟨i.val + 1, h⟩ j else 0 from
        sum_fin_value c (i.val + 1) (fun x => (1 / 25 : ℝ) * A x j)]
    split_ifs <;> simp

/-- Exact finite killed-walk propagator before a path reflected from the far
boundary can return to the observed edge. No limiting approximation is used. -/
theorem endpointKilled_pow_ballot (c s : ℕ) (i : Fin (c + 1))
    (hfront : s + i.val < 2 * (c + 1)) :
    (endpointKilled (c + 1) ^ s) i 0 = endpointBallotKernel s ((i.val : ℤ) + 1) := by
  induction s generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply, endpointBallotKernel_zero (by omega)]
    by_cases hi : i = 0
    · subst i
      simp
    · rw [if_neg hi, if_neg]
      intro he
      apply hi
      apply Fin.ext
      change i.val = 0
      omega
  | succ s ih =>
    rw [pow_succ', endpointKilled_mul_apply, endpointBallotKernel_succ]
    rw [ih i (by omega)]
    have hlo : (if h : 0 < i.val then
        (endpointKilled (c + 1) ^ s) ⟨i.val - 1, by omega⟩ 0 else 0) =
        endpointBallotKernel s ((i.val : ℤ) + 1 - 1) := by
      split_ifs with hi
      · rw [ih _ (by simp; omega)]
        congr 1
        simp only
        omega
      · have hi0 : i.val = 0 := by omega
        simp [hi0, endpointBallotKernel_boundary]
    have hhi : (if h : i.val + 1 < c + 1 then
        (endpointKilled (c + 1) ^ s) ⟨i.val + 1, h⟩ 0 else 0) =
        endpointBallotKernel s ((i.val : ℤ) + 1 + 1) := by
      split_ifs with hi
      · rw [ih _ (by simp; omega)]
        congr 1
      · rw [endpointBallotKernel_outside s (by have := i.isLt; omega)]
    rw [hlo, hhi]
    ring

lemma endpointKilled_reverse (c : ℕ) (i j : Fin c) :
    endpointKilled c i j = endpointKilled c j.rev i.rev := by
  rw [endpointKilled_apply, endpointKilled_apply]
  have h0 : i = j ↔ j.rev = i.rev := by
    rw [Fin.rev_inj]
    exact eq_comm
  have h1 : i.val = j.val + 1 ↔ j.rev.val = i.rev.val + 1 := by
    simp only [Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega
  have h2 : j.val = i.val + 1 ↔ i.rev.val = j.rev.val + 1 := by
    simp only [Fin.val_rev]
    have := i.isLt
    have := j.isLt
    omega
  simp only [h0, h1, h2]

lemma endpointKilled_pow_reverse (c s : ℕ) (i j : Fin c) :
    (endpointKilled c ^ s) i j = (endpointKilled c ^ s) j.rev i.rev := by
  induction s generalizing i j with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ s ih =>
    conv_lhs => rw [pow_succ', Matrix.mul_apply]
    conv_rhs => rw [pow_succ, Matrix.mul_apply]
    apply Fintype.sum_equiv Fin.revPerm
    intro a
    simp only [Fin.revPerm_apply]
    rw [ih a j, endpointKilled_reverse c i a]
    ring

/-- Exact future propagator, obtained by reversing and transposing paths. -/
theorem endpointFutureFactor_ballot (c s : ℕ) (i : Fin (c + 1))
    (hfront : s < c + i.val + 2) :
    endpointFutureFactor (c + 1) s i =
      endpointBallotKernel s ((c : ℤ) - i.val + 1) := by
  rw [endpointFutureFactor_eq_killed, endpointKilled_pow_reverse]
  simp only [Fin.rev_last]
  rw [endpointKilled_pow_ballot c s i.rev (by
    simp only [Fin.val_rev]
    have := i.isLt
    omega)]
  congr 1
  simp only [Fin.val_rev]
  have := i.isLt
  omega

/-- Exact past propagator with the manuscript's 4/5 prefactor. -/
theorem endpointPastFactor_ballot (c s : ℕ) (i : Fin (c + 1))
    (hfront : s + i.val < 2 * (c + 1)) :
    endpointPastFactor (c + 1) s i =
      (4 / 5) * endpointBallotKernel s ((i.val : ℤ) + 1) := by
  rw [endpointPastFactor_eq_killed, endpointKilled_pow_ballot c s i hfront]

/-- Exact binomial past-front identity in its finite reflection-free region. -/
theorem endpointPastFactor_frontProfile (c s : ℕ) (i : Fin (c + 1))
    (hfront : s + i.val < 2 * (c + 1)) :
    endpointPastFactor (c + 1) s i =
      endpointFrontProfile (2 * s + 1) ((s : ℤ) - i.val) := by
  rw [endpointPastFactor_ballot c s i hfront,
    show (s : ℤ) - i.val = (s : ℤ) - ((i.val : ℤ) + 1) + 1 by omega,
    endpointFrontProfile_ballot]

/-- Exact binomial future-front identity, including its 5/4 normalization. -/
theorem endpointFutureFactor_frontProfile (c s : ℕ) (i : Fin (c + 1))
    (hfront : s < c + i.val + 2) :
    endpointFutureFactor (c + 1) s i =
      (5 / 4) * endpointFrontProfile (2 * s + 1) ((s : ℤ) - c + i.val) := by
  rw [endpointFutureFactor_ballot c s i hfront,
    show (s : ℤ) - c + i.val = (s : ℤ) - ((c : ℤ) - i.val + 1) + 1 by omega,
    endpointFrontProfile_ballot]
  ring

end Fluctuations
