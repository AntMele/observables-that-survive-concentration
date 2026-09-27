import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace Fluctuations

/-- Adjacent-cell difference columns; there are c edges and c+1 cells. -/
def endpointDifference (c : ℕ) : Matrix (Fin (c + 1)) (Fin c) ℝ :=
  fun i j => (if i = j.succ then 1 else 0) - (if i = j.castSucc then 1 else 0)

/-- The past sensitivity takes this weighted difference of adjacent cell masses. -/
noncomputable def endpointGradient (c : ℕ) : Matrix (Fin c) (Fin (c + 1)) ℝ :=
  fun i j => (if j = i.castSucc then 4 / 5 else 0) - (if j = i.succ then 1 / 20 else 0)

/-- Reflecting endpoint-cell transition matrix. The factorization is useful
for exact propagation of past and future gate sensitivities. -/
noncomputable def endpointMarkov (c : ℕ) : Matrix (Fin (c + 1)) (Fin (c + 1)) ℝ :=
  1 + (4 / 5 : ℝ) • (endpointDifference c * endpointGradient c)

/-- Killed edge walk obtained by taking weighted differences of the cell chain. -/
noncomputable def endpointKilled (c : ℕ) : Matrix (Fin c) (Fin c) ℝ :=
  1 + (4 / 5 : ℝ) • (endpointGradient c * endpointDifference c)

lemma endpointGradient_mul_apply {c : ℕ} {J : Type*} [Fintype J]
    (A : Matrix (Fin (c + 1)) J ℝ) (i : Fin c) (j : J) :
    (endpointGradient c * A) i j = (4 / 5) * A i.castSucc j - (1 / 20) * A i.succ j := by
  simp [Matrix.mul_apply, endpointGradient, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma mul_endpointDifference_apply {c : ℕ} {J : Type*} [Fintype J]
    (A : Matrix J (Fin (c + 1)) ℝ) (i : J) (j : Fin c) :
    (A * endpointDifference c) i j = A i j.succ - A i j.castSucc := by
  simp [Matrix.mul_apply, endpointDifference, mul_sub, Finset.sum_sub_distrib, mul_ite]

/-- The edge walk has the bulk weights 16/25, 8/25, 1/25 and absorbing
boundaries: omitted neighbors contribute no reflected holding probability. -/
theorem endpointKilled_apply (c : ℕ) (i j : Fin c) :
    endpointKilled c i j =
      (if i = j then 8 / 25 else 0) +
      (if i.val = j.val + 1 then 16 / 25 else 0) +
      (if j.val = i.val + 1 then 1 / 25 else 0) := by
  simp only [endpointKilled, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    endpointGradient_mul_apply, endpointDifference, Matrix.one_apply,
    Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

/-- Exact intertwining of the physical cell walk with the killed edge walk. -/
theorem endpointGradient_intertwines (c : ℕ) :
    endpointGradient c * endpointMarkov c = endpointKilled c * endpointGradient c := by
  simp only [endpointMarkov, endpointKilled, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem endpointDifference_intertwines (c : ℕ) :
    endpointMarkov c * endpointDifference c = endpointDifference c * endpointKilled c := by
  simp only [endpointMarkov, endpointKilled, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem endpointGradient_intertwines_pow (c s : ℕ) :
    endpointGradient c * endpointMarkov c ^ s = endpointKilled c ^ s * endpointGradient c := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, endpointGradient_intertwines,
      ← Matrix.mul_assoc, ← pow_succ]

theorem endpointDifference_intertwines_pow (c s : ℕ) :
    endpointMarkov c ^ s * endpointDifference c = endpointDifference c * endpointKilled c ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, endpointDifference_intertwines,
      Matrix.mul_assoc, ← pow_succ']

/-- Exact past factor, with physical t = 2s+2 and bond l = 2(a+1). -/
noncomputable def endpointPastFactor (c s : ℕ) (a : Fin c) : ℝ :=
  (4 / 5) * (endpointMarkov c ^ s) a.castSucc 0 -
    (1 / 20) * (endpointMarkov c ^ s) a.succ 0

/-- Exact future factor, with d-t = 2s+2. -/
noncomputable def endpointFutureFactor (c s : ℕ) (a : Fin c) : ℝ :=
  (endpointMarkov c ^ s) (Fin.last c) a.succ -
    (endpointMarkov c ^ s) (Fin.last c) a.castSucc

lemma sum_fin_value (c j : ℕ) (f : Fin c → ℝ) :
    (∑ a : Fin c, if a.val = j then f a else 0) =
      if h : j < c then f ⟨j, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro a _ ha
      have hv : a.val ≠ j := fun he => ha (Fin.ext he)
      simp [hv]
    · simp
  · apply Finset.sum_eq_zero
    intro a _
    have hv : a.val ≠ j := by intro he; have := a.isLt; omega
    simp [hv]

lemma endpointDifference_mul_apply {c : ℕ} {J : Type*} [Fintype J]
    (A : Matrix (Fin c) J ℝ) (i : Fin (c + 1)) (j : J) :
    (endpointDifference c * A) i j =
      (if h : 0 < i.val then A ⟨i.val - 1, by omega⟩ j else 0) -
      (if h : i.val < c then A ⟨i.val, h⟩ j else 0) := by
  simp only [Matrix.mul_apply, endpointDifference, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_sub_distrib]
  congr 1
  · by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      have he (a : Fin c) : i = a.succ ↔ a.val = i.val - 1 := by
        rw [Fin.ext_iff]
        simp only [Fin.val_succ]
        omega
      simp_rw [he]
      rw [sum_fin_value]
      simp [show i.val - 1 < c by omega]
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro a _
      have he : i ≠ a.succ := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ] at hv
        omega
      simp [he]
  · have he (a : Fin c) : i = a.castSucc ↔ a.val = i.val := by
      rw [Fin.ext_iff]
      simp only [Fin.coe_castSucc]
      omega
    simp_rw [he]
    exact sum_fin_value c i.val (fun a => A a j)

set_option maxHeartbeats 1000000 in
/-- Explicit reflecting birth-death matrix, including the one-cell chain. -/
theorem endpointMarkov_apply (c : ℕ) (i j : Fin (c + 1)) :
    endpointMarkov c i j =
      (if i = j then (8 / 25 : ℝ) + (if i.val = 0 then 1 / 25 else 0) +
        (if i.val = c then 16 / 25 else 0) else 0) +
      (if i.val = j.val + 1 then 16 / 25 else 0) +
      (if j.val = i.val + 1 then 1 / 25 else 0) := by
  simp only [endpointMarkov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    endpointDifference_mul_apply, Matrix.one_apply]
  split_ifs <;>
    (try simp only [endpointGradient, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]) <;>
    (try split_ifs) <;> norm_num <;> omega

/-- Every endpoint transition probability is nonnegative. -/
theorem endpointMarkov_nonneg (c : ℕ) (i j : Fin (c + 1)) :
    0 ≤ endpointMarkov c i j := by
  rw [endpointMarkov_apply]
  positivity

/-- Columns are probability distributions, including at both boundaries. -/
theorem endpointMarkov_column_sum (c : ℕ) (j : Fin (c + 1)) :
    (∑ i : Fin (c + 1), endpointMarkov c i j) = 1 := by
  have hE (a : Fin c) : (∑ i : Fin (c + 1), endpointDifference c i a) = 0 := by
    simp [endpointDifference, Finset.sum_sub_distrib]
  simp only [endpointMarkov, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hE, zero_mul]
  simp [Matrix.one_apply]

theorem endpointPastFactor_eq_killed (c s : ℕ) (a : Fin (c + 1)) :
    endpointPastFactor (c + 1) s a = (4 / 5) * (endpointKilled (c + 1) ^ s) a 0 := by
  have h := congrArg (fun A : Matrix (Fin (c + 1)) (Fin (c + 2)) ℝ => A a 0)
    (endpointGradient_intertwines_pow (c + 1) s)
  dsimp only at h
  rw [endpointGradient_mul_apply] at h
  change endpointPastFactor (c + 1) s a = _ at h
  rw [h]
  have hD (j : Fin (c + 1)) : endpointGradient (c + 1) j 0 =
      if j = 0 then 4 / 5 else 0 := by
    have he : (0 : Fin (c + 2)) = j.castSucc ↔ j = 0 := by
      constructor
      · intro h
        apply Fin.ext
        exact (congrArg Fin.val h).symm
      · rintro rfl
        rfl
    have hn : (0 : Fin (c + 2)) ≠ j.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at hv
      omega
    simp only [endpointGradient, he, if_neg hn, sub_zero]
  rw [Matrix.mul_apply]
  simp_rw [hD, mul_ite, mul_zero]
  simp
  ring

theorem endpointFutureFactor_eq_killed (c s : ℕ) (a : Fin (c + 1)) :
    endpointFutureFactor (c + 1) s a = (endpointKilled (c + 1) ^ s) (Fin.last c) a := by
  have h := congrArg (fun A : Matrix (Fin (c + 2)) (Fin (c + 1)) ℝ => A (Fin.last (c + 1)) a)
    (endpointDifference_intertwines_pow (c + 1) s)
  dsimp only at h
  rw [mul_endpointDifference_apply] at h
  change endpointFutureFactor (c + 1) s a = _ at h
  rw [h, endpointDifference_mul_apply]
  simp
  rfl

end Fluctuations
