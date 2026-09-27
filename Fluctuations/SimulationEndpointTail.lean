import Fluctuations.SimulationTailBinomial
import Fluctuations.PauliBrickwork

open scoped BigOperators Matrix

namespace Fluctuations

/-- Probability that the actual reflecting endpoint-cell chain, started in
cell zero, is in a cell of index at least `a` after `s` periods. -/
noncomputable def simulationEndpointTail (c s a : ℕ) : ℝ :=
  ∑ i : Fin (c + 1), (endpointMarkov c ^ s) i 0 * (if a ≤ i.val then 1 else 0)

lemma simulationEndpointPower_nonneg (c s : ℕ) (i j : Fin (c + 1)) :
    0 ≤ (endpointMarkov c ^ s) i j := by
  induction s generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ s ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (endpointMarkov_nonneg c i k) (ih k j))

lemma simulationEndpointPower_sum (c s : ℕ) (j : Fin (c + 1)) :
    (∑ i : Fin (c + 1), (endpointMarkov c ^ s) i j) = 1 := by
  induction s with
  | zero => simp [Matrix.one_apply]
  | succ s ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, endpointMarkov_column_sum, one_mul]
    exact ih

lemma simulationEndpointTail_nonneg (c s a : ℕ) : 0 ≤ simulationEndpointTail c s a := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (simulationEndpointPower_nonneg c s i 0) (by split_ifs <;> norm_num)

lemma simulationEndpointTail_le_one (c s a : ℕ) : simulationEndpointTail c s a ≤ 1 := by
  rw [← simulationEndpointPower_sum c s (0 : Fin (c + 1))]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · simp
  · simpa using simulationEndpointPower_nonneg c s i 0

@[simp] lemma simulationEndpointTail_left (c s : ℕ) : simulationEndpointTail c s 0 = 1 := by
  simp [simulationEndpointTail, simulationEndpointPower_sum]

lemma simulationEndpointTail_outside (c s a : ℕ) (ha : c < a) :
    simulationEndpointTail c s a = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : ¬a ≤ i.val := by omega
  simp [hi]

@[simp] lemma simulationEndpointTail_initial (c a : ℕ) :
    simulationEndpointTail c 0 a = if a = 0 then 1 else 0 := by
  simp only [simulationEndpointTail, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

lemma simulationEndpointTail_column (c a : ℕ) (ha : 0 < a) (hac : a ≤ c)
    (j : Fin (c + 1)) :
    (∑ i : Fin (c + 1), endpointMarkov c i j * (if a ≤ i.val then 1 else 0)) =
      (16 / 25 : ℝ) * (if a - 1 ≤ j.val then 1 else 0) +
      (8 / 25 : ℝ) * (if a ≤ j.val then 1 else 0) +
      (1 / 25 : ℝ) * (if a + 1 ≤ j.val then 1 else 0) := by
  rw [endpointMarkov_sum_column]
  dsimp only
  split_ifs <;> norm_num <;> omega

/-- Exact tail recursion at every interior threshold, including thresholds
adjacent to either reflecting boundary. -/
theorem simulationEndpointTail_succ (c s a : ℕ) (ha : 0 < a) (hac : a ≤ c) :
    simulationEndpointTail c (s + 1) a =
      (16 / 25) * simulationEndpointTail c s (a - 1) +
      (8 / 25) * simulationEndpointTail c s a +
      (1 / 25) * simulationEndpointTail c s (a + 1) := by
  calc
    simulationEndpointTail c (s + 1) a =
        ∑ j : Fin (c + 1), (endpointMarkov c ^ s) j 0 *
          (∑ i : Fin (c + 1), endpointMarkov c i j * (if a ≤ i.val then 1 else 0)) := by
      simp only [simulationEndpointTail, pow_succ', Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [simulationEndpointTail_column c a ha hac]
      simp only [simulationEndpointTail, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      simp only [mul_left_comm]

/-- Uniform comparison with the lower binomial CDF. Both finite reflecting
boundaries are included; no assumption excludes paths hitting a boundary. -/
theorem simulationEndpointTail_binomial (c s a : ℕ) :
    simulationEndpointTail c s a ≤
      (5 / 4) * simulationBinomialCDF (2 * s + 1) ((s : ℤ) - a) := by
  induction s generalizing a with
  | zero =>
    by_cases ha : a = 0
    · subst a
      norm_num [simulationBinomialCDF]
    · rw [simulationEndpointTail_initial, if_neg ha]
      exact mul_nonneg (by norm_num) (simulationBinomialCDF_nonneg _ _)
  | succ s ih =>
    by_cases ha : a = 0
    · subst a
      rw [simulationEndpointTail_left]
      simp only [Nat.cast_zero, sub_zero]
      linarith [simulationBinomialCDF_odd_center (s + 1)]
    · by_cases hac : c < a
      · rw [simulationEndpointTail_outside c (s + 1) a hac]
        exact mul_nonneg (by norm_num) (simulationBinomialCDF_nonneg _ _)
      · have hap : 0 < a := by omega
        rw [simulationEndpointTail_succ c s a hap (by omega),
          show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by omega,
          simulationBinomialCDF_add_two]
        have h1 : ((s + 1 : ℕ) : ℤ) - a = (s : ℤ) - (a - 1 : ℕ) := by omega
        have h2 : ((s + 1 : ℕ) : ℤ) - a - 1 = (s : ℤ) - a := by omega
        have h3 : ((s + 1 : ℕ) : ℤ) - a - 2 = (s : ℤ) - (a + 1 : ℕ) := by omega
        rw [h2, h3, h1]
        linarith [ih (a - 1), ih a, ih (a + 1)]

/-- Gaussian upper tail for the genuine finite reflecting endpoint chain. -/
theorem simulationEndpointTail_gaussian (c s a : ℕ)
    (ha : ((s : ℤ) - a : ℝ) ≤ ((2 * s + 1 : ℕ) : ℝ) / 5) :
    simulationEndpointTail c s a ≤ (5 / 4) *
      Real.exp (-2 * (((2 * s + 1 : ℕ) : ℝ) / 5 - ((s : ℤ) - a)) ^ 2 /
        ((2 * s + 1 : ℕ) : ℝ)) := by
  have hb := simulationBinomialCDF_hoeffding (2 * s + 1) (by omega)
    ((s : ℤ) - a) (by simpa using ha)
  have hc := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 5 / 4 by norm_num)
  exact (simulationEndpointTail_binomial c s a).trans (by simpa using hc)

end Fluctuations
