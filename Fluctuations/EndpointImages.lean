import Fluctuations.EndpointPropagation
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Int.Interval

open scoped BigOperators Matrix
namespace Fluctuations

lemma endpointImage_zero_outside (L s : ℕ) (hL : 0 < L) (x m : ℤ)
    (hm : m ∉ Finset.Icc (-(s : ℤ) - |x| - 1) ((s : ℤ) + |x| + 1)) :
    endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m) = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hm
  have hLi : (1 : ℤ) ≤ L := by omega
  have hx₁ := le_abs_self x
  have hx₂ := neg_abs_le x
  have hx₀ := abs_nonneg x
  rcases hm with hm | hm
  · apply endpointChoose_neg
    have hm0 : m < 0 := by omega
    nlinarith
  · apply endpointChoose_gt
    have hm0 : 0 < m := by omega
    push_cast
    nlinarith

lemma endpointImage_summable (L s : ℕ) (hL : 0 < L) (x : ℤ) :
    Summable (fun m : ℤ => endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m)) :=
  summable_of_ne_finset_zero (endpointImage_zero_outside L s hL x)

/-- Periodized even-binomial kernel. The series has finite support at each
finite time; it is written as a tsum solely to make image reindexing exact. -/
noncomputable def endpointPeriodicChoose (L s : ℕ) (x : ℤ) : ℝ :=
  ∑' m : ℤ, endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m)

/-- Every image series is a genuinely finite, explicitly bounded sum. -/
lemma endpointPeriodicChoose_finite (L s : ℕ) (hL : 0 < L) (x : ℤ) :
    endpointPeriodicChoose L s x =
      ∑ m ∈ Finset.Icc (-(s : ℤ) - |x| - 1) ((s : ℤ) + |x| + 1),
        endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m) :=
  tsum_eq_sum (endpointImage_zero_outside L s hL x)

lemma endpointPeriodicChoose_even (L s : ℕ) (x : ℤ) :
    endpointPeriodicChoose L s (-x) = endpointPeriodicChoose L s x := by
  unfold endpointPeriodicChoose
  calc
    _ = ∑' m : ℤ, endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * (-m)) := by
      apply tsum_congr
      intro m
      rw [endpointChoose_symm]
      congr 1
      push_cast
      ring
    _ = _ := by
      simpa using ((Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m)))

lemma endpointPeriodicChoose_period (L s : ℕ) (x : ℤ) :
    endpointPeriodicChoose L s (x + 2 * L) = endpointPeriodicChoose L s x := by
  unfold endpointPeriodicChoose
  calc
    _ = ∑' m : ℤ, endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * (m - 1)) := by
      apply tsum_congr
      intro m
      congr 1
      ring
    _ = _ := by
      simpa [sub_eq_add_neg] using ((Equiv.addRight (-1 : ℤ)).tsum_eq
        (fun m : ℤ => endpointChoose (2 * s) ((s : ℤ) - x + 2 * L * m)))

lemma endpointPeriodicChoose_succ (L s : ℕ) (hL : 0 < L) (x : ℤ) :
    endpointPeriodicChoose L (s + 1) x = endpointPeriodicChoose L s (x - 1) +
      2 * endpointPeriodicChoose L s x + endpointPeriodicChoose L s (x + 1) := by
  unfold endpointPeriodicChoose
  have h1 := endpointImage_summable L s hL (x - 1)
  have h2 := (endpointImage_summable L s hL x).mul_left 2
  have h3 := endpointImage_summable L s hL (x + 1)
  rw [← tsum_mul_left, ← h1.tsum_add h2, ← (h1.add h2).tsum_add h3]
  apply tsum_congr
  intro m
  rw [show 2 * (s + 1) = 2 * s + 2 by omega, endpointChoose_add_two]
  push_cast
  congr 2 <;> congr 1 <;> ring_nf

lemma endpointPeriodicChoose_zero (L : ℕ) (hL : 0 < L) (x : ℤ)
    (hx0 : 0 ≤ x) (hxL : x < 2 * L) :
    endpointPeriodicChoose L 0 x = if x = 0 then 1 else 0 := by
  unfold endpointPeriodicChoose
  rw [tsum_eq_single (0 : ℤ)]
  · by_cases hx : x = 0
    · subst x
      norm_num [endpointChoose]
    · rw [if_neg hx]
      apply endpointChoose_neg
      simp only [Nat.cast_zero, zero_sub, mul_zero, add_zero]
      omega
  · intro m hm
    by_cases hm0 : m < 0
    · apply endpointChoose_neg
      simp only [Nat.cast_zero, zero_sub]
      have hLi : (0 : ℤ) < L := by omega
      nlinarith
    · apply endpointChoose_gt
      simp only [mul_zero, Nat.cast_zero, zero_sub]
      have hm1 : 1 ≤ m := by omega
      have hLi : (0 : ℤ) < L := by omega
      nlinarith

/-- Exact absorbing interval kernel from its first site. Boundaries are 0,L. -/
noncomputable def endpointImageKernel (L s : ℕ) (a : ℤ) : ℝ :=
  (4 : ℝ) ^ (a - 1) * (4 / 25 : ℝ) ^ s *
    (endpointPeriodicChoose L s (a - 1) - endpointPeriodicChoose L s (a + 1))

lemma endpointImageKernel_left (L s : ℕ) : endpointImageKernel L s 0 = 0 := by
  unfold endpointImageKernel
  norm_num only
  rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, endpointPeriodicChoose_even]
  ring

lemma endpointImageKernel_right (L s : ℕ) : endpointImageKernel L s L = 0 := by
  have he : endpointPeriodicChoose L s ((L : ℤ) + 1) =
      endpointPeriodicChoose L s ((L : ℤ) - 1) := by
    rw [← endpointPeriodicChoose_even L s ((L : ℤ) + 1)]
    rw [← endpointPeriodicChoose_period L s (-((L : ℤ) + 1))]
    congr 1
    ring
  simp [endpointImageKernel, he]

lemma endpointImageKernel_zero (L : ℕ) (hL : 1 < L) (a : ℤ)
    (ha0 : 1 ≤ a) (haL : a < L) :
    endpointImageKernel L 0 a = if a = 1 then 1 else 0 := by
  unfold endpointImageKernel
  rw [endpointPeriodicChoose_zero L (by omega) (a - 1) (by omega) (by omega),
    endpointPeriodicChoose_zero L (by omega) (a + 1) (by omega) (by omega)]
  by_cases ha : a = 1
  · subst a
    norm_num
  · simp [show a - 1 ≠ 0 by omega, show a + 1 ≠ 0 by omega, ha]

lemma endpointImageKernel_succ (L s : ℕ) (hL : 0 < L) (a : ℤ) :
    endpointImageKernel L (s + 1) a =
      (16 / 25) * endpointImageKernel L s (a - 1) +
      (8 / 25) * endpointImageKernel L s a +
      (1 / 25) * endpointImageKernel L s (a + 1) := by
  have hpowlo : (4 : ℝ) ^ (a - 1 - 1) = (4 : ℝ) ^ (a - 1) / 4 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  have hpowhi : (4 : ℝ) ^ (a + 1 - 1) = (4 : ℝ) ^ (a - 1) * 4 := by
    rw [show a + 1 - 1 = (a - 1) + 1 by omega, zpow_add₀ (by norm_num)]
    norm_num
  simp only [endpointImageKernel, hpowlo, hpowhi, pow_succ]
  rw [endpointPeriodicChoose_succ L s hL, endpointPeriodicChoose_succ L s hL]
  rw [show a - 1 + 1 = a by omega, show a + 1 - 1 = a by omega]
  ring

/-- All-depth exact finite-interval image formula for the actual killed matrix.
Both absorbing boundary conditions are included, so no front restriction remains. -/
theorem endpointKilled_pow_images (c s : ℕ) (i : Fin (c + 1)) :
    (endpointKilled (c + 1) ^ s) i 0 =
      endpointImageKernel (c + 2) s ((i.val : ℤ) + 1) := by
  induction s generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply,
      endpointImageKernel_zero (c + 2) (by omega) _ (by omega) (by have := i.isLt; omega)]
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
    rw [pow_succ', endpointKilled_mul_apply, endpointImageKernel_succ _ _ (by omega)]
    rw [ih i]
    have hlo : (if h : 0 < i.val then
        (endpointKilled (c + 1) ^ s) ⟨i.val - 1, by omega⟩ 0 else 0) =
        endpointImageKernel (c + 2) s ((i.val : ℤ) + 1 - 1) := by
      split_ifs with hi
      · rw [ih]
        congr 1
        simp only
        omega
      · have hi0 : i.val = 0 := by omega
        simp [hi0, endpointImageKernel_left]
    have hhi : (if h : i.val + 1 < c + 1 then
        (endpointKilled (c + 1) ^ s) ⟨i.val + 1, h⟩ 0 else 0) =
        endpointImageKernel (c + 2) s ((i.val : ℤ) + 1 + 1) := by
      split_ifs with hi
      · rw [ih]
        congr 1
      · have he : (i.val : ℤ) + 1 + 1 = (c + 2 : ℕ) := by have := i.isLt; omega
        rw [he, endpointImageKernel_right]
    rw [hlo,hhi]
    ring

end Fluctuations
