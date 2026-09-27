import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

namespace Fluctuations

/-- Binomial coefficients with the manuscript's zero convention for negative indices. -/
noncomputable def endpointChoose (m : ℕ) (r : ℤ) : ℝ :=
  if 0 ≤ r then (m.choose r.toNat : ℝ) else 0

@[simp] lemma endpointChoose_nat (m r : ℕ) :
    endpointChoose m r = (m.choose r : ℝ) := by simp [endpointChoose]

lemma endpointChoose_neg (m : ℕ) {r : ℤ} (hr : r < 0) : endpointChoose m r = 0 := by
  simp [endpointChoose, not_le.mpr hr]

lemma endpointChoose_gt (m : ℕ) {r : ℤ} (hr : (m : ℤ) < r) : endpointChoose m r = 0 := by
  have hp : 0 ≤ r := by omega
  have hn : m < r.toNat := by omega
  simp [endpointChoose, hp, Nat.choose_eq_zero_of_lt hn]

/-- Pascal's identity is valid at every integer coefficient index. -/
lemma endpointChoose_succ (m : ℕ) (r : ℤ) :
    endpointChoose (m + 1) r = endpointChoose m r + endpointChoose m (r - 1) := by
  by_cases hr : r < 0
  · rw [endpointChoose_neg _ hr, endpointChoose_neg _ hr,
      endpointChoose_neg _ (show r - 1 < 0 by omega)]
    simp
  · have hr' : 0 ≤ r := by omega
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr'
    cases r with
    | zero => simp [endpointChoose]
    | succ r =>
      rw [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega]
      change ((m + 1).choose (r + 1) : ℝ) =
        (m.choose (r + 1) : ℝ) + (m.choose r : ℝ)
      rw [Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- Reflection symmetry includes all out-of-range coefficient indices. -/
lemma endpointChoose_symm (m : ℕ) (r : ℤ) :
    endpointChoose m r = endpointChoose m ((m : ℤ) - r) := by
  by_cases hr : r < 0
  · rw [endpointChoose_neg _ hr, endpointChoose_gt _ (show (m : ℤ) < m - r by omega)]
  · by_cases hm : (m : ℤ) < r
    · rw [endpointChoose_gt _ hm, endpointChoose_neg _ (show (m : ℤ) - r < 0 by omega)]
    · have hr' : 0 ≤ r := by omega
      have hm' : r.toNat ≤ m := by omega
      have he : (m : ℤ) - r = ((m - r.toNat : ℕ) : ℤ) := by omega
      rw [he, endpointChoose_nat]
      simp only [endpointChoose, hr', ↓reduceIte]
      exact_mod_cast (Nat.choose_symm hm').symm

/-- The absorbing half-line kernel, written as a weighted ballot difference.
The coordinate a is one-based: boundary a=0, initial point a=1. -/
noncomputable def endpointBallotKernel (s : ℕ) (a : ℤ) : ℝ :=
  (4 : ℝ) ^ (a - 1) * (4 / 25 : ℝ) ^ s *
    (endpointChoose (2 * s) ((s : ℤ) - a + 1) -
      endpointChoose (2 * s) ((s : ℤ) - a - 1))

lemma endpointBallotKernel_boundary (s : ℕ) : endpointBallotKernel s 0 = 0 := by
  have h := endpointChoose_symm (2 * s) ((s : ℤ) + 1)
  have he : ((2 * s : ℕ) : ℤ) - ((s : ℤ) + 1) = (s : ℤ) - 1 := by omega
  rw [he] at h
  simp [endpointBallotKernel, h]

lemma endpointBallotKernel_outside (s : ℕ) {a : ℤ} (ha : (s : ℤ) + 1 < a) :
    endpointBallotKernel s a = 0 := by
  rw [endpointBallotKernel, endpointChoose_neg _ (show (s : ℤ) - a + 1 < 0 by omega),
    endpointChoose_neg _ (show (s : ℤ) - a - 1 < 0 by omega)]
  ring

lemma endpointBallotKernel_zero {a : ℤ} (ha : 1 ≤ a) :
    endpointBallotKernel 0 a = if a = 1 then 1 else 0 := by
  by_cases h : a = 1
  · subst a
    norm_num [endpointBallotKernel, endpointChoose]
  · rw [if_neg h]
    exact endpointBallotKernel_outside 0 (by omega)

lemma endpointChoose_add_two (m : ℕ) (r : ℤ) :
    endpointChoose (m + 2) r = endpointChoose m r +
      2 * endpointChoose m (r - 1) + endpointChoose m (r - 2) := by
  rw [show m + 2 = (m + 1) + 1 by omega, endpointChoose_succ,
    endpointChoose_succ, endpointChoose_succ]
  rw [show r - 1 - 1 = r - 2 by omega]
  ring

/-- The ballot expression solves the actual killed-walk recurrence. -/
lemma endpointBallotKernel_succ (s : ℕ) (a : ℤ) :
    endpointBallotKernel (s + 1) a =
      (16 / 25) * endpointBallotKernel s (a - 1) +
      (8 / 25) * endpointBallotKernel s a +
      (1 / 25) * endpointBallotKernel s (a + 1) := by
  have hpowlo : (4 : ℝ) ^ (a - 1 - 1) = (4 : ℝ) ^ (a - 1) / 4 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  have hpowhi : (4 : ℝ) ^ (a + 1 - 1) = (4 : ℝ) ^ (a - 1) * 4 := by
    rw [show a + 1 - 1 = (a - 1) + 1 by omega, zpow_add₀ (by norm_num)]
    norm_num
  simp only [endpointBallotKernel, hpowlo, hpowhi, pow_succ, Nat.cast_add,
    Nat.cast_one]
  rw [show 2 * (s + 1) = 2 * s + 2 by omega]
  rw [endpointChoose_add_two, endpointChoose_add_two]
  have h1 : (s : ℤ) + 1 - a + 1 = (s : ℤ) - a + 2 := by omega
  have h2 : (s : ℤ) + 1 - a - 1 = (s : ℤ) - a := by omega
  have h3 : (s : ℤ) - (a - 1) + 1 = (s : ℤ) - a + 2 := by omega
  have h4 : (s : ℤ) - (a - 1) - 1 = (s : ℤ) - a := by omega
  have h5 : (s : ℤ) - (a + 1) + 1 = (s : ℤ) - a := by omega
  have h6 : (s : ℤ) - (a + 1) - 1 = (s : ℤ) - a - 2 := by omega
  rw [h1, h2, h3, h4, h5, h6]
  rw [show (s : ℤ) - a + 2 - 1 = (s : ℤ) - a + 1 by omega,
    show (s : ℤ) - a + 2 - 2 = (s : ℤ) - a by omega]
  ring

/-- Exact discrete front profile, using zero-extended binomial coefficients. -/
noncomputable def endpointFrontProfile (M : ℕ) (r : ℤ) : ℝ :=
  (4 : ℝ) ^ ((M : ℤ) - r) / (5 : ℝ) ^ M *
    (endpointChoose M r - endpointChoose M (r - 1))

lemma endpointFrontProfile_ballot (s : ℕ) (a : ℤ) :
    endpointFrontProfile (2 * s + 1) ((s : ℤ) - a + 1) =
      (4 / 5) * endpointBallotKernel s a := by
  unfold endpointFrontProfile endpointBallotKernel
  rw [endpointChoose_succ, endpointChoose_succ]
  rw [show (s : ℤ) - a + 1 - 1 - 1 = (s : ℤ) - a - 1 by omega]
  have hpower : (4 : ℝ) ^ (((2 * s + 1 : ℕ) : ℤ) - ((s : ℤ) - a + 1)) =
      (4 : ℝ) ^ s * (4 : ℝ) ^ (a - 1) * 4 := by
    rw [show (((2 * s + 1 : ℕ) : ℤ) - ((s : ℤ) - a + 1)) =
      ((s : ℤ) + (a - 1)) + 1 by omega]
    rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast]
    norm_num
  rw [hpower, pow_add, pow_mul, div_pow]
  norm_num
  ring

end Fluctuations
