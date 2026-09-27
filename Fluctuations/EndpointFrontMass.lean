import Fluctuations.EndpointPropagation
import Fluctuations.BinomialLocalBounds

namespace Fluctuations

lemma endpointChoose_predecessor_mul (M r : ℕ) (hr : r ≤ M) :
    endpointChoose M ((r : ℤ) - 1) * ((M : ℝ) - r + 1) =
      (M.choose r : ℝ) * r := by
  cases r with
  | zero => simp [endpointChoose]
  | succ r =>
    have h := Nat.choose_succ_right_eq M r
    have hr' : r ≤ M := by omega
    have hc : (M.choose (r + 1) : ℝ) * (r + 1) =
        (M.choose r : ℝ) * ((M : ℝ) - r) := by
      have hc' := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast [Nat.cast_sub hr'] at hc'
      exact hc' 
    rw [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega, endpointChoose_nat]
    push_cast
    nlinarith [hc]

lemma endpointFrontProfile_mass (M r : ℕ) (hr : r ≤ M) :
    endpointFrontProfile M r = endpointBinomialMass M r *
      (((M : ℝ) - 2 * r + 1) / ((M : ℝ) - r + 1)) := by
  have hcoef := endpointChoose_predecessor_mul M r hr
  have hden : (M : ℝ) - r + 1 ≠ 0 := by
    have : (r : ℝ) ≤ M := by exact_mod_cast hr
    linarith
  have hpow : (5 : ℝ) ^ M = (5 : ℝ) ^ r * (5 : ℝ) ^ (M - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hamp : (4 : ℝ) ^ ((M : ℤ) - r) / (5 : ℝ) ^ M * (M.choose r : ℝ) =
      endpointBinomialMass M r := by
    rw [← Nat.cast_sub hr, zpow_natCast]
    unfold endpointBinomialMass
    rw [div_pow, div_pow, one_pow, hpow]
    ring
  unfold endpointFrontProfile
  rw [endpointChoose_nat, ← hamp]
  field_simp [hden]
  nlinarith [hcoef]

end Fluctuations
