import Fluctuations.EndpointImages

open scoped BigOperators Matrix
namespace Fluctuations

/-- Each increase in the right-boundary cell mass is an exact killed-walk
boundary flux. This identity includes both reflecting boundaries in Q. -/
theorem endpointMarkov_last_succ (c s : ℕ) :
    (endpointMarkov (c + 1) ^ (s + 1)) (Fin.last (c + 1)) 0 =
      (endpointMarkov (c + 1) ^ s) (Fin.last (c + 1)) 0 +
      (16 / 25) * (endpointKilled (c + 1) ^ s) (Fin.last c) 0 := by
  rw [pow_succ']
  conv_lhs =>
    rw [endpointMarkov, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc,
      endpointDifference_mul_apply]
  simp only [Fin.val_last, show 0 < c + 1 by omega, ↓reduceDIte, Nat.add_sub_cancel,
    lt_self_iff_false, sub_zero]
  rw [endpointGradient_mul_apply]
  change (endpointMarkov (c + 1) ^ s) (Fin.last (c + 1)) 0 +
    (4 / 5) * endpointPastFactor (c + 1) s (Fin.last c) = _
  rw [endpointPastFactor_eq_killed]
  ring

/-- Exact finite-time endpoint transition probability as accumulated boundary flux. -/
theorem endpointMarkov_last_sum (c s : ℕ) :
    (endpointMarkov (c + 1) ^ s) (Fin.last (c + 1)) 0 =
      (16 / 25) * ∑ u ∈ Finset.range s,
        (endpointKilled (c + 1) ^ u) (Fin.last c) 0 := by
  induction s with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Finset.range_zero, Finset.sum_empty, mul_zero]
    rw [if_neg]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  | succ s ih =>
    rw [endpointMarkov_last_succ, ih, Finset.sum_range_succ]
    ring

/-- All-depth exact image-sum expression for the right endpoint probability.
The image kernels consist entirely of explicit binomial coefficients. -/
theorem endpointMarkov_last_images (c s : ℕ) :
    (endpointMarkov (c + 1) ^ s) (Fin.last (c + 1)) 0 =
      (16 / 25) * ∑ u ∈ Finset.range s,
        endpointImageKernel (c + 2) u ((c : ℤ) + 1) := by
  rw [endpointMarkov_last_sum]
  simp_rw [endpointKilled_pow_images]
  rfl

/-- The endpoint-chain expression for the averaged OTOC at physical depth
2(s+1). Its identification with the quantum circuit uses the separate Haar
Pauli-to-endpoint reduction. -/
noncomputable def endpointChainMean (c s : ℕ) : ℝ :=
  1 - (16 / 15) * (endpointMarkov (c + 1) ^ s) (Fin.last (c + 1)) 0

/-- An exact all-depth binomial image formula for the endpoint-chain mean. -/
theorem endpointChainMean_images (c s : ℕ) :
    endpointChainMean c s = 1 - (256 / 375) *
      ∑ u ∈ Finset.range s, endpointImageKernel (c + 2) u ((c : ℤ) + 1) := by
  rw [endpointChainMean, endpointMarkov_last_images]
  ring

/-- The exact finite-chain mean is one before the endpoint light cone arrives. -/
theorem endpointChainMean_lightcone (c s : ℕ) (hlight : s < c + 1) :
    endpointChainMean c s = 1 := by
  rw [endpointChainMean, endpointMarkov_last_sum]
  have hz : (∑ u ∈ Finset.range s,
      (endpointKilled (c + 1) ^ u) (Fin.last c) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [endpointKilled_pow_ballot c u (Fin.last c) (by simp; omega)]
    apply endpointBallotKernel_outside
    simp only [Fin.val_last]
    omega
  rw [hz]
  ring

/-- Endpoint-chain mean for every even physical depth 2T and every positive
number c+1 of cells, including the depth-zero and one-cell boundary cases. -/
noncomputable def endpointEvenMean (c : ℕ) : ℕ → ℝ
  | 0 => 1
  | s + 1 => 1 - (16 / 15) * (endpointMarkov c ^ s) (Fin.last c) 0

@[simp] theorem endpointEvenMean_zero (c : ℕ) : endpointEvenMean c 0 = 1 := rfl

theorem endpointMarkov_zero : endpointMarkov 0 = 1 := by
  ext i j
  simp [endpointMarkov]

/-- A single cell is randomized by its first odd gate and then remains at
its global two-qubit Haar mean at every positive even depth. -/
theorem endpointEvenMean_oneCell (s : ℕ) : endpointEvenMean 0 (s + 1) = -1 / 15 := by
  simp [endpointEvenMean, endpointMarkov_zero]
  norm_num

/-- All remaining even-size, positive-depth cases are covered by the proved
finite-interval image formula. -/
theorem endpointEvenMean_images (c s : ℕ) :
    endpointEvenMean (c + 1) (s + 1) = 1 - (256 / 375) *
      ∑ u ∈ Finset.range s, endpointImageKernel (c + 2) u ((c : ℤ) + 1) :=
  endpointChainMean_images c s

end Fluctuations
