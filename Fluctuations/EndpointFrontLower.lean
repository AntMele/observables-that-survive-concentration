import Fluctuations.EndpointFrontMass
import Fluctuations.EndpointEye

namespace Fluctuations

/-- The exact integer-indexed ballot profile inherits the proved local
binomial lower bound on an actual front segment. -/
theorem EndpointSegmentBounds.profile_lower {n c ℓ t : ℝ} {M : ℕ} {r : ℤ}
    (h : EndpointSegmentBounds n c ℓ t) (hn : 0 < n) (hc : 0 ≤ c)
    (hM : (M : ℝ) = t - 1) (hr : (r : ℝ) = (t - ℓ) / 2) :
    endpointFrontConstant c / Real.sqrt n ≤ endpointFrontProfile M r := by
  have hrpos : (0 : ℝ) < r := by rw [hr]; exact h.index_pos
  have hr0 : 0 ≤ r := by exact_mod_cast hrpos.le
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  norm_cast at hrpos hr ⊢
  have hrM : r ≤ M := by
    apply Nat.cast_le (α := ℝ) |>.mp
    rw [hr,hM]
    exact h.index_lt.le
  rw [endpointFrontProfile_mass M r hrM]
  have he : ((M : ℝ) - 2 * r + 1) / ((M : ℝ) - r + 1) =
      2 * ℓ / (t + ℓ) := by
    have hden : t + ℓ ≠ 0 := by
      have := h.time_lower
      have := h.space_lower
      linarith
    rw [hM,hr]
    apply (div_eq_div_iff (show t - 1 - (t - ℓ) / 2 + 1 ≠ 0 by
      intro hh
      apply hden
      linarith) hden).mpr
    ring
  rw [he]
  exact h.front_lower hn hc hM hr

/-- Actual past Q-power sensitivity is at least C/sqrt(n) on any segment
satisfying the proved eye geometry. -/
theorem endpointPastFactor_lower_of_segment (c s : ℕ) (i : Fin (c + 1))
    {C : ℝ} (hC : 0 ≤ C)
    (h : EndpointSegmentBounds (2 * (c + 2)) C
      (2 * (i.val + 1)) (2 * (s + 1))) :
    endpointFrontConstant C / Real.sqrt (2 * (c + 2)) ≤
      endpointPastFactor (c + 1) s i := by
  have hfront : s + i.val < 2 * (c + 1) := by
    have hh := h.no_reflection
    have hh' : (s : ℝ) + i.val < 2 * (c + 1) := by linarith
    exact_mod_cast hh'
  rw [endpointPastFactor_frontProfile c s i hfront]
  apply h.profile_lower (by positivity) hC
  · push_cast
    ring
  · push_cast
    ring

/-- Actual future Q-power sensitivity is at least (5/4) C/sqrt(n), with the
normalization required by the endpoint one-gate identity. -/
theorem endpointFutureFactor_lower_of_segment (c s : ℕ) (i : Fin (c + 1))
    {C : ℝ} (hC : 0 ≤ C)
    (h : EndpointSegmentBounds (2 * (c + 2)) C
      (2 * (c + 2) - 2 * (i.val + 1)) (2 * (s + 1))) :
    (5 / 4) * (endpointFrontConstant C / Real.sqrt (2 * (c + 2))) ≤
      endpointFutureFactor (c + 1) s i := by
  have hfront : s < c + i.val + 2 := by
    have hh := h.no_reflection
    have hh' : (s : ℝ) < c + i.val + 2 := by linarith
    exact_mod_cast hh'
  rw [endpointFutureFactor_frontProfile c s i hfront]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply h.profile_lower (by positivity) hC
  · push_cast
    ring
  · push_cast
    ring

/-- Both exact propagation factors of every concrete even gate in the eye
have the required inverse-square-root lower bounds.  Here there are c+2
endpoint cells, d=2T layers, and the gate is at bond 2(i+1), layer 2(s+1). -/
theorem endpointEye_factors_lower (c T s : ℕ) (i : Fin (c + 1)) {C : ℝ}
    (hC : 0 ≤ C) (hlarge : 12 * (C + 2) ≤ Real.sqrt (2 * (c + 2)))
    (hfront : |(2 * T : ℝ) - 5 * (2 * (c + 2)) / 3| ≤
      C * Real.sqrt (2 * (c + 2)))
    (hz : (⟨(i.val : ℤ) + 1, (s : ℤ) + 1⟩ : Σ _ : ℤ, ℤ) ∈
      endpointEye (2 * (c + 2)) (2 * T)) :
    endpointFrontConstant C / Real.sqrt (2 * (c + 2)) ≤
        endpointPastFactor (c + 1) s i ∧
      (5 / 4) * (endpointFrontConstant C / Real.sqrt (2 * (c + 2))) ≤
        endpointFutureFactor (c + 1) (T - s - 2) i := by
  have hb := endpointEye_segmentBounds (n := 2 * (c + 2)) (d := 2 * T)
    hC (by simpa using hlarge) (by simpa using hfront) hz
  push_cast at hb
  obtain ⟨hP,hF⟩ := hb
  constructor
  · exact endpointPastFactor_lower_of_segment c s i hC hP
  · have hsT : s + 2 ≤ T := by
      have ht := hF.time_lower
      have hh : (s : ℝ) + 1 < T := by
        have hc0 : (0 : ℝ) ≤ c := by positivity
        linarith
      have hh' : s + 1 < T := by exact_mod_cast hh
      omega
    have htime : (2 : ℝ) * ((T - s - 2 : ℕ) + 1) = 2 * T - 2 * (s + 1) := by
      rw [Nat.cast_sub (by omega : 2 ≤ T - s), Nat.cast_sub (by omega : s ≤ T)]
      push_cast
      ring
    apply endpointFutureFactor_lower_of_segment c (T - s - 2) i hC
    rw [htime]
    exact hF

end Fluctuations
