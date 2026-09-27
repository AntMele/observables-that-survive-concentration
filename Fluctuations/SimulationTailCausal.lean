import Fluctuations.SimulationTailPhysical

namespace Fluctuations
noncomputable section

lemma simulationTouching_even_causal (c s : ℕ) (a : Fin c) (ha : s < a.val) :
    simulationTouching (a.castSucc,1) (a.succ,0) (simulationBeforeEven c s) ≤ 0 := by
  have h := (simulationTouching_even_le c s a).trans (simulationEndpointTail_binomial c s a.val)
  rw [simulationBinomialCDF_neg _ (show (s : ℤ)-a.val < 0 by omega)] at h
  simpa using h

lemma simulationTouching_odd_causal (c s : ℕ) (a : Fin (c+1)) (ha : s+1 < a.val) :
    simulationTouching (a,0) (a,1) (simulationBeforeOdd c s) ≤ 0 := by
  have h := (simulationTouching_odd_le c s a).trans (simulationEndpointTail_binomial c s (a.val-1))
  rw [simulationBinomialCDF_neg _ (show (s : ℤ)-(a.val-1 : ℕ) < 0 by omega)] at h
  simpa using h

lemma simulationTouching_initial_causal (c : ℕ) (a : Fin (c+1)) (ha : 0 < a.val) :
    simulationTouching (a,0) (a,1) (pauliInitialVector (brickworkInitialZ c)) = 0 := by
  rw [simulationTouching_initial, if_neg]
  intro he
  have h := congrArg Fin.val he
  change a.val = 0 at h
  omega

/-- Exact forward causal irrelevance, derived from the finite-support
binomial law and the genuine Haar Pauli prefix. -/
theorem simulationForwardTouch_causal (c T : ℕ) (z : Fin (T*(2*c+1)))
    (hcausal : simulationGateTime c T z < simulationGatePosition c T z) :
    simulationForwardTouch c T z = 0 := by
  apply le_antisymm _ (simulationForwardTouch_nonneg c T z)
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [ht,hp] at hcausal
    rw [simulationForwardTouch,hb,hz]
    change simulationTouching (a,0) (a,1) _ ≤ 0
    cases s with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add]
      rw [simulationPrefix_odd_initial c T hs a, simulationTouching_initial_causal c a (by omega)]
    | succ s =>
      rw [simulationPrefix_odd_succ c T s hs a]
      exact simulationTouching_odd_causal c s a (by omega)
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [ht,hp] at hcausal
    rw [simulationForwardTouch,hb,hz]
    change simulationTouching (a.castSucc,1) (a.succ,0) _ ≤ 0
    rw [simulationPrefix_even c T s hs a]
    exact simulationTouching_even_causal c s a (by omega)

/-- Exact backwards causal irrelevance. The final even layer is included,
so its zero virtual time does not need a division-by-zero tail estimate. -/
theorem simulationBackwardTouch_causal (c T : ℕ) (z : Fin (T*(2*c+1)))
    (hcausal : 2*T-simulationGateTime c T z < 2*(c+1)-simulationGatePosition c T z) :
    simulationBackwardTouch c T z = 0 := by
  apply le_antisymm _ (simulationBackwardTouch_nonneg c T z)
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [ht,hp] at hcausal
    rw [simulationBackwardTouch,hb,hz]
    change simulationTouching (a,0) (a,1) _ ≤ 0
    have heP : 2*(c+1)-(2*a.val+1) = 2*a.rev.val+1 := by rw [Fin.val_rev]; omega
    rw [heP] at hcausal
    by_cases hlast : s+1=T
    · subst T
      rw [simulationBackward_odd_last, simulationTouching_initial_causal c a.rev (by omega)]
    · have hmore : s+1<T := by omega
      rw [simulationBackward_odd c T s hmore a]
      exact simulationTouching_odd_causal c (T-s-2) a.rev (by omega)
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [ht,hp] at hcausal
    rw [simulationBackwardTouch,hb,hz]
    change simulationTouching (a.castSucc,1) (a.succ,0) _ ≤ 0
    by_cases hlast : s+1=T
    · subst T
      rw [simulationBackward_even_last]
    · have hmore : s+1<T := by omega
      have heP : 2*(c+1)-(2*a.val+2) = 2*a.rev.val+2 := by rw [Fin.val_rev]; omega
      rw [heP] at hcausal
      rw [simulationBackward_even c T s hmore a]
      exact simulationTouching_even_causal c (T-s-2) a.rev (by omega)

end
end Fluctuations
