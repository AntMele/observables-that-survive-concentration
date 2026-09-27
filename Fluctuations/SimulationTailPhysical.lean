import Fluctuations.SimulationExpectedTouch
import Fluctuations.SimulationGateCoordinates
import Fluctuations.SimulationBackwardAverage

open MeasureTheory
open scoped BigOperators
namespace Fluctuations
noncomputable section

def simulationTouchTail (u v : ℕ) : ℝ :=
  (5/2) * Real.exp (-(max (5*(v:ℝ)-3*(u:ℝ)) 0)^2 / (200*u))

def simulationForwardTouch (c T : ℕ) (z : Fin (T*(2*c+1))) : ℝ :=
  simulationTouching (brickworkCircuitBond c T z.val).1 (brickworkCircuitBond c T z.val).2
    (pauliLayerEvolution ((brickworkGateSchedule c T).take z.val)
      (pauliInitialVector (brickworkInitialZ c)))

def simulationBackwardTouch (c T : ℕ) (z : Fin (T*(2*c+1))) : ℝ :=
  simulationTouching (brickworkCircuitBond c T z.val).1 (brickworkCircuitBond c T z.val).2
    (pauliLayerEvolution ((brickworkGateSchedule c T).drop (z.val+1)).reverse
      (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2)))))

theorem simulationCoordinateMass_expected (c T : ℕ) (z : Fin (T*(2*c+1))) :
    (∫ x, simulationCoordinateMass (brickworkCircuitBond c T) (brickworkInitialZ c)
      (T*(2*c+1)) z x ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationForwardTouch c T z := by
  exact simulationExpected_prefix c T z.val z.isLt.le _ _


theorem simulationBackwardMass_expected (c T : ℕ) (z : Fin (T*(2*c+1))) :
    (∫ x, simulationBackwardMass (brickworkCircuitBond c T) (Fin.last c,(1 : Fin 2))
      (T*(2*c+1)) z x ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationBackwardTouch c T z := by
  let e : Fin z.rev.val → Fin (T*(2*c+1)) := fun i =>
    (⟨i.val,lt_trans i.isLt z.rev.isLt⟩ : Fin (T*(2*c+1))).rev
  have he : Function.Injective e := by
    intro a b hab
    have h := congrArg (fun q : Fin (T*(2*c+1)) => q.rev.val) hab
    simp only [e,Fin.rev_rev] at h
    exact Fin.ext h
  have h := simulationActiveMass_extracted_inv
    (reverseCircuitBond (brickworkCircuitBond c T) (T*(2*c+1)))
    (pauliSiteZ (Fin.last c,(1 : Fin 2)))
    (brickworkCircuitBond c T z.val).1 (brickworkCircuitBond c T z.val).2 e he
  change (∫ x, simulationBackwardMass (brickworkCircuitBond c T) (Fin.last c,(1 : Fin 2))
    (T*(2*c+1)) z x ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) = _ at h
  rw [h]
  have hb : reverseCircuitBond (brickworkCircuitBond c T) (T*(2*c+1)) =
      fun k => brickworkCircuitBond c T (T*(2*c+1)-1-k) := by
    funext k
    unfold reverseCircuitBond
    congr 1
    omega
  rw [hb, Fin.val_rev, show T*(2*c+1)-(z.val+1)=T*(2*c+1)-z.val-1 by omega,
    simulationReverseChronologicalSuffix]
  rfl

lemma simulationForwardTouch_nonneg (c T : ℕ) (z : Fin (T*(2*c+1))) :
    0 ≤ simulationForwardTouch c T z := by
  apply simulationTouching_nonneg
  apply simulationLayer_nonneg
  intro P
  unfold pauliInitialVector
  split_ifs <;> norm_num

lemma simulationBackwardTouch_nonneg (c T : ℕ) (z : Fin (T*(2*c+1))) :
    0 ≤ simulationBackwardTouch c T z := by
  apply simulationTouching_nonneg
  apply simulationLayer_nonneg
  intro P
  unfold pauliInitialVector
  split_ifs <;> norm_num

/-- The all-gate physical forward touching bound, expressed in the actual
one-based layer and bond coordinates of each gate. -/
theorem simulationForwardTouch_gaussian (c T : ℕ) (z : Fin (T*(2*c+1))) :
    simulationForwardTouch c T z ≤
      simulationTouchTail (simulationGateTime c T z) (simulationGatePosition c T z) := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [simulationForwardTouch, hb, hz, ht, hp]
    change simulationTouching (a,0) (a,1) _ ≤ _
    cases s with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [simulationPrefix_odd_initial c T hs a]
      simpa [simulationTouchTail] using simulationTouching_initial_gaussian c a
    | succ s =>
      rw [simulationPrefix_odd_succ c T s hs a]
      have he : 2*(s+1)+1 = 2*s+3 := by omega
      rw [he]
      simpa [simulationTouchTail] using simulationTouching_odd_gaussian c s a
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [simulationForwardTouch, hb, hz, ht, hp]
    change simulationTouching (a.castSucc,1) (a.succ,0) _ ≤ _
    rw [simulationPrefix_even c T s hs a]
    simpa [simulationTouchTail] using simulationTouching_even_gaussian c s a

/-- The all-gate backwards touching bound, with exactly the manuscript's
virtual time `d-t` and reflected distance `n-ell`. -/
theorem simulationBackwardTouch_gaussian (c T : ℕ) (z : Fin (T*(2*c+1)))
    (htd : simulationGateTime c T z < 2*T) :
    simulationBackwardTouch c T z ≤
      simulationTouchTail (2*T-simulationGateTime c T z)
        (2*(c+1)-simulationGatePosition c T z) := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    rw [simulationBackwardTouch, hb, hz, ht, hp]
    change simulationTouching (a,0) (a,1) _ ≤ _
    have heP : 2*(c+1)-(2*a.val+1) = 2*a.rev.val+1 := by rw [Fin.val_rev]; omega
    rw [heP]
    by_cases hlast : s+1=T
    · subst T
      rw [simulationBackward_odd_last]
      have heT : 2*(s+1)-(2*s+1)=1 := by omega
      rw [heT]
      simpa [simulationTouchTail] using simulationTouching_initial_gaussian c a.rev
    · have hmore : s+1<T := by omega
      rw [simulationBackward_odd c T s hmore a]
      have heT : 2*T-(2*s+1) = 2*(T-s-2)+3 := by omega
      rw [heT]
      simpa [simulationTouchTail] using simulationTouching_odd_gaussian c (T-s-2) a.rev
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨ht,hp,hb⟩
    have hmore : s+1<T := by rw [ht] at htd; omega
    rw [simulationBackwardTouch, hb, hz, ht, hp]
    change simulationTouching (a.castSucc,1) (a.succ,0) _ ≤ _
    rw [simulationBackward_even c T s hmore a]
    have heP : 2*(c+1)-(2*a.val+2) = 2*a.rev.val+2 := by rw [Fin.val_rev]; omega
    have heT : 2*T-(2*s+2) = 2*(T-s-2)+2 := by omega
    rw [heP,heT]
    simpa [simulationTouchTail] using simulationTouching_even_gaussian c (T-s-2) a.rev

end
end Fluctuations
