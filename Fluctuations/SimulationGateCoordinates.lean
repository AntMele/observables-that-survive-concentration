import Fluctuations.SimulationWidth
import Fluctuations.PauliBrickworkCircuit

namespace Fluctuations
noncomputable section
attribute [local instance] Classical.propDecidable

/-- One-based physical time of an actual chronological gate coordinate. -/
def simulationGateTime (c T : ℕ) (z : Fin (T*(2*c+1))) : ℕ :=
  2 * (z.val / (2*c+1)) + if z.val % (2*c+1) < c+1 then 1 else 2

/-- One-based physical bond position of an actual chronological coordinate. -/
def simulationGatePosition (c T : ℕ) (z : Fin (T*(2*c+1))) : ℕ :=
  if z.val % (2*c+1) < c+1 then 2*(z.val % (2*c+1))+1
  else 2*(z.val % (2*c+1)-(c+1))+2

/-- Retain exactly the paper's causal eye, including its parity and final
layer convention, using the physical eye also used by the runtime model. -/
def simulationRetainedGate (c T : ℕ) (R : ℝ) (z : Fin (T*(2*c+1))) : Prop :=
  (simulationGatePosition c T z : ℤ) ∈
    simulationEyePositions (2*(c+1)) (2*T) (simulationGateTime c T z) R


/-- Boolean retention schedule consumed by the actual mixed sampler. -/
def simulationRetainedSchedule (c T : ℕ) (R : ℝ) : ℕ → Bool :=
  fun k => if h : k < T*(2*c+1) then decide (simulationRetainedGate c T R ⟨k,h⟩) else false

@[simp] theorem simulationRetainedSchedule_at (c T : ℕ) (R : ℝ) (z : Fin (T*(2*c+1))) :
    simulationRetainedSchedule c T R z.val = decide (simulationRetainedGate c T R z) := by
  simp [simulationRetainedSchedule, z.isLt]

lemma simulationGate_period_lt (c T : ℕ) (z : Fin (T*(2*c+1))) :
    z.val / (2*c+1) < T := by
  exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Nat.mul_comm] using z.isLt)

theorem simulationGate_odd_coordinates (c T s : ℕ) (hs : s < T) (a : Fin (c+1))
    (z : Fin (T*(2*c+1))) (hz : z.val = s*(2*c+1)+a.val) :
    simulationGateTime c T z = 2*s+1 ∧ simulationGatePosition c T z = 2*a.val+1 ∧
      brickworkCircuitBond c T z.val = brickworkOddBond a := by
  have ha : a.val < 2*c+1 := by omega
  have hq : z.val / (2*c+1) = s := by rw [hz, Nat.mul_comm s (2*c+1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha]; omega
  have hr : z.val % (2*c+1) = a.val := by rw [hz]; simp [Nat.mod_eq_of_lt ha]
  simp only [simulationGateTime, simulationGatePosition, hq, hr, a.isLt, if_true]
  exact ⟨trivial, trivial, hz ▸ brickworkCircuitBond_odd c T s a hs⟩

theorem simulationGate_even_coordinates (c T s : ℕ) (hs : s < T) (a : Fin c)
    (z : Fin (T*(2*c+1))) (hz : z.val = s*(2*c+1)+(c+1)+a.val) :
    simulationGateTime c T z = 2*s+2 ∧ simulationGatePosition c T z = 2*a.val+2 ∧
      brickworkCircuitBond c T z.val = brickworkEvenBond a := by
  have ha : c+1+a.val < 2*c+1 := by omega
  have he : z.val = s*(2*c+1)+(c+1+a.val) := by omega
  have hq : z.val / (2*c+1) = s := by rw [he, Nat.mul_comm s (2*c+1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha]; omega
  have hr : z.val % (2*c+1) = c+1+a.val := by rw [he]; simp [Nat.mod_eq_of_lt ha]
  simp only [simulationGateTime, simulationGatePosition, hq, hr,
    show ¬c+1+a.val < c+1 by omega, if_false, Nat.add_sub_cancel_left]
  exact ⟨trivial, trivial, hz ▸ brickworkCircuitBond_even c T s a hs⟩

/-- Every actual gate is uniquely in an odd or even matching of a valid period. -/
theorem simulationGate_cases (c T : ℕ) (z : Fin (T*(2*c+1))) :
    (∃ s < T, ∃ a : Fin (c+1), z.val = s*(2*c+1)+a.val) ∨
      (∃ s < T, ∃ a : Fin c, z.val = s*(2*c+1)+(c+1)+a.val) := by
  let s := z.val / (2*c+1)
  let r := z.val % (2*c+1)
  have hs : s < T := simulationGate_period_lt c T z
  have hr : r < 2*c+1 := Nat.mod_lt _ (by omega)
  have he : z.val = s*(2*c+1)+r := by
    dsimp [s,r]
    simpa only [Nat.mul_comm] using (Nat.div_add_mod z.val (2*c+1)).symm
  by_cases h : r < c+1
  · exact Or.inl ⟨s,hs,⟨r,h⟩,he⟩
  · refine Or.inr ⟨s,hs,⟨r-(c+1),by omega⟩,?_⟩
    dsimp
    omega

theorem simulationGateTime_bounds (c T : ℕ) (z : Fin (T*(2*c+1))) :
    1 ≤ simulationGateTime c T z ∧ simulationGateTime c T z ≤ 2*T := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rw [(simulationGate_odd_coordinates c T s hs a z hz).1]; omega
  · rw [(simulationGate_even_coordinates c T s hs a z hz).1]; omega

theorem simulationGatePosition_bounds (c T : ℕ) (z : Fin (T*(2*c+1))) :
    1 ≤ simulationGatePosition c T z ∧ simulationGatePosition c T z < 2*(c+1) := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rw [(simulationGate_odd_coordinates c T s hs a z hz).2.1]; omega
  · rw [(simulationGate_even_coordinates c T s hs a z hz).2.1]; omega

theorem simulationGate_parity (c T : ℕ) (z : Fin (T*(2*c+1))) :
    simulationGatePosition c T z % 2 = simulationGateTime c T z % 2 := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨ht,hp,_⟩
    rw [ht,hp]
    omega
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨ht,hp,_⟩
    rw [ht,hp]
    omega

theorem simulationGatePosition_eq_bondPosition (c T : ℕ) (z : Fin (T*(2*c+1))) :
    (simulationGatePosition c T z : ℤ) = simulationBondPosition (brickworkCircuitBond c T z.val) := by
  rcases simulationGate_cases c T z with ⟨s,hs,a,hz⟩ | ⟨s,hs,a,hz⟩
  · rcases simulationGate_odd_coordinates c T s hs a z hz with ⟨_,hp,hb⟩
    rw [hp,hb]
    simp [simulationBondPosition, brickworkOddBond, brickworkRank]
  · rcases simulationGate_even_coordinates c T s hs a z hz with ⟨_,hp,hb⟩
    rw [hp,hb]
    simp [simulationBondPosition, brickworkEvenBond, brickworkRank]
    omega

end
end Fluctuations
