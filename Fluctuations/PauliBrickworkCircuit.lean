import Fluctuations.PauliBrickworkInitial
import Mathlib.Data.List.GetD

namespace Fluctuations
noncomputable section

section ScheduleBridge
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

theorem pauliLayerEvolution_ofFn (bond : ℕ → Site × Site)
    (hbond : ∀ t, (bond t).1 ≠ (bond t).2) (n : ℕ)
    (w : (Site → Fin 4) → ℝ) :
    pauliLayerEvolution (List.ofFn (fun i : Fin n => bond i.val)) w =
      markovWeightEvolution (pauliCircuitHaarKernel bond) w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, pauliLayerEvolution_append]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [ih]
    funext Q
    change pauliPairEvolution (bond n).1 (bond n).2 localPauliHaarKernel _ Q = _
    symm
    exact pauliPairKernel_mul (bond n).1 (bond n).2 (hbond n) _ Q

end ScheduleBridge

def brickworkBlock (c : ℕ) : List (BrickworkSite c × BrickworkSite c) :=
  brickworkOddBonds c ++ brickworkEvenBonds c

/-- All gates of T complete odd/even periods, in physical chronological order. -/
def brickworkGateSchedule (c : ℕ) : ℕ → List (BrickworkSite c × BrickworkSite c)
  | 0 => []
  | T+1 => brickworkGateSchedule c T ++ brickworkBlock c

@[simp] lemma brickworkBlock_length (c : ℕ) : (brickworkBlock c).length = 2*c+1 := by
  simp [brickworkBlock,brickworkOddBonds,brickworkEvenBonds]
  omega

@[simp] lemma brickworkGateSchedule_length (c T : ℕ) :
    (brickworkGateSchedule c T).length = T*(2*c+1) := by
  induction T with
  | zero => simp [brickworkGateSchedule]
  | succ T ih => simp [brickworkGateSchedule,ih]; ring

def brickworkCircuitBond (c T t : ℕ) : BrickworkSite c × BrickworkSite c :=
  (brickworkGateSchedule c T).getD t (brickworkOddBond 0)

lemma brickworkBlock_distinct {c : ℕ} {p : BrickworkSite c × BrickworkSite c}
    (hp : p ∈ brickworkBlock c) : p.1 ≠ p.2 := by
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp h
    simp [brickworkOddBond]
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp h
    simp [brickworkEvenBond]

lemma brickworkGateSchedule_distinct {c T : ℕ} {p : BrickworkSite c × BrickworkSite c}
    (hp : p ∈ brickworkGateSchedule c T) : p.1 ≠ p.2 := by
  induction T with
  | zero => simp [brickworkGateSchedule] at hp
  | succ T ih =>
    rcases List.mem_append.mp hp with h | h
    · exact ih h
    · exact brickworkBlock_distinct h

theorem brickworkCircuitBond_distinct (c T t : ℕ) :
    (brickworkCircuitBond c T t).1 ≠ (brickworkCircuitBond c T t).2 := by
  unfold brickworkCircuitBond
  by_cases ht : t < (brickworkGateSchedule c T).length
  · rw [List.getD_eq_getElem _ _ ht]
    exact brickworkGateSchedule_distinct (List.getElem_mem ht)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [brickworkOddBond]

lemma brickworkGateSchedule_getD (c T s j : ℕ) (hs : s < T) (hj : j < 2*c+1) :
    (brickworkGateSchedule c T).getD (s*(2*c+1)+j) (brickworkOddBond 0) =
      (brickworkBlock c).getD j (brickworkOddBond 0) := by
  induction T with
  | zero => omega
  | succ T ih =>
    rw [brickworkGateSchedule]
    by_cases hsT : s < T
    · rw [List.getD_append]
      · exact ih hsT
      · rw [brickworkGateSchedule_length]
        have hh := Nat.mul_le_mul_right (2*c+1) (show s+1 ≤ T by omega)
        nlinarith
    · have he : s = T := by omega
      subst s
      rw [List.getD_append_right]
      · simp only [brickworkGateSchedule_length,Nat.add_sub_cancel_left]
      · rw [brickworkGateSchedule_length]
        omega

theorem brickworkCircuitBond_odd (c T s : ℕ) (a : Fin (c+1)) (hs : s < T) :
    brickworkCircuitBond c T (s*(2*c+1)+a.val) = brickworkOddBond a := by
  rw [brickworkCircuitBond, brickworkGateSchedule_getD c T s a.val hs (by omega)]
  rw [brickworkBlock,List.getD_append]
  · rw [List.getD_eq_getElem]
    · simp only [brickworkOddBonds,List.getElem_ofFn]
    · simp [brickworkOddBonds]
  · simp [brickworkOddBonds]

theorem brickworkCircuitBond_even (c T s : ℕ) (a : Fin c) (hs : s < T) :
    brickworkCircuitBond c T (s*(2*c+1)+(c+1)+a.val) = brickworkEvenBond a := by
  rw [show s*(2*c+1)+(c+1)+a.val = s*(2*c+1)+((c+1)+a.val) by omega,
    brickworkCircuitBond,brickworkGateSchedule_getD c T s ((c+1)+a.val) hs (by omega)]
  rw [brickworkBlock,List.getD_append_right]
  · simp only [brickworkOddBonds,List.length_ofFn,Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem]
    · simp only [brickworkEvenBonds,List.getElem_ofFn]
    · simp [brickworkEvenBonds]
  · simp [brickworkOddBonds]

/-- The actual independent gate coordinate of an even bond in a chosen period. -/
def brickworkEvenGateIndex {c T : ℕ} (z : Fin T × Fin c) : Fin (T*(2*c+1)) :=
  ⟨z.1.val*(2*c+1)+(c+1)+z.2.val,by
    have h₁ := z.1.isLt
    have h₂ := z.2.isLt
    have hh := Nat.mul_le_mul_right (2*c+1) (show z.1.val+1 ≤ T by omega)
    nlinarith⟩

theorem brickworkEvenGateIndex_injective (c T : ℕ) :
    Function.Injective (brickworkEvenGateIndex (c := c) (T := T)) := by
  intro z w h
  have he := congrArg Fin.val h
  change z.1.val*(2*c+1)+(c+1)+z.2.val = w.1.val*(2*c+1)+(c+1)+w.2.val at he
  have hz := z.2.isLt
  have hw := w.2.isLt
  have hfirst : z.1.val = w.1.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · have hm := Nat.mul_le_mul_right (2*c+1) (show z.1.val+1 ≤ w.1.val by omega)
      nlinarith
    · have hm := Nat.mul_le_mul_right (2*c+1) (show w.1.val+1 ≤ z.1.val by omega)
      nlinarith
  apply Prod.ext
  · exact Fin.ext hfirst
  · apply Fin.ext
    rw [hfirst] at he
    omega

/-- Every physical qubit is touched after an interior fixed even gate: use
the next odd layer. This discharges the quantum covariance-reset condition. -/
theorem brickworkEvenGate_later_cover {c T : ℕ} (z : Fin T × Fin c)
    (hz : z.1.val+1 < T) (q : BrickworkSite c) :
    ∃ u : Fin (T*(2*c+1)), (brickworkEvenGateIndex z).val < u.val ∧
      (q = (brickworkCircuitBond c T u.val).1 ∨ q = (brickworkCircuitBond c T u.val).2) := by
  let u : Fin (T*(2*c+1)) := ⟨(z.1.val+1)*(2*c+1)+q.1.val,by
    have hq := q.1.isLt
    have hh := Nat.mul_le_mul_right (2*c+1) (show z.1.val+2 ≤ T by omega)
    nlinarith⟩
  refine ⟨u,?_,?_⟩
  · have ha := z.2.isLt
    dsimp [u,brickworkEvenGateIndex]
    nlinarith
  · change q = (brickworkCircuitBond c T ((z.1.val+1)*(2*c+1)+q.1.val)).1 ∨ _
    rw [brickworkCircuitBond_odd c T _ q.1 hz]
    rcases q with ⟨a,b⟩
    fin_cases b <;> simp [brickworkOddBond]

theorem brickworkCircuit_markov (c T : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    markovWeightEvolution (pauliCircuitHaarKernel (brickworkCircuitBond c T)) w
      (T*(2*c+1)) = pauliLayerEvolution (brickworkGateSchedule c T) w := by
  rw [← pauliLayerEvolution_ofFn _ (brickworkCircuitBond_distinct c T)]
  congr 1
  have he : (List.ofFn (fun i : Fin (brickworkGateSchedule c T).length =>
      (brickworkGateSchedule c T).getD i.val (brickworkOddBond 0))) = brickworkGateSchedule c T := by
    simp_rw [List.getD_eq_getElem _ _ (Fin.isLt _)]
    exact List.ofFn_getElem _
  simpa only [brickworkGateSchedule_length,brickworkCircuitBond] using he

end
end Fluctuations
