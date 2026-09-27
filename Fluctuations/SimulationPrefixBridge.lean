import Fluctuations.SimulationTouchingTail
import Fluctuations.PauliBrickworkConditional

open scoped BigOperators
namespace Fluctuations
noncomputable section

section Untouched
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Haar updates on a disjoint bond preserve the touching probability of
the specified pair, including for correlated full-string distributions. -/
theorem simulationTouching_pair_misses (i j k l : Site) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (w : (Site → Fin 4) → ℝ) :
    simulationTouching i j (pauliPairEvolution k l localPauliHaarKernel w) =
      simulationTouching i j w := by
  let f : (Site → Fin 4) → ℝ := fun P => if P i = 0 ∧ P j = 0 then 0 else 1
  have hf : pauliPairEvolution k l localPauliHaarKernel f = f := by
    funext P
    simp only [pauliPairEvolution, f, pauliPairReplace_apply_away k l i hik hil,
      pauliPairReplace_apply_away k l j hjk hjl, ← Finset.sum_mul]
    have hk : (∑ q, localPauliHaarKernel (P k, P l) q) = 1 := by
      simpa using pauliHaar_one_product (P k, P l)
    rw [hk, one_mul]
  have he := pauliPairEvolution_selfAdjoint k l hkl f w
  rw [hf] at he
  simpa only [simulationTouching, f, mul_comm] using he

theorem simulationTouching_layer_misses (i j : Site) (bs : List (Site × Site))
    (hd : ∀ p ∈ bs, p.1 ≠ p.2)
    (hmiss : ∀ p ∈ bs, i ≠ p.1 ∧ i ≠ p.2 ∧ j ≠ p.1 ∧ j ≠ p.2)
    (w : (Site → Fin 4) → ℝ) :
    simulationTouching i j (pauliLayerEvolution bs w) = simulationTouching i j w := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨k,l⟩
    rw [pauliLayerEvolution, ih (fun p hp => hd p (by simp [hp]))
      (fun p hp => hmiss p (by simp [hp]))]
    have hm := hmiss (k,l) (by simp)
    exact simulationTouching_pair_misses i j k l (hd (k,l) (by simp))
      hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 w

end Untouched

theorem simulationChronologicalPrefix (c T t : ℕ) (ht : t ≤ T * (2*c+1))
    (w : PauliString (BrickworkSite c) → ℝ) :
    markovWeightEvolution (pauliCircuitHaarKernel (brickworkCircuitBond c T)) w t =
      pauliLayerEvolution ((brickworkGateSchedule c T).take t) w := by
  rw [← pauliLayerEvolution_ofFn _ (brickworkCircuitBond_distinct c T)]
  unfold brickworkCircuitBond
  rw [list_ofFn_getD_take _ _ _ (by simpa using ht)]

lemma simulationTake_append_length_add {A : Type*} (l r : List A) (n : ℕ) :
    (l ++ r).take (l.length + n) = l ++ r.take n := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _)]
  simp

lemma simulationDrop_append_length_add {A : Type*} (l r : List A) (n : ℕ) :
    (l ++ r).drop (l.length + n) = r.drop n := by
  rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _)]
  simp

theorem simulationSchedule_take_odd (c T s : ℕ) (hs : s < T) (a : Fin (c+1)) :
    (brickworkGateSchedule c T).take (s*(2*c+1)+a.val) =
      brickworkGateSchedule c s ++ (brickworkOddBonds c).take a.val := by
  rw [brickworkGateSchedule_period_split c T s hs, brickworkBlock]
  simp only [List.append_assoc]
  have hn : s*(2*c+1)+a.val = (brickworkGateSchedule c s).length+a.val := by simp
  rw [hn, simulationTake_append_length_add,
    List.take_append_of_le_length (by simp only [brickworkOddBonds,List.length_ofFn]; omega)]

theorem simulationSchedule_drop_odd (c T s : ℕ) (hs : s < T) (a : Fin (c+1)) :
    (brickworkGateSchedule c T).drop (s*(2*c+1)+a.val+1) =
      (brickworkOddBonds c).drop (a.val+1) ++ brickworkEvenBonds c ++
        brickworkGateSchedule c (T-s-1) := by
  rw [brickworkGateSchedule_period_split c T s hs, brickworkBlock]
  simp only [List.append_assoc]
  have hn : s*(2*c+1)+a.val+1 = (brickworkGateSchedule c s).length+(a.val+1) := by simp; omega
  rw [hn, simulationDrop_append_length_add,
    List.drop_append_of_le_length (by simp only [brickworkOddBonds,List.length_ofFn]; omega)]

lemma simulationOddBond_disjoint {c : ℕ} (a b : Fin (c+1)) (hba : b ≠ a) :
    (brickworkOddBond a).1 ≠ (brickworkOddBond b).1 ∧
    (brickworkOddBond a).1 ≠ (brickworkOddBond b).2 ∧
    (brickworkOddBond a).2 ≠ (brickworkOddBond b).1 ∧
    (brickworkOddBond a).2 ≠ (brickworkOddBond b).2 := by
  simp [brickworkOddBond, Ne.symm hba]

lemma simulationOddPrefix_misses {c : ℕ} (a : Fin (c+1))
    (p : BrickworkSite c × BrickworkSite c) (hp : p ∈ (brickworkOddBonds c).take a.val) :
    (a,0) ≠ p.1 ∧ (a,0) ≠ p.2 ∧ (a,1) ≠ p.1 ∧ (a,1) ≠ p.2 := by
  obtain ⟨k,hk,hp⟩ := List.mem_take_iff_getElem.mp hp
  have hka : k < a.val := (lt_min_iff.mp hk).1
  let b : Fin (c+1) := ⟨k,by omega⟩
  have hb : b ≠ a := by intro he; have := congrArg Fin.val he; dsimp [b] at this; omega
  have he : brickworkOddBond b = p := by simpa only [brickworkOddBonds, List.getElem_ofFn] using hp
  rw [← he]
  exact simulationOddBond_disjoint a b hb

theorem simulationPrefix_even (c T s : ℕ) (hs : s < T) (a : Fin c) :
    simulationTouching (a.castSucc,1) (a.succ,0)
      (pauliLayerEvolution ((brickworkGateSchedule c T).take (s*(2*c+1)+(c+1)+a.val))
        (pauliInitialVector (brickworkInitialZ c))) =
      simulationTouching (a.castSucc,1) (a.succ,0) (simulationBeforeEven c s) := by
  rw [brickworkGateSchedule_take_even c T s hs a, pauliLayerEvolution_append,
    simulationTouching_layer_misses]
  · rw [pauliLayerEvolution_append, brickworkSchedule_then_odd]
    rfl
  · intro p hp
    obtain ⟨b,_,rfl⟩ := brickworkEvenBonds_take_mem a p hp
    simp [brickworkEvenBond]
  · exact brickworkEvenPrefix_misses a

theorem simulationPrefix_odd_succ (c T s : ℕ) (hs : s+1 < T) (a : Fin (c+1)) :
    simulationTouching (a,0) (a,1)
      (pauliLayerEvolution ((brickworkGateSchedule c T).take ((s+1)*(2*c+1)+a.val))
        (pauliInitialVector (brickworkInitialZ c))) =
      simulationTouching (a,0) (a,1) (simulationBeforeOdd c s) := by
  rw [simulationSchedule_take_odd c T (s+1) hs a, pauliLayerEvolution_append,
    simulationTouching_layer_misses]
  · rw [brickworkSchedule_action_succ]
    rfl
  · intro p hp
    have hp' := List.mem_of_mem_take hp
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hp'
    simp [brickworkOddBond]
  · exact simulationOddPrefix_misses a

theorem simulationPrefix_odd_initial (c T : ℕ) (hT : 0 < T) (a : Fin (c+1)) :
    simulationTouching (a,0) (a,1)
      (pauliLayerEvolution ((brickworkGateSchedule c T).take a.val)
        (pauliInitialVector (brickworkInitialZ c))) =
      simulationTouching (a,0) (a,1) (pauliInitialVector (brickworkInitialZ c)) := by
  have h := simulationSchedule_take_odd c T 0 hT a
  simp only [Nat.zero_mul, Nat.zero_add, brickworkGateSchedule, List.nil_append] at h
  rw [h]
  apply simulationTouching_layer_misses
  · intro p hp
    have hp' := List.mem_of_mem_take hp
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp hp'
    simp [brickworkOddBond]
  · exact simulationOddPrefix_misses a

end
end Fluctuations
