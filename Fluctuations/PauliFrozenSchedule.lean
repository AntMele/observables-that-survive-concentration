import Fluctuations.PauliBrickworkCircuit
import Fluctuations.PauliFrozenCircuit

open scoped BigOperators

namespace Fluctuations
noncomputable section

section Recurrence
variable {Q : Type*} [Fintype Q]

lemma markovWeightEvolution_congr_upto (K L : ℕ → Matrix Q Q ℝ) (w : Q → ℝ) (n : ℕ)
    (h : ∀ t < n, K t = L t) : markovWeightEvolution K w n = markovWeightEvolution L w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [markovWeightEvolution,h n (by omega)]
    rw [ih (fun t ht => h t (by omega))]

lemma markovWeightEvolution_add (K : ℕ → Matrix Q Q ℝ) (w : Q → ℝ) (m n : ℕ) :
    markovWeightEvolution K w (m+n) =
      markovWeightEvolution (fun t => K (m+t)) (markovWeightEvolution K w m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (K (m+n)).mulVec (markovWeightEvolution K w (m+n)) = _
    rw [ih]
    rfl

end Recurrence

section Frozen
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Actual frozen-gate recurrence, split into its ordinary Haar prefix,
one physical fixed squared-transfer kernel, and its ordinary Haar suffix. -/
theorem pauliFrozenMarkov_split (bond : ℕ → Site × Site)
    (hbond : ∀ t, (bond t).1 ≠ (bond t).2) (w : PauliString Site → ℝ)
    (n t : ℕ) (ht : t < n) (U : TwoQubitUnitary) :
    markovWeightEvolution (pauliCircuitFixedKernel bond t U) w n =
      pauliLayerEvolution (List.ofFn (fun k : Fin (n-t-1) => bond (t+1+k.val)))
        (pauliPairEvolution (bond t).1 (bond t).2
          (fun q p => twoQubitPauliTransfer U q p ^ 2)
          (pauliLayerEvolution (List.ofFn (fun k : Fin t => bond k.val)) w)) := by
  have hpre : markovWeightEvolution (pauliCircuitFixedKernel bond t U) w t =
      markovWeightEvolution (pauliCircuitHaarKernel bond) w t := by
    apply markovWeightEvolution_congr_upto
    intro u hu
    simp [pauliCircuitFixedKernel,show u ≠ t by omega]
  have hfix : markovWeightEvolution (pauliCircuitFixedKernel bond t U) w (t+1) =
      pauliPairEvolution (bond t).1 (bond t).2
        (fun q p => twoQubitPauliTransfer U q p ^ 2)
        (pauliLayerEvolution (List.ofFn (fun k : Fin t => bond k.val)) w) := by
    rw [markovWeightEvolution,hpre,pauliLayerEvolution_ofFn bond hbond]
    funext Q
    simp only [pauliCircuitFixedKernel,Matrix.mulVec, dotProduct]
    exact pauliPairSquaredTransfer_mul (bond t).1 (bond t).2 (hbond t) U _ Q
  have hn : n = (t+1)+(n-t-1) := by omega
  conv_lhs => rw [hn,markovWeightEvolution_add,hfix]
  rw [pauliLayerEvolution_ofFn (fun k => bond (t+1+k)) (fun k => hbond _)]
  apply markovWeightEvolution_congr_upto
  intro k _
  simp [pauliCircuitFixedKernel,pauliCircuitHaarKernel,show t+1+k ≠ t by omega]

end Frozen

lemma list_ofFn_getD_take {α : Type*} (l : List α) (d : α) (t : ℕ) (ht : t ≤ l.length) :
    List.ofFn (fun k : Fin t => l.getD k.val d) = l.take t := by
  apply List.ext_getElem
  · simp [ht]
  · intro k hk hk'
    simp only [List.getElem_ofFn,List.getElem_take]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn] at hk; omega)]

lemma list_ofFn_getD_drop {α : Type*} (l : List α) (d : α) (t : ℕ) :
    List.ofFn (fun k : Fin (l.length-t) => l.getD (t+k.val) d) = l.drop t := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_ofFn,List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn] at hk; omega)]

/-- The chronological frozen recurrence for the physical brickwork schedule,
using the literal list prefix and suffix at the selected even gate. -/
theorem brickworkFrozenMarkov_split {c T : ℕ} (z : Fin T × Fin c)
    (U : TwoQubitUnitary) (w : PauliString (BrickworkSite c) → ℝ) :
    markovWeightEvolution
      (pauliCircuitFixedKernel (brickworkCircuitBond c T) (brickworkEvenGateIndex z).val U)
      w (T*(2*c+1)) =
      pauliLayerEvolution ((brickworkGateSchedule c T).drop ((brickworkEvenGateIndex z).val+1))
        (pauliPairEvolution (brickworkEvenBond z.2).1 (brickworkEvenBond z.2).2
          (fun q p => twoQubitPauliTransfer U q p ^ 2)
          (pauliLayerEvolution ((brickworkGateSchedule c T).take (brickworkEvenGateIndex z).val) w)) := by
  rw [pauliFrozenMarkov_split _ (brickworkCircuitBond_distinct c T) _ _ _
    (brickworkEvenGateIndex z).isLt]
  have hb : brickworkCircuitBond c T (brickworkEvenGateIndex z).val = brickworkEvenBond z.2 :=
    brickworkCircuitBond_even c T z.1.val z.2 z.1.isLt
  rw [hb]
  have hpre := list_ofFn_getD_take (brickworkGateSchedule c T) (brickworkOddBond 0)
    (brickworkEvenGateIndex z).val (by rw [brickworkGateSchedule_length]; exact (brickworkEvenGateIndex z).isLt.le)
  have hpost := list_ofFn_getD_drop (brickworkGateSchedule c T) (brickworkOddBond 0)
    ((brickworkEvenGateIndex z).val+1)
  simp only [brickworkCircuitBond]
  rw [hpre]
  congr 1
  simpa only [brickworkGateSchedule_length,Nat.sub_add_eq] using hpost

end
end Fluctuations
