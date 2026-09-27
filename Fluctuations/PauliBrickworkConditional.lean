import Fluctuations.PauliBrickworkCircuit
import Fluctuations.PauliBrickworkScheduleSplit
import Fluctuations.PauliFrozenSchedule
import Fluctuations.PauliFixedPropagation
import Fluctuations.PauliPairCommutation
import Fluctuations.PauliUntouchedObservable
import Fluctuations.BrickworkEvenRemainder

open scoped BigOperators Matrix
namespace Fluctuations
noncomputable section

/-- Moving the final odd layer to the front of the period decomposition is
an identity of actual Pauli evolution operators. -/
lemma brickworkSchedule_then_odd (c s : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    pauliLayerEvolution (brickworkOddBonds c)
      (pauliLayerEvolution (brickworkGateSchedule c s) w) =
      (brickworkPeriod c)^[s] (pauliLayerEvolution (brickworkOddBonds c) w) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [brickworkGateSchedule,pauliLayerEvolution_append,brickworkBlock,pauliLayerEvolution_append]
    change brickworkPeriod c (pauliLayerEvolution (brickworkOddBonds c)
      (pauliLayerEvolution (brickworkGateSchedule c s) w)) = _
    rw [ih,Function.iterate_succ_apply']

/-- The physical complete schedule ends with one even layer after a sequence
of even–odd periods started by its first odd layer. -/
lemma brickworkSchedule_action_succ (c s : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    pauliLayerEvolution (brickworkGateSchedule c (s+1)) w =
      pauliLayerEvolution (brickworkEvenBonds c)
        ((brickworkPeriod c)^[s] (pauliLayerEvolution (brickworkOddBonds c) w)) := by
  rw [brickworkGateSchedule,pauliLayerEvolution_append,brickworkBlock,pauliLayerEvolution_append]
  rw [brickworkSchedule_then_odd]

/-- The actual complete Haar past, through the odd layer immediately before
an even gate, is the full shock mixture with coefficients given by Q^s. -/
theorem brickworkInitialZ_prefix (c s : ℕ) :
    pauliLayerEvolution (brickworkGateSchedule c s ++ brickworkOddBonds c)
      (pauliInitialVector (brickworkInitialZ c)) =
      brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0) := by
  rw [pauliLayerEvolution_append,brickworkSchedule_then_odd,brickworkInitialZ_odd_layer]
  have he : brickworkCellShock (0 : Fin (c+1)) =
      brickworkCellProjection (fun b : Fin (c+1) => if b = 0 then 1 else 0) := by
    funext P
    simp [brickworkCellProjection]
  rw [he,brickworkPeriod_iterate_cellProjection]
  congr 1
  funext b
  simp [Matrix.mulVec,dotProduct,mul_ite]

/-- Literal chronological Pauli evolution with one chosen even gate replaced
by a specified local transfer kernel. -/
def brickworkEvenCutEvolution (c T s : ℕ) (a : Fin c)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ) :
    (BrickworkSite c → Fin 4) → ℝ :=
  pauliLayerEvolution ((brickworkGateSchedule c T).drop (s*(2*c+1)+(c+1)+a.val+1))
    (pauliPairEvolution (a.castSucc,1) (a.succ,0) K
      (pauliLayerEvolution ((brickworkGateSchedule c T).take (s*(2*c+1)+(c+1)+a.val))
        (pauliInitialVector (brickworkInitialZ c))))

/-- Choosing the Haar kernel at the selected position restores the actual
complete Haar circuit, including all gates in the selected matching. -/
lemma brickworkEvenCutEvolution_haar (c T s : ℕ) (a : Fin c) (hs : s < T) :
    brickworkEvenCutEvolution c T s a localPauliHaarKernel =
      pauliLayerEvolution (brickworkGateSchedule c T) (pauliInitialVector (brickworkInitialZ c)) := by
  unfold brickworkEvenCutEvolution
  rw [brickworkGateSchedule_take_even c T s hs a,brickworkGateSchedule_drop_even c T s hs a]
  conv_rhs => rw [← brickworkGateSchedule_even_decomposition c T s hs a]
  simp only [pauliLayerEvolution_append,pauliLayerEvolution,brickworkEvenBond]

/-- The full chronological frozen evolution is reduced to the actual Haar
past, a reordered matching, and the entire remaining Haar future. -/
lemma brickworkEvenCutEvolution_form (c T s : ℕ) (a : Fin c) (hz : s + 1 < T)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (hmiss : ∀ p ∈ (brickworkEvenBonds c).take a.val,
      (a.castSucc,(1 : Fin 2)) ≠ p.1 ∧ (a.castSucc,(1 : Fin 2)) ≠ p.2 ∧
      (a.succ,(0 : Fin 2)) ≠ p.1 ∧ (a.succ,(0 : Fin 2)) ≠ p.2) :
    brickworkEvenCutEvolution c T s a K =
      pauliLayerEvolution (brickworkEvenBonds c)
        ((brickworkPeriod c)^[T-s-2] (pauliLayerEvolution (brickworkOddBonds c)
          (pauliLayerEvolution ((brickworkEvenBonds c).take a.val ++
            (brickworkEvenBonds c).drop (a.val+1))
            (pauliPairEvolution (a.castSucc,1) (a.succ,0) K
              (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0)))))) := by
  unfold brickworkEvenCutEvolution
  rw [brickworkGateSchedule_take_even c T s (by omega) a,
    brickworkGateSchedule_drop_even c T s (by omega) a]
  rw [pauliLayerEvolution_append,pauliLayerEvolution_append,
    brickworkInitialZ_prefix,pauliFixedPair_first _ _ K _ _ hmiss]
  rw [show T-s-1=(T-s-2)+1 by omega,brickworkSchedule_action_succ]

/-- The complete physical brickwork circuit with one interior even gate fixed
has the exact manuscript conditional-response formula at the classical Pauli
level. Every prefix, matching gate, final layer, and endpoint factor is explicit. -/
theorem brickworkFrozenMarkov_sign_gap {c T : ℕ} (z : Fin T × Fin c)
    (hz : z.1.val + 1 < T) (U : TwoQubitUnitary) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      markovWeightEvolution
        (pauliCircuitFixedKernel (brickworkCircuitBond c T) (brickworkEvenGateIndex z).val U)
        (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P) -
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      markovWeightEvolution (pauliCircuitHaarKernel (brickworkCircuitBond c T))
        (pauliInitialVector (brickworkInitialZ c)) (T*(2*c+1)) P) =
      -(16/15 : ℝ) * endpointPastFactor c z.1.val z.2 *
        endpointFutureFactor c (T-z.1.val-2) z.2 * (localPauliA U - 4/5) := by
  rw [brickworkFrozenMarkov_split,brickworkCircuit_markov]
  change (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      brickworkEvenCutEvolution c T z.1.val z.2 (localPauliSquaredKernel U) P) -
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      pauliLayerEvolution (brickworkGateSchedule c T) (pauliInitialVector (brickworkInitialZ c)) P) = _
  rw [← brickworkEvenCutEvolution_haar c T z.1.val z.2 z.1.isLt]
  rw [brickworkEvenCutEvolution_form c T z.1.val z.2 hz (localPauliSquaredKernel U)
      (brickworkEvenPrefix_misses z.2),
    brickworkEvenCutEvolution_form c T z.1.val z.2 hz localPauliHaarKernel
      (brickworkEvenPrefix_misses z.2)]
  simp only [brickworkEven_sign]
  exact brickworkFixedMatching_future_sign_gap c z.1.val (T-z.1.val-2) z.2 U
    ((brickworkEvenBonds c).take z.2.val ++ (brickworkEvenBonds c).drop (z.2.val+1))
    (brickworkEvenRemainder_adjacent z.2) (brickworkEvenRemainder_misses z.2)

end
end Fluctuations
