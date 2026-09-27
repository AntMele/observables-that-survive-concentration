import Fluctuations.SimulationLocalCoordinate
import Fluctuations.SimulationReverseCircuit

open scoped BigOperators
namespace Fluctuations

lemma reverseGateRealization_update {n : ℕ} (x : Fin n → TwoQubitUnitary)
    (t : Fin n) (U : TwoQubitUnitary) :
    reverseGateRealization (Function.update x t U) =
      Function.update (reverseGateRealization x) t.rev U⁻¹ := by
  funext a
  by_cases ha : a = t.rev
  · subst a
    change (Function.update x t U (Fin.rev (Fin.rev t)))⁻¹ =
      Function.update (reverseGateRealization x) t.rev U⁻¹ t.rev
    rw [Fin.rev_rev, Function.update_self, Function.update_self]
  · have har : a.rev ≠ t := by
      intro h
      apply ha
      simpa using congrArg Fin.rev h
    simp [reverseGateRealization, ha, har]

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Backward causal-cone influence for the literal quantum OTOC. The prefix is
formed from the actual reversed suffix gates, each inverted; its law is thus
the reversed-suffix Pauli process after Haar averaging. -/
theorem pauliCircuit_coordinate_backward_otoc_change
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (initial probe : Site) (N : ℕ) (x : Fin N → TwoQubitUnitary)
    (t : Fin N) (U V : TwoQubitUnitary) :
    ‖globalOTOC (globalMaximallyMixedState (QubitState Site))
       (pauliStringMatrix (pauliSiteZ initial)) (pauliStringMatrix (pauliSiteZ probe)) 1
       (pauliCircuitUnitary bond hbond N (Function.update x t U)) -
     globalOTOC (globalMaximallyMixedState (QubitState Site))
       (pauliStringMatrix (pauliSiteZ initial)) (pauliStringMatrix (pauliSiteZ probe)) 1
       (pauliCircuitUnitary bond hbond N (Function.update x t V))‖ ≤
      4 * Real.sqrt (pauliGateActiveMass (bond t.val).1 (bond t.val).2
        (randomLinearEvolution (pauliCircuitTransfer (reverseCircuitBond bond N))
          (pauliInitialVector (pauliSiteZ probe)) t.rev.val
          (fun i => reverseGateRealization x ⟨i.val, lt_trans i.isLt t.rev.isLt⟩))) := by
  rw [pauliCircuit_otoc_reverse bond hbond _ _ N (Function.update x t U),
    pauliCircuit_otoc_reverse bond hbond _ _ N (Function.update x t V),
    reverseGateRealization_update, reverseGateRealization_update]
  have h := pauliCircuit_coordinate_otoc_change (reverseCircuitBond bond N)
    (fun u => hbond (N-(u+1))) (pauliSiteZ probe) initial N
    (reverseGateRealization x) t.rev U⁻¹ V⁻¹
  have hb : reverseCircuitBond bond N t.rev.val = bond t.val := by
    unfold reverseCircuitBond
    congr 1
    rw [Fin.val_rev]
    omega
  simpa only [hb] using h

end Fluctuations
