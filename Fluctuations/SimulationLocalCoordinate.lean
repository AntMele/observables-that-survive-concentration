import Fluctuations.SimulationLocalInfluence

open scoped BigOperators
namespace Fluctuations

lemma randomLinearEvolution_split {G Q : Type*} [Fintype Q]
    (K : ℕ → G → Matrix Q Q ℝ) (v : Q → ℝ) (n m : ℕ) (x : Fin (n+m) → G) :
    randomLinearEvolution K v (n+m) x =
      randomLinearEvolution (fun t => K (n+t))
        (randomLinearEvolution K v n (fun i => x (Fin.castAdd m i))) m
        (fun j => x (Fin.natAdd n j)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [randomLinearEvolution]
    change (K (n+m) (x (Fin.last (n+m)))).mulVec
      (randomLinearEvolution K v (n+m) (fun a => x a.castSucc)) = _
    rw [ih (fun a => x a.castSucc)]
    rfl

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Literal coordinate replacement, with the original prefix and common suffix
explicitly extracted from the physical gate sequence. -/
theorem pauliCircuit_coordinate_sign_change
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeMass ψ = 1)
    (probe : Site) (n m : ℕ) (x : Fin (n+1+m) → TwoQubitUnitary)
    (U V : TwoQubitUnitary) :
    |amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) ψ (n+1+m)
        (Function.update x ⟨n, by omega⟩ U)) -
     amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) ψ (n+1+m)
        (Function.update x ⟨n, by omega⟩ V))| ≤
      4 * Real.sqrt (pauliGateActiveMass (bond n).1 (bond n).2
        (randomLinearEvolution (pauliCircuitTransfer bond) ψ n
          (fun i => x ⟨i.val, by omega⟩))) := by
  let vpre := randomLinearEvolution (pauliCircuitTransfer bond) ψ n
    (fun i => x ⟨i.val, by omega⟩)
  let suffix : Fin m → TwoQubitUnitary := fun j => x (Fin.natAdd (n+1) j)
  have he (W : TwoQubitUnitary) :
      randomLinearEvolution (pauliCircuitTransfer bond) ψ (n+1+m)
        (Function.update x ⟨n, by omega⟩ W) =
      randomLinearEvolution (pauliCircuitTransfer (fun t => bond (n+1+t)))
        (pauliSamplerFixed (bond n).1 (bond n).2 (hbond n) W vpre) m suffix := by
    rw [randomLinearEvolution_split _ _ (n+1) m]
    have hp : randomLinearEvolution (pauliCircuitTransfer bond) ψ (n+1)
        (fun i => Function.update x ⟨n, by omega⟩ W (Fin.castAdd m i)) =
        pauliSamplerFixed (bond n).1 (bond n).2 (hbond n) W vpre := by
      simp only [randomLinearEvolution]
      have hl : Fin.castAdd m (Fin.last n) = (⟨n, by omega⟩ : Fin (n+1+m)) := rfl
      rw [hl, Function.update_self]
      rw [show (fun a : Fin n => Function.update x (⟨n, by omega⟩ : Fin (n+1+m)) W
          (Fin.castAdd m a.castSucc)) = (fun a => x ⟨a.val, by omega⟩) by
        funext a
        apply Function.update_of_ne
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.coe_castAdd, Fin.coe_castSucc] at hval
        omega]
      exact (funext (pauliSamplerFixed_eq_mulVec (bond n).1 (bond n).2 (hbond n) W vpre)).symm
    rw [hp]
    have hs : (fun j => Function.update x (⟨n, by omega⟩ : Fin (n+1+m)) W
        (Fin.natAdd (n+1) j)) = suffix := by
      funext j
      apply Function.update_of_ne
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.coe_natAdd] at hval
      omega
    rw [hs]
    rfl
  rw [he U, he V]
  exact pauliGateChange_endpoint_le (bond n).1 (bond n).2 (hbond n) U V vpre
    (by rw [randomLinearEvolution_pauli_mass bond hbond]; exact hψ)
    (fun t => bond (n+1+t)) (fun t => hbond (n+1+t)) probe m suffix

/-- Coordinate form with the original finite circuit indexing. -/
theorem pauliCircuit_coordinate_sign_change_fin
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeMass ψ = 1)
    (probe : Site) (N : ℕ) (x : Fin N → TwoQubitUnitary) (t : Fin N)
    (U V : TwoQubitUnitary) :
    |amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) ψ N (Function.update x t U)) -
     amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) ψ N (Function.update x t V))| ≤
      4 * Real.sqrt (pauliGateActiveMass (bond t.val).1 (bond t.val).2
        (randomLinearEvolution (pauliCircuitTransfer bond) ψ t.val
          (fun i => x ⟨i.val, lt_trans i.isLt t.isLt⟩))) := by
  let k := t.val
  have hkt : t.val = k := rfl
  have hkn : k < N := t.isLt
  clear_value k
  obtain ⟨m, hm⟩ : ∃ m, N = k+1+m := ⟨N-(k+1), by omega⟩
  subst N
  have ht : t = (⟨k, by omega⟩ : Fin (k+1+m)) := Fin.ext hkt
  subst t
  exact pauliCircuit_coordinate_sign_change bond hbond ψ hψ probe k m x U V

/-- The same bound for the literal complex-valued quantum matrix trace.
At infinite temperature the observable is real, but no real-part relaxation is
used in this norm inequality. -/
theorem pauliCircuit_coordinate_otoc_change
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (probe : Site) (N : ℕ)
    (x : Fin N → TwoQubitUnitary) (t : Fin N) (U V : TwoQubitUnitary) :
    ‖globalOTOC (globalMaximallyMixedState (QubitState Site)) (pauliStringMatrix P₀)
       (pauliStringMatrix (pauliSiteZ probe)) 1
       (pauliCircuitUnitary bond hbond N (Function.update x t U)) -
     globalOTOC (globalMaximallyMixedState (QubitState Site)) (pauliStringMatrix P₀)
       (pauliStringMatrix (pauliSiteZ probe)) 1
       (pauliCircuitUnitary bond hbond N (Function.update x t V))‖ ≤
      4 * Real.sqrt (pauliGateActiveMass (bond t.val).1 (bond t.val).2
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) t.val
          (fun i => x ⟨i.val, lt_trans i.isLt t.isLt⟩))) := by
  simp_rw [pauliCircuit_infiniteTemperature_sign, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  apply pauliCircuit_coordinate_sign_change_fin bond hbond
  simp [amplitudeMass, pauliInitialVector]

end Fluctuations
