import Fluctuations.SimulationSampler
import Fluctuations.SimulationTrace

open scoped BigOperators
namespace Fluctuations
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The physical local conjugation preserves Euclidean mass for every vector,
including unnormalized differences and active-sector projections. -/
theorem amplitudeMass_pauliSamplerFixed (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (ψ : PauliString Site → ℝ) :
    amplitudeMass (pauliSamplerFixed i j hij U ψ) = amplitudeMass ψ := by
  let e := pairSplitEquiv i j hij (Fin 4)
  let v := fun x => ψ (e.symm x)
  change (∑ P, amplitudeLocalUpdate (twoQubitPauliTransfer U) v (e P) ^ 2) = _
  rw [Equiv.sum_comp e (fun p => amplitudeLocalUpdate (twoQubitPauliTransfer U) v p ^ 2)]
  unfold amplitudeMass
  conv_rhs => rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact amplitudeMass_mulVec (twoQubitPauliTransfer U)
    (fun a b => twoQubitPauliTransfer_column_inner a b U) (fun a => v (a,s))

theorem amplitudeMass_pauliPairTransfer (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (ψ : PauliString Site → ℝ) :
    amplitudeMass (Matrix.mulVec (pauliPairTransfer i j U) ψ) = amplitudeMass ψ := by
  rw [← show pauliSamplerFixed i j hij U ψ = Matrix.mulVec (pauliPairTransfer i j U) ψ from
    funext (pauliSamplerFixed_eq_mulVec i j hij U ψ)]
  exact amplitudeMass_pauliSamplerFixed i j hij U ψ

/-- Coefficients with a nonidentity Pauli somewhere on the gate bond. -/
noncomputable def pauliGateActiveVector (i j : Site) (ψ : PauliString Site → ℝ)
    (P : PauliString Site) : ℝ := if (P i,P j) = (0,0) then 0 else ψ P

noncomputable def pauliGateActiveMass (i j : Site) (ψ : PauliString Site → ℝ) : ℝ :=
  amplitudeMass (pauliGateActiveVector i j ψ)

theorem pauliGateActiveMass_nonneg (i j : Site) (ψ : PauliString Site → ℝ) :
    0 ≤ pauliGateActiveMass i j ψ := amplitudeMass_nonneg _

/-- Changing a gate acts only on its nonidentity input sector. -/
theorem pauliSamplerFixed_sub_active (i j : Site) (hij : i ≠ j)
    (U V : TwoQubitUnitary) (ψ : PauliString Site → ℝ) (P : PauliString Site) :
    pauliSamplerFixed i j hij U ψ P - pauliSamplerFixed i j hij V ψ P =
      pauliSamplerFixed i j hij U (pauliGateActiveVector i j ψ) P -
      pauliSamplerFixed i j hij V (pauliGateActiveVector i j ψ) P := by
  unfold pauliSamplerFixed amplitudeLocalUpdate
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change twoQubitPauliTransfer U (P i,P j) a *
      ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a,fun s => P s)) -
      twoQubitPauliTransfer V (P i,P j) a *
      ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a,fun s => P s)) = _
  change _ = twoQubitPauliTransfer U (P i,P j) a *
    pauliGateActiveVector i j ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a, fun s => P s)) -
    twoQubitPauliTransfer V (P i,P j) a *
    pauliGateActiveVector i j ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a, fun s => P s))
  simp only [pairSplitEquiv_symm_pauli, pauliGateActiveVector,
    pauliPairUpdate_left i j hij, pauliPairUpdate_right, Prod.mk.eta]
  by_cases ha : a = (0,0)
  · subst a
    simp [twoQubitPauliTransfer]
  · simp [ha]

theorem pauliSamplerFixed_sub_mass_le (i j : Site) (hij : i ≠ j)
    (U V : TwoQubitUnitary) (ψ : PauliString Site → ℝ) :
    amplitudeMass (fun P => pauliSamplerFixed i j hij U ψ P - pauliSamplerFixed i j hij V ψ P) ≤
      4 * pauliGateActiveMass i j ψ := by
  have he : (fun P => pauliSamplerFixed i j hij U ψ P - pauliSamplerFixed i j hij V ψ P) =
      fun P => pauliSamplerFixed i j hij U (pauliGateActiveVector i j ψ) P -
        pauliSamplerFixed i j hij V (pauliGateActiveVector i j ψ) P :=
    funext (pauliSamplerFixed_sub_active i j hij U V ψ)
  rw [he]
  have h := amplitudeMass_sub_le
    (pauliSamplerFixed i j hij U (pauliGateActiveVector i j ψ))
    (pauliSamplerFixed i j hij V (pauliGateActiveVector i j ψ))
  rw [amplitudeMass_pauliSamplerFixed, amplitudeMass_pauliSamplerFixed] at h
  exact h.trans_eq (by unfold pauliGateActiveMass; ring)

/-- Any prescribed continuation preserves mass. -/
theorem randomLinearEvolution_pauli_mass
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (ψ : PauliString Site → ℝ) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    amplitudeMass (randomLinearEvolution (pauliCircuitTransfer bond) ψ n x) = amplitudeMass ψ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change amplitudeMass (Matrix.mulVec (pauliPairTransfer (bond n).1 (bond n).2 (x (Fin.last n)))
      (randomLinearEvolution (pauliCircuitTransfer bond) ψ n (fun a => x a.castSucc))) = _
    rw [amplitudeMass_pauliPairTransfer _ _ (hbond n), ih]

lemma randomLinearEvolution_sub {G Q : Type*} [Fintype Q]
    (K : ℕ → G → Matrix Q Q ℝ) (v w : Q → ℝ) (n : ℕ) (x : Fin n → G) :
    randomLinearEvolution K (fun q => v q - w q) n x =
      fun q => randomLinearEvolution K v n x q - randomLinearEvolution K w n x q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [randomLinearEvolution, ih]
    exact Matrix.mulVec_sub _ _ _

/-- A common physical continuation preserves squared distance exactly. -/
theorem randomLinearEvolution_pauli_distance
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (v w : PauliString Site → ℝ) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    amplitudeMass (fun P => randomLinearEvolution (pauliCircuitTransfer bond) v n x P -
      randomLinearEvolution (pauliCircuitTransfer bond) w n x P) =
      amplitudeMass (fun P => v P - w P) := by
  rw [← randomLinearEvolution_sub, randomLinearEvolution_pauli_mass bond hbond]

/-- After an arbitrary common continuation, changing one actual local unitary
changes the endpoint sign readout by at most four times the square root of the
prefix's active Pauli mass on that gate bond. -/
theorem pauliGateChange_endpoint_le
    (i j : Site) (hij : i ≠ j) (U V : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeMass ψ = 1)
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (probe : Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    |amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) (pauliSamplerFixed i j hij U ψ) n x) -
     amplitudeSignReadout (fun P => pauliEndpointSign (P probe))
      (randomLinearEvolution (pauliCircuitTransfer bond) (pauliSamplerFixed i j hij V ψ) n x)| ≤
      4 * Real.sqrt (pauliGateActiveMass i j ψ) := by
  apply amplitudeSignReadout_sub_le_four_sqrt
  · intro P
    unfold pauliEndpointSign
    split_ifs <;> norm_num
  · rw [randomLinearEvolution_pauli_mass bond hbond, amplitudeMass_pauliSamplerFixed, hψ]
  · rw [randomLinearEvolution_pauli_mass bond hbond, amplitudeMass_pauliSamplerFixed, hψ]
  · exact pauliGateActiveMass_nonneg _ _ _
  · rw [randomLinearEvolution_pauli_distance bond hbond]
    exact pauliSamplerFixed_sub_mass_le i j hij U V ψ

end Fluctuations
