import Fluctuations.SimulationPerturbation

open scoped BigOperators Matrix

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma tensorMatrix_trace (Q : Site → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (tensorMatrix Q) = ∏ s, Matrix.trace (Q s) := by
  simp only [Matrix.trace, Matrix.diag, tensorMatrix]
  exact (Fintype.prod_sum (fun s z => Q s z z)).symm

theorem pauliStringMatrix_trace_mul (P Q : PauliString Site) :
    Matrix.trace (pauliStringMatrix P * pauliStringMatrix Q) =
      if P = Q then (Fintype.card (QubitState Site) : ℂ) else 0 := by
  rw [pauliStringMatrix, pauliStringMatrix, tensorMatrix_mul, tensorMatrix_trace]
  simp_rw [pauliMatrix_trace_mul]
  by_cases h : P = Q
  · subst Q
    simp [QubitState]
  · rw [if_neg h]
    obtain ⟨s, hs⟩ : ∃ s, P s ≠ Q s := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

lemma pauliMatrix_Z_conjugate (p : Fin 4) :
    pauliMatrix 3 * pauliMatrix p * pauliMatrix 3 =
      (pauliEndpointSign p : ℂ) • pauliMatrix p := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliMatrix, pauliEndpointSign, Fin.ext_iff, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliStringMatrix_siteZ_conjugate (P : PauliString Site) (j : Site) :
    pauliStringMatrix (pauliSiteZ j) * pauliStringMatrix P *
      pauliStringMatrix (pauliSiteZ j) = (pauliEndpointSign (P j) : ℂ) • pauliStringMatrix P := by
  unfold pauliStringMatrix
  rw [tensorMatrix_mul, tensorMatrix_mul]
  have he : (fun s => pauliMatrix (pauliSiteZ j s) * pauliMatrix (P s) *
      pauliMatrix (pauliSiteZ j s)) = fun s =>
      (if s = j then (pauliEndpointSign (P j) : ℂ) else 1) • pauliMatrix (P s) := by
    funext s
    by_cases h : s = j
    · subst s
      simpa [pauliSiteZ] using pauliMatrix_Z_conjugate (P j)
    · simp [pauliSiteZ, h]
  rw [he, tensorMatrix_smul]
  simp

/-- At infinite temperature, unequal Pauli strings have zero OTOC weight.
This statement is pointwise and does not use a Haar average. -/
theorem pauliOTOCWeight_maximallyMixed (P Q : PauliString Site) (j : Site) :
    pauliOTOCWeight (globalMaximallyMixedState (QubitState Site))
      (pauliStringMatrix (pauliSiteZ j)) P Q =
      if P = Q then (pauliEndpointSign (P j) : ℂ) else 0 := by
  unfold pauliOTOCWeight globalMaximallyMixedState
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
  rw [show (pauliStringMatrix P * pauliStringMatrix (pauliSiteZ j)) *
      (pauliStringMatrix Q * pauliStringMatrix (pauliSiteZ j)) =
      pauliStringMatrix P * (pauliStringMatrix (pauliSiteZ j) * pauliStringMatrix Q *
      pauliStringMatrix (pauliSiteZ j)) by simp only [Matrix.mul_assoc]]
  rw [pauliStringMatrix_siteZ_conjugate, Matrix.mul_smul, Matrix.trace_smul,
    pauliStringMatrix_trace_mul]
  by_cases h : P = Q
  · subst Q
    simp only [ite_true, smul_eq_mul]
    have hn : (Fintype.card (QubitState Site) : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (QubitState Site) ≠ 0)
    field_simp
  · simp [h]

/-- The exact observable evaluated by the sign sampler, for every fixed circuit. -/
theorem pauliCircuit_infiniteTemperature_sign
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (j : Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    globalOTOC (globalMaximallyMixedState (QubitState Site)) (pauliStringMatrix P₀)
      (pauliStringMatrix (pauliSiteZ j)) 1 (pauliCircuitUnitary bond hbond n x) =
      (amplitudeSignReadout (fun P => pauliEndpointSign (P j))
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n x) : ℂ) := by
  rw [pauliCircuit_otoc_quadratic]
  unfold quadraticCoefficientObservable amplitudeSignReadout
  simp_rw [pauliOTOCWeight_maximallyMixed]
  simp [Complex.ofReal_sum, Complex.ofReal_mul, pow_two]

end Fluctuations
