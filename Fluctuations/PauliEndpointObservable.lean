import Fluctuations.PauliCircuitBridge

open MeasureTheory
open scoped BigOperators Matrix

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

omit [DecidableEq Site] in
@[simp] lemma tensorMatrix_one : tensorMatrix (fun _ : Site => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorMatrix]
  · simp only [tensorMatrix, Matrix.one_apply, if_neg h]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

omit [DecidableEq Site] in
lemma tensorMatrix_smul (c : Site → ℂ) (Q : Site → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix (fun s => c s • Q s) = (∏ s, c s) • tensorMatrix Q := by
  ext x y
  simp [tensorMatrix, Matrix.smul_apply, Finset.prod_mul_distrib]

/-- The actual Z probe at one specified site. -/
def pauliSiteZ (j : Site) : PauliString Site := fun s => if s = j then 3 else 0

def pauliEndpointSign (p : Fin 4) : ℝ := if p = 1 ∨ p = 2 then -1 else 1

lemma pauliMatrix_Z_square (p : Fin 4) :
    (pauliMatrix p * pauliMatrix 3) * (pauliMatrix p * pauliMatrix 3) =
      (pauliEndpointSign p : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliMatrix, pauliEndpointSign, Fin.ext_iff, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

/-- Each diagonal Pauli contribution to the endpoint OTOC is a scalar matrix,
so its state expectation needs only trace one. -/
theorem pauliString_siteZ_square (P : PauliString Site) (j : Site) :
    (pauliStringMatrix P * pauliStringMatrix (pauliSiteZ j)) *
        (pauliStringMatrix P * pauliStringMatrix (pauliSiteZ j)) =
      (pauliEndpointSign (P j) : ℂ) • (1 : QubitOperator Site) := by
  unfold pauliStringMatrix
  rw [tensorMatrix_mul, tensorMatrix_mul]
  have he : (fun s => (pauliMatrix (P s) * pauliMatrix (pauliSiteZ j s)) *
      (pauliMatrix (P s) * pauliMatrix (pauliSiteZ j s))) =
      fun s => (if s = j then (pauliEndpointSign (P j) : ℂ) else 1) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext s
    by_cases h : s = j
    · subst s
      simpa [pauliSiteZ] using pauliMatrix_Z_square (P j)
    · simp [pauliSiteZ, h, pauliMatrix_involution]
  rw [he, tensorMatrix_smul, tensorMatrix_one]
  congr 1
  simp

theorem pauliOTOCWeight_siteZ_diagonal (ρ : QubitOperator Site) (hρ : Matrix.trace ρ = 1)
    (j : Site) (P : PauliString Site) :
    pauliOTOCWeight ρ (pauliStringMatrix (pauliSiteZ j)) P P = pauliEndpointSign (P j) := by
  unfold pauliOTOCWeight
  rw [pauliString_siteZ_square, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, hρ]
  simp

/-- The actual endpoint OTOC mean equals the Pauli Markov expectation of its
endpoint commutation sign, uniformly over all trace-one input states. -/
theorem pauliCircuit_haar_endpoint_otoc
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ : QubitOperator Site) (hρ : Matrix.trace ρ = 1)
    (j : Site) (n : ℕ) :
    (∫ x : Fin n → TwoQubitUnitary,
      globalOTOC ρ (pauliStringMatrix P₀) (pauliStringMatrix (pauliSiteZ j)) 1
        (pauliCircuitUnitary bond hbond n x) ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ∑ P : PauliString Site, (pauliEndpointSign (P j) : ℂ) *
        (markovWeightEvolution (pauliCircuitHaarKernel bond) (pauliInitialVector P₀) n P : ℂ) := by
  rw [pauliCircuit_haar_otoc_markov]
  simp_rw [pauliOTOCWeight_siteZ_diagonal ρ hρ]

end Fluctuations
