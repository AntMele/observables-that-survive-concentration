import Fluctuations.PauliStringQuantum
import Fluctuations.ProductKernelEvolution

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

def pauliPairUnitary (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary) :
    GlobalUnitary (QubitState Site) :=
  ⟨pauliPairEmbedding i j hij U.val, pauliPairEmbedding_unitary i j hij U⟩

/-- The actual chronological product of canonically embedded two-qubit gates. -/
def pauliCircuitUnitary (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2) :
    (n : ℕ) → (Fin n → TwoQubitUnitary) → GlobalUnitary (QubitState Site)
  | 0, _ => 1
  | n + 1, x => pauliCircuitUnitary bond hbond n (fun a => x a.castSucc) *
      pauliPairUnitary (bond n).1 (bond n).2 (hbond n) (x (Fin.last n))

noncomputable def pauliInitialVector (P₀ : PauliString Site) : PauliString Site → ℝ :=
  fun P => if P = P₀ then 1 else 0

noncomputable def pauliCircuitTransfer (bond : ℕ → Site × Site) :
    ℕ → TwoQubitUnitary → Matrix (PauliString Site) (PauliString Site) ℝ :=
  fun t => pauliPairTransfer (bond t).1 (bond t).2

noncomputable def pauliCircuitHaarKernel (bond : ℕ → Site × Site) :
    ℕ → Matrix (PauliString Site) (PauliString Site) ℝ :=
  fun t => pauliPairKernel (bond t).1 (bond t).2

lemma pauliCircuitTransfer_continuous (bond : ℕ → Site × Site) (t : ℕ) :
    Continuous (pauliCircuitTransfer bond t) :=
  pauliPairTransfer_continuous (bond t).1 (bond t).2

/-- The actual Heisenberg-evolved Pauli is the coefficient evolution supplied
to the independent-product integration theorem. This is an operator identity. -/
theorem pauliCircuit_conjugate_expansion
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    globalHaarConjugate (pauliStringMatrix P₀) (pauliCircuitUnitary bond hbond n x) =
      ∑ P : PauliString Site,
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n x P : ℂ) •
          pauliStringMatrix P := by
  classical
  induction n with
  | zero =>
    simp [pauliCircuitUnitary, globalHaarConjugate, randomLinearEvolution, pauliInitialVector]
  | succ n ih =>
    change globalHaarConjugate (pauliStringMatrix P₀)
      (pauliCircuitUnitary bond hbond n (fun a => x a.castSucc) *
        pauliPairUnitary (bond n).1 (bond n).2 (hbond n) (x (Fin.last n))) = _
    rw [globalHaarConjugate_mul_right, ih]
    exact pauliPairEmbedding_conjugate_expansion (bond n).1 (bond n).2 (hbond n)
      (x (Fin.last n))
      (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n
        (fun a => x a.castSucc))

/-- The literal matrix-trace weights for the first-order OTOC, allowing any
input state and any probe. -/
noncomputable def pauliOTOCWeight (ρ M : QubitOperator Site) :
    Matrix (PauliString Site) (PauliString Site) ℂ :=
  fun P Q => Matrix.trace (ρ * ((pauliStringMatrix P * M) * (pauliStringMatrix Q * M)))

theorem pauliCircuit_otoc_quadratic
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ M : QubitOperator Site)
    (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    globalOTOC ρ (pauliStringMatrix P₀) M 1 (pauliCircuitUnitary bond hbond n x) =
      quadraticCoefficientObservable (pauliOTOCWeight ρ M)
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) n x) := by
  change Matrix.trace (ρ * ((globalHaarConjugate (pauliStringMatrix P₀)
    (pauliCircuitUnitary bond hbond n x) * M) ^ (2 * 1))) = _
  rw [pauliCircuit_conjugate_expansion, Nat.mul_one, pow_two]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  unfold quadraticCoefficientObservable pauliOTOCWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  intro Q _
  simp only [Complex.ofReal_mul]
  ring

omit [DecidableEq Site] in
lemma pauliInitialVector_covariance (P₀ P Q : PauliString Site) :
    pauliInitialVector P₀ P * pauliInitialVector P₀ Q =
      if P = Q then pauliInitialVector P₀ P else 0 := by
  classical
  by_cases hP : P = P₀ <;> by_cases hQ : Q = P₀ <;>
    simp_all [pauliInitialVector, eq_comm]

/-- The actual product-Haar Pauli covariance is diagonal and obeys the
derived local Markov kernel. No quantum-to-Markov correspondence is assumed. -/
theorem pauliCircuit_haar_covariance
    (bond : ℕ → Site × Site) (P₀ : PauliString Site) (n : ℕ) (P Q : PauliString Site) :
    fullSecondMomentEvolution (globalHaar TwoQubitBasis) (pauliCircuitTransfer bond)
      (pauliInitialVector P₀) n P Q =
      if P = Q then markovWeightEvolution (pauliCircuitHaarKernel bond)
        (pauliInitialVector P₀) n P else 0 := by
  apply fullSecondMomentEvolution_diagonal
  · exact pauliInitialVector_covariance P₀
  · intro t P Q R
    exact pauliPairTransfer_haar_column_covariance (bond t).1 (bond t).2 R P Q

/-- Genuine finite-circuit Haar-to-Pauli-Markov identity for the actual OTOC.
The circuit can be any prescribed ordered list of physical two-site gates. -/
theorem pauliCircuit_haar_otoc_markov
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ M : QubitOperator Site) (n : ℕ) :
    (∫ x : Fin n → TwoQubitUnitary,
      globalOTOC ρ (pauliStringMatrix P₀) M 1 (pauliCircuitUnitary bond hbond n x)
        ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ∑ P : PauliString Site, pauliOTOCWeight ρ M P P *
        (markovWeightEvolution (pauliCircuitHaarKernel bond) (pauliInitialVector P₀) n P : ℂ) := by
  classical
  simp_rw [pauliCircuit_otoc_quadratic]
  rw [integral_randomLinearEvolution_quadratic (globalHaar TwoQubitBasis)
    (pauliCircuitTransfer bond) (pauliCircuitTransfer_continuous bond)]
  simp_rw [pauliCircuit_haar_covariance]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The actual conditional circuit OTOC with one gate fixed, retaining the
off-diagonal moments created by that fixed gate until later Haar averaging. -/
theorem pauliCircuit_fixed_gate_otoc
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ M : QubitOperator Site) (n : ℕ)
    (t : Fin n) (g : TwoQubitUnitary) :
    coordinateAverage (fun _ : Fin n => globalHaar TwoQubitBasis) t
      (fun x => globalOTOC ρ (pauliStringMatrix P₀) M 1
        (pauliCircuitUnitary bond hbond n x)) g =
      ∑ P : PauliString Site, ∑ Q : PauliString Site, pauliOTOCWeight ρ M P Q *
        (fullSecondMomentEvolution (globalHaar TwoQubitBasis)
          (freezeGateKernel (pauliCircuitTransfer bond) t.val g) (pauliInitialVector P₀) n P Q : ℂ) := by
  simp_rw [pauliCircuit_otoc_quadratic]
  exact coordinateAverage_randomLinearEvolution_quadratic (globalHaar TwoQubitBasis)
    (pauliCircuitTransfer bond) (pauliCircuitTransfer_continuous bond)
    (pauliInitialVector P₀) n t g (pauliOTOCWeight ρ M)

end Fluctuations
