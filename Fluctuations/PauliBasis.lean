import Mathlib

open scoped BigOperators Matrix Kronecker

namespace Fluctuations

/-- The computational-basis Pauli matrices, ordered identity, X, Y, Z. -/
def pauliMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

@[simp] theorem pauliMatrix_zero : pauliMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliMatrix, Matrix.one_apply]

theorem pauliMatrix_hermitian (p : Fin 4) : (pauliMatrix p).IsHermitian := by
  change (pauliMatrix p).conjTranspose = pauliMatrix p
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix, Matrix.conjTranspose_apply]

theorem pauliMatrix_involution (p : Fin 4) : pauliMatrix p * pauliMatrix p = 1 := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem pauliMatrix_trace (p : Fin 4) :
    Matrix.trace (pauliMatrix p) = if p = 0 then 2 else 0 := by
  fin_cases p <;> norm_num [pauliMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem pauliMatrix_trace_mul (p q : Fin 4) :
    Matrix.trace (pauliMatrix p * pauliMatrix q) = if p = q then 2 else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [pauliMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual sixteen two-qubit Pauli matrices on the product basis. -/
def twoQubitPauli (p : Fin 4 × Fin 4) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  pauliMatrix p.1 ⊗ₖ pauliMatrix p.2

@[simp] theorem twoQubitPauli_zero : twoQubitPauli (0, 0) = 1 := by
  simp [twoQubitPauli]

theorem twoQubitPauli_hermitian (p : Fin 4 × Fin 4) : (twoQubitPauli p).IsHermitian := by
  change (twoQubitPauli p).conjTranspose = twoQubitPauli p
  rw [twoQubitPauli, Matrix.conjTranspose_kronecker,
    pauliMatrix_hermitian p.1, pauliMatrix_hermitian p.2]

theorem twoQubitPauli_involution (p : Fin 4 × Fin 4) :
    twoQubitPauli p * twoQubitPauli p = 1 := by
  rw [twoQubitPauli, ← Matrix.mul_kronecker_mul,
    pauliMatrix_involution, pauliMatrix_involution, Matrix.one_kronecker_one]

theorem twoQubitPauli_trace (p : Fin 4 × Fin 4) :
    Matrix.trace (twoQubitPauli p) = if p = (0, 0) then 4 else 0 := by
  rw [twoQubitPauli, Matrix.trace_kronecker, pauliMatrix_trace, pauliMatrix_trace]
  by_cases h1 : p.1 = 0 <;> by_cases h2 : p.2 = 0 <;> norm_num [h1, h2, Prod.ext_iff]

theorem twoQubitPauli_trace_mul (p q : Fin 4 × Fin 4) :
    Matrix.trace (twoQubitPauli p * twoQubitPauli q) = if p = q then 4 else 0 := by
  rw [twoQubitPauli, twoQubitPauli, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    pauliMatrix_trace_mul, pauliMatrix_trace_mul]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> norm_num [h1, h2, Prod.ext_iff]

/-- Entrywise completeness of the one-qubit Pauli basis. -/
lemma pauliMatrix_completeness (a b c d : Fin 2) :
    (∑ p : Fin 4, pauliMatrix p a b * pauliMatrix p c d) =
      if a = d ∧ b = c then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauliMatrix, Fin.sum_univ_four]

/-- Entrywise completeness on the actual four-dimensional product basis. -/
lemma twoQubitPauli_completeness (a b c d : Fin 2 × Fin 2) :
    (∑ p : Fin 4 × Fin 4, twoQubitPauli p a b * twoQubitPauli p c d) =
      if a = d ∧ b = c then 4 else 0 := by
  have hf : (∑ p : Fin 4 × Fin 4, twoQubitPauli p a b * twoQubitPauli p c d) =
      (∑ p : Fin 4, pauliMatrix p a.1 b.1 * pauliMatrix p c.1 d.1) *
      (∑ p : Fin 4, pauliMatrix p a.2 b.2 * pauliMatrix p c.2 d.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp only [twoQubitPauli, Matrix.kroneckerMap_apply]
    ring
  rw [hf, pauliMatrix_completeness, pauliMatrix_completeness]
  by_cases h1 : a.1 = d.1 <;> by_cases h2 : b.1 = c.1 <;>
    by_cases h3 : a.2 = d.2 <;> by_cases h4 : b.2 = c.2 <;>
    norm_num [h1, h2, h3, h4, Prod.ext_iff]

/-- Reconstruction of every complex two-qubit matrix from its actual Pauli traces. -/
theorem twoQubitPauli_reconstruction (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (∑ p : Fin 4 × Fin 4, Matrix.trace (twoQubitPauli p * M) • twoQubitPauli p) =
      (4 : ℂ) • M := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul]
  calc
    (∑ p : Fin 4 × Fin 4, ∑ a, ∑ b, twoQubitPauli p a b * M b a * twoQubitPauli p i j) =
        ∑ a, ∑ b, M b a * (∑ p : Fin 4 × Fin 4, twoQubitPauli p a b * twoQubitPauli p i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 4 * M i j := by
      simp_rw [twoQubitPauli_completeness, ite_and]
      simp
      ring

/-- The usual Pauli expansion, normalized by the physical dimension four. -/
theorem twoQubitPauli_expansion (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    M = ∑ p : Fin 4 × Fin 4, (Matrix.trace (twoQubitPauli p * M) / 4) • twoQubitPauli p := by
  have h := congrArg (fun A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => (1 / 4 : ℂ) • A)
    (twoQubitPauli_reconstruction M)
  simpa [Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm] using h.symm

/-- Bilinear Parseval identity for the actual two-qubit Pauli basis. -/
theorem twoQubitPauli_trace_mul_parseval
    (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.trace (A * B) = (1 / 4 : ℂ) *
      ∑ p : Fin 4 × Fin 4, Matrix.trace (twoQubitPauli p * A) *
        Matrix.trace (twoQubitPauli p * B) := by
  conv_lhs => rw [twoQubitPauli_expansion B]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.trace_mul_comm A]
  ring

end Fluctuations
