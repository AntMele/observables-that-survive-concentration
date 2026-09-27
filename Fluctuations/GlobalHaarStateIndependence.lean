import Fluctuations.GlobalHaarMean

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A diagonal unitary that changes the sign of one coordinate. -/
def coordinateSignUnitary (i : N) : GlobalUnitary N :=
  ⟨Matrix.diagonal (fun j => if j = i then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff]
    change Matrix.diagonal _ * (Matrix.diagonal _).conjTranspose = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext j l
    by_cases hjl : j = l
    · subst l
      by_cases hji : j = i <;> simp [hji]
    · simp [Matrix.diagonal_apply, hjl]⟩

/-- Every diagonal probe forces the global even-OTOC matrix mean to be diagonal. -/
theorem globalHaarOTOCMatrixMean_diagonal (B : Matrix N N ℂ) (q : N → ℂ)
    (k : ℕ) (i j : N) (hij : i ≠ j) :
    globalHaarOTOCMatrixMean B (Matrix.diagonal q) k i j = 0 := by
  have h := globalHaarOTOCMatrixMean_commute B (Matrix.diagonal q) k
    (coordinateSignUnitary i)
    (Or.inl (Matrix.commute_diagonal _ _).eq)
  have he := congrArg (fun X : Matrix N N ℂ => X i j) h.eq
  simp only [coordinateSignUnitary, Matrix.diagonal_mul, Matrix.mul_diagonal,
    if_true, if_neg hij.symm, neg_one_mul, mul_one] at he
  linear_combination -(1 / 2 : ℂ) * he

/-- A permutation matrix regarded as a genuine global unitary. -/
def permutationUnitary (σ : Equiv.Perm N) : GlobalUnitary N :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff]
    change σ.permMatrix ℂ * (σ.permMatrix ℂ).conjTranspose = 1
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Equiv.Perm.permMatrix, Matrix.submatrix_apply, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Matrix.one_apply]⟩

lemma permutationUnitary_diagonal_commute (q : N → ℂ) (σ : Equiv.Perm N)
    (h : ∀ i, q (σ i) = q i) :
    (permutationUnitary σ).val * Matrix.diagonal q =
      Matrix.diagonal q * (permutationUnitary σ).val := by
  change σ.permMatrix ℂ * Matrix.diagonal q = Matrix.diagonal q * σ.permMatrix ℂ
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases hij : σ i = j
  · subst j
    simp [h]
  · simp [hij]

lemma permutationUnitary_diagonal_anticommute (q : N → ℂ) (σ : Equiv.Perm N)
    (h : ∀ i, q (σ i) = -q i) :
    (permutationUnitary σ).val * Matrix.diagonal q =
      -(Matrix.diagonal q * (permutationUnitary σ).val) := by
  change σ.permMatrix ℂ * Matrix.diagonal q = -(Matrix.diagonal q * σ.permMatrix ℂ)
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.neg_apply]
  by_cases hij : σ i = j
  · subst j
    simp [h]
  · simp [hij]

/-- A signed permutation symmetry forces equality of the corresponding
diagonal entries of the actual Haar matrix mean. -/
lemma globalHaarOTOCMatrixMean_diagonal_permute (B : Matrix N N ℂ) (q : N → ℂ)
    (k : ℕ) (σ : Equiv.Perm N)
    (hσ : (∀ i, q (σ i) = q i) ∨ (∀ i, q (σ i) = -q i)) (i : N) :
    globalHaarOTOCMatrixMean B (Matrix.diagonal q) k (σ i) (σ i) =
      globalHaarOTOCMatrixMean B (Matrix.diagonal q) k i i := by
  have hs : (permutationUnitary σ).val * Matrix.diagonal q =
      Matrix.diagonal q * (permutationUnitary σ).val ∨
      (permutationUnitary σ).val * Matrix.diagonal q =
        -(Matrix.diagonal q * (permutationUnitary σ).val) :=
    hσ.imp (permutationUnitary_diagonal_commute q σ)
      (permutationUnitary_diagonal_anticommute q σ)
  have h := (globalHaarOTOCMatrixMean_commute B (Matrix.diagonal q) k
    (permutationUnitary σ) hs).eq
  have he := congrArg (fun X : Matrix N N ℂ => X i (σ i)) h
  simpa only [permutationUnitary, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, id_eq,
    Equiv.symm_apply_apply] using he

/-- A concrete algebraic criterion on a diagonal probe: its signed permutation
symmetries act transitively on the basis coordinates. -/
def SignedPermutationTransitive (q : N → ℂ) : Prop :=
  ∀ i j : N, ∃ σ : Equiv.Perm N, σ i = j ∧
    ((∀ l, q (σ l) = q l) ∨ (∀ l, q (σ l) = -q l))

theorem globalHaarOTOCMatrixMean_scalar_of_transitive [Nonempty N]
    (B : Matrix N N ℂ) (q : N → ℂ) (hq : SignedPermutationTransitive q) (k : ℕ) :
    ∃ α : ℂ, globalHaarOTOCMatrixMean B (Matrix.diagonal q) k = α • (1 : Matrix N N ℂ) := by
  classical
  let i₀ : N := Classical.choice inferInstance
  refine ⟨globalHaarOTOCMatrixMean B (Matrix.diagonal q) k i₀ i₀, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    obtain ⟨σ, hσi, hσ⟩ := hq i₀ i
    have he := globalHaarOTOCMatrixMean_diagonal_permute B q k σ hσ i₀
    simpa [hσi] using he
  · simp [globalHaarOTOCMatrixMean_diagonal B q k i j hij, Matrix.one_apply, hij]

theorem globalHaarOTOCMean_state_independent_of_transitive [Nonempty N]
    (B : Matrix N N ℂ) (q : N → ℂ) (hq : SignedPermutationTransitive q) (k : ℕ) :
    ∃ α : ℂ, ∀ ρ : Matrix N N ℂ, Matrix.trace ρ = 1 →
      globalHaarOTOCMean ρ B (Matrix.diagonal q) k = α := by
  obtain ⟨α, hα⟩ := globalHaarOTOCMatrixMean_scalar_of_transitive B q hq k
  refine ⟨α, ?_⟩
  intro ρ hρ
  rw [globalHaarOTOCMean_eq_trace_matrixMean, hα]
  simp [hρ]

/-- The eigenvalue of the computational-basis Pauli Z on the first factor. -/
def balancedZSign {S : Type*} (i : Bool × S) : ℂ := if i.1 then 1 else -1

/-- The genuine Pauli Z on a two-dimensional factor, with arbitrary spectators. -/
def balancedZProbe (S : Type*) [Fintype S] [DecidableEq S] :
    Matrix (Bool × S) (Bool × S) ℂ := Matrix.diagonal balancedZSign

lemma balancedZSign_transitive (S : Type*) [Fintype S] [DecidableEq S] :
    SignedPermutationTransitive (balancedZSign : Bool × S → ℂ) := by
  intro i j
  rcases i with ⟨bi, si⟩
  rcases j with ⟨bj, sj⟩
  refine ⟨Equiv.prodCongr (Equiv.swap bi bj) (Equiv.swap si sj), by simp, ?_⟩
  cases bi <;> cases bj
  · left
    intro l
    rcases l with ⟨b, s⟩
    cases b <;> simp [balancedZSign]
  · right
    intro l
    rcases l with ⟨b, s⟩
    cases b <;> simp [balancedZSign]
  · right
    intro l
    rcases l with ⟨b, s⟩
    cases b <;> simp [balancedZSign]
  · left
    intro l
    rcases l with ⟨b, s⟩
    cases b <;> simp [balancedZSign]

/-- State independence for every OTOC order and every butterfly matrix when
the probe is an actual Pauli Z with arbitrary finite spectator dimension. -/
theorem globalHaarOTOCMean_balancedZ_state_independent
    (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    (B : Matrix (Bool × S) (Bool × S) ℂ) (k : ℕ) :
    ∃ α : ℂ, ∀ ρ : Matrix (Bool × S) (Bool × S) ℂ, Matrix.trace ρ = 1 →
      globalHaarOTOCMean ρ B (balancedZProbe S) k = α :=
  globalHaarOTOCMean_state_independent_of_transitive B balancedZSign
    (balancedZSign_transitive S) k

/-- The state-independence conclusion survives every unitary change of basis
of a probe whose actual averaged OTOC matrix is scalar. -/
theorem globalHaarOTOCMatrixMean_scalar_conjugateProbe (B M : Matrix N N ℂ) (k : ℕ)
    (V : GlobalUnitary N) {α : ℂ}
    (hα : globalHaarOTOCMatrixMean B M k = α • (1 : Matrix N N ℂ)) :
    globalHaarOTOCMatrixMean B (V.val.conjTranspose * M * V.val) k =
      α • (1 : Matrix N N ℂ) := by
  rw [globalHaarOTOCMatrixMean_conjugateProbe, hα]
  have hV : V.val.conjTranspose * V.val = 1 := V.prop.1
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV]

/-- All orders and all trace-one states for any unitary conjugate of the
balanced Pauli Z probe. No smallness or state-independence premise is assumed. -/
theorem globalHaarOTOCMean_conjugateBalancedZ_state_independent
    (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    (B : Matrix (Bool × S) (Bool × S) ℂ) (k : ℕ) (V : GlobalUnitary (Bool × S)) :
    ∃ α : ℂ, ∀ ρ : Matrix (Bool × S) (Bool × S) ℂ, Matrix.trace ρ = 1 →
      globalHaarOTOCMean ρ B
        (V.val.conjTranspose * balancedZProbe S * V.val) k = α := by
  obtain ⟨α, hα⟩ := globalHaarOTOCMatrixMean_scalar_of_transitive B balancedZSign
    (balancedZSign_transitive S) k
  have hv := globalHaarOTOCMatrixMean_scalar_conjugateProbe B (balancedZProbe S) k V hα
  refine ⟨α, ?_⟩
  intro ρ hρ
  rw [globalHaarOTOCMean_eq_trace_matrixMean, hv]
  simp [hρ]

/-- The scalar mean for an actual Pauli Z probe equals the normalized trace
of the actual Haar matrix mean, uniformly for every trace-one input matrix. -/
theorem globalHaarOTOCMean_balancedZ_eq_normalized_trace
    (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
    (ρ B : Matrix (Bool × S) (Bool × S) ℂ) (hρ : Matrix.trace ρ = 1) (k : ℕ) :
    globalHaarOTOCMean ρ B (balancedZProbe S) k =
      (Fintype.card (Bool × S) : ℂ)⁻¹ *
        Matrix.trace (globalHaarOTOCMatrixMean B (balancedZProbe S) k) := by
  obtain ⟨α, hα⟩ := globalHaarOTOCMean_balancedZ_state_independent S B k
  rw [hα ρ hρ, ← hα (globalMaximallyMixedState (Bool × S)) globalMaximallyMixedState_trace,
    globalHaarOTOCMean_eq_trace_matrixMean]
  simp [globalMaximallyMixedState]

end Fluctuations
