import Fluctuations.GlobalHaarFirstOrder
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Equivariance under genuine complex unitary conjugation. -/
def UnitaryConjugationEquivariant (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) : Prop :=
  ∀ (X : Matrix N N ℂ) (S : GlobalUnitary N),
    T (S.val.conjTranspose * X * S.val) = S.val.conjTranspose * T X * S.val

lemma diagonal_conjugation_sign (q : N → ℂ) (i : N) :
    (coordinateSignUnitary i).val.conjTranspose * Matrix.diagonal q *
      (coordinateSignUnitary i).val = Matrix.diagonal q := by
  change (Matrix.diagonal _).conjTranspose * Matrix.diagonal q * Matrix.diagonal _ = _
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  ext j
  by_cases h : j = i <;> simp [h]

lemma equivariant_diagonal_offdiag (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hT : UnitaryConjugationEquivariant T) (q : N → ℂ) (i j : N) (hij : i ≠ j) :
    T (Matrix.diagonal q) i j = 0 := by
  have h := hT (Matrix.diagonal q) (coordinateSignUnitary i)
  rw [diagonal_conjugation_sign] at h
  have he := congrArg (fun A : Matrix N N ℂ => A i j) h
  simp only [coordinateSignUnitary, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, if_true, if_neg hij.symm,
    Pi.star_apply, star_neg, star_one, neg_one_mul, mul_one] at he
  linear_combination (1 / 2 : ℂ) * he

lemma permutationUnitary_conjugation (σ : Equiv.Perm N) (X : Matrix N N ℂ) (i j : N) :
    ((permutationUnitary σ).val.conjTranspose * X * (permutationUnitary σ).val)
      (σ i) (σ j) = X i j := by
  simp only [permutationUnitary, Matrix.conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply, Equiv.Perm.inv_apply_self]

lemma permutationUnitary_conjugation_diagonal (σ : Equiv.Perm N) (q : N → ℂ) :
    (permutationUnitary σ).val.conjTranspose * Matrix.diagonal q *
      (permutationUnitary σ).val = Matrix.diagonal (q ∘ σ.symm) := by
  ext i j
  obtain ⟨i, rfl⟩ := σ.surjective i
  obtain ⟨j, rfl⟩ := σ.surjective j
  rw [permutationUnitary_conjugation]
  simp [Matrix.diagonal_apply]

lemma equivariant_diagonal_permute (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hT : UnitaryConjugationEquivariant T) (σ : Equiv.Perm N) (q : N → ℂ) (i : N) :
    T (Matrix.diagonal (q ∘ σ.symm)) (σ i) (σ i) = T (Matrix.diagonal q) i i := by
  have h := hT (Matrix.diagonal q) (permutationUnitary σ)
  rw [permutationUnitary_conjugation_diagonal] at h
  exact (congrArg (fun X : Matrix N N ℂ => X (σ i) (σ i)) h).trans
    (permutationUnitary_conjugation σ (T (Matrix.diagonal q)) i i)

omit [Fintype N] in
lemma exists_permutation_pair (i j a b : N) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm N, σ i = a ∧ σ j = b := by
  let τ := Equiv.swap i a
  have hτi : τ i = a := Equiv.swap_apply_left i a
  have hτja : τ j ≠ a := by
    rw [← hτi]
    exact fun h => hij (τ.injective h).symm
  refine ⟨τ.trans (Equiv.swap (τ j) b), ?_, ?_⟩
  · simp only [Equiv.trans_apply, hτi]
    exact Equiv.swap_apply_of_ne_of_ne hτja.symm hab
  · exact Equiv.swap_apply_left (τ j) b

noncomputable def coordinateProjection (i : N) : Matrix N N ℂ :=
  Matrix.diagonal (fun j => if j = i then 1 else 0)

omit [Fintype N] in
lemma coordinateProjection_permute (σ : Equiv.Perm N) (i : N) :
    Matrix.diagonal ((fun j => if j = i then (1 : ℂ) else 0) ∘ σ.symm) =
      coordinateProjection (σ i) := by
  congr 1
  ext j
  simp only [Function.comp_apply]
  simp [Equiv.symm_apply_eq]

lemma equivariant_projection_permute (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hT : UnitaryConjugationEquivariant T) (σ : Equiv.Perm N) (i j : N) :
    T (coordinateProjection (σ i)) (σ j) (σ j) = T (coordinateProjection i) j j := by
  have h := equivariant_diagonal_permute T hT σ
    (fun j => if j = i then (1 : ℂ) else 0) j
  rw [coordinateProjection_permute] at h
  exact h

/-- An equivariant map has two common coefficients on coordinate projections. -/
theorem equivariant_coordinateProjection [Nontrivial N]
    (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) (hT : UnitaryConjugationEquivariant T) :
    ∃ a b : ℂ, ∀ i : N, T (coordinateProjection i) =
      a • coordinateProjection i + b • (1 : Matrix N N ℂ) := by
  obtain ⟨p, q, hpq⟩ := exists_pair_ne N
  let u := T (coordinateProjection p) p p
  let v := T (coordinateProjection p) q q
  refine ⟨u - v, v, ?_⟩
  intro i
  ext j l
  by_cases hjl : j = l
  · subst l
    by_cases hji : j = i
    · subst j
      have h := equivariant_projection_permute T hT (Equiv.swap p i) p p
      simp only [Equiv.swap_apply_left] at h
      simpa [coordinateProjection, u, v] using h
    · obtain ⟨σ, hσp, hσq⟩ := exists_permutation_pair p q i j hpq (fun h => hji h.symm)
      have h := equivariant_projection_permute T hT σ p q
      simpa [hσp, hσq, coordinateProjection, hji, v] using h
  · have h := equivariant_diagonal_offdiag T hT
      (fun j => if j = i then (1 : ℂ) else 0) j l hjl
    simpa [coordinateProjection, Matrix.diagonal_apply, Matrix.one_apply, hjl] using h

lemma diagonal_eq_sum_coordinateProjection (q : N → ℂ) :
    Matrix.diagonal q = ∑ i : N, q i • coordinateProjection i := by
  ext j l
  by_cases hjl : j = l
  · subst l
    simp [coordinateProjection, Matrix.sum_apply]
  · simp [coordinateProjection, Matrix.sum_apply, hjl]

lemma linear_on_diagonal (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) (a b : ℂ)
    (h : ∀ i : N, T (coordinateProjection i) =
      a • coordinateProjection i + b • (1 : Matrix N N ℂ)) (q : N → ℂ) :
    T (Matrix.diagonal q) = a • Matrix.diagonal q +
      (b * Matrix.trace (Matrix.diagonal q)) • (1 : Matrix N N ℂ) := by
  rw [diagonal_eq_sum_coordinateProjection q, map_sum]
  simp_rw [map_smul, h, smul_add, smul_smul]
  rw [Finset.sum_add_distrib]
  have hcomm (i : N) : q i * a = a * q i := mul_comm _ _
  simp_rw [hcomm, ← smul_smul]
  rw [← Finset.smul_sum, ← diagonal_eq_sum_coordinateProjection]
  congr 1
  rw [← Finset.sum_smul]
  simp [smul_smul, Matrix.trace_diagonal, mul_comm]

lemma equivariant_on_hermitian (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hT : UnitaryConjugationEquivariant T) (a b : ℂ)
    (h : ∀ i : N, T (coordinateProjection i) =
      a • coordinateProjection i + b • (1 : Matrix N N ℂ))
    (X : Matrix N N ℂ) (hX : X.IsHermitian) :
    T X = a • X + (b * Matrix.trace X) • (1 : Matrix N N ℂ) := by
  let U := hX.eigenvectorUnitary
  let D : Matrix N N ℂ := Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)
  have hs : U.val * D * U.val.conjTranspose = X := hX.spectral_theorem.symm
  have ht : Matrix.trace D = Matrix.trace X := by
    have hD : U.val.conjTranspose * X * U.val = D :=
      hX.star_mul_self_mul_eq_diagonal
    rw [← hD]
    exact globalHaarConjugate_trace X U
  have he := hT D (star U)
  simp only [unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at he
  rw [hs] at he
  have hd := linear_on_diagonal T a b h (RCLike.ofReal ∘ hX.eigenvalues)
  change T D = _ at hd
  rw [hd, ht] at he
  have hU : U.val * U.val.conjTranspose = 1 := U.prop.2
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU] at he
  change T X = a • (U.val * D * U.val.conjTranspose) + (b * Matrix.trace X) • 1 at he
  rwa [hs] at he

/-- Scalar plus trace form, bundled as a complex linear map. -/
noncomputable def scalarTraceLinear (a b : ℂ) : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ where
  toFun X := a • X + (b * Matrix.trace X) • (1 : Matrix N N ℂ)
  map_add' X Y := by
    simp only [Matrix.trace_add, mul_add, add_smul, smul_add]
    module
  map_smul' c X := by
    simp [Matrix.trace_smul, smul_add, smul_smul, mul_comm, mul_left_comm]

omit [Fintype N] [DecidableEq N] in
/-- A complex linear map is determined by its values on Hermitian matrices. -/
lemma matrix_linear_ext_hermitian (T S : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ)
    (h : ∀ X : Matrix N N ℂ, X.IsHermitian → T X = S X) : T = S := by
  ext X : 1
  have hr : (realPart X : Matrix N N ℂ).IsHermitian := (realPart X).prop
  have hi : (imaginaryPart X : Matrix N N ℂ).IsHermitian := (imaginaryPart X).prop
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
  conv_rhs => rw [← realPart_add_I_smul_imaginaryPart X]
  simp only [map_add, map_smul, h _ hr, h _ hi]

/-- Full classification of complex linear maps intertwining every unitary
conjugation. The proof uses coordinate symmetries and the spectral theorem. -/
theorem unitaryConjugationEquivariant_classification [Nontrivial N]
    (T : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ) (hT : UnitaryConjugationEquivariant T) :
    ∃ a b : ℂ, ∀ X : Matrix N N ℂ,
      T X = a • X + (b * Matrix.trace X) • (1 : Matrix N N ℂ) := by
  obtain ⟨a, b, h⟩ := equivariant_coordinateProjection T hT
  refine ⟨a, b, ?_⟩
  have he : T = scalarTraceLinear a b := matrix_linear_ext_hermitian T
    (scalarTraceLinear a b) (fun X hX => equivariant_on_hermitian T hT a b h X hX)
  intro X
  exact congrArg (fun L : Matrix N N ℂ →ₗ[ℂ] Matrix N N ℂ => L X) he

end Fluctuations
