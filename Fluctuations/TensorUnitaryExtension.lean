import Fluctuations.HaarTensorInvariants

open scoped BigOperators

namespace Fluctuations

/-- A rational parametrization of the complex unit circle. -/
noncomputable def unitPhaseParam (t : ℝ) : ℂ :=
  (1 + (t : ℂ) * Complex.I) / (1 - (t : ℂ) * Complex.I)

lemma unitPhaseParam_den_ne_zero (t : ℝ) : (1 : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh

lemma unitPhaseParam_norm (t : ℝ) : ‖unitPhaseParam t‖ = 1 := by
  have hc : (1 : ℂ) + (t : ℂ) * Complex.I = star ((1 : ℂ) - (t : ℂ) * Complex.I) := by
    simp
  rw [unitPhaseParam, norm_div, hc, norm_star]
  exact div_self (norm_ne_zero_iff.mpr (unitPhaseParam_den_ne_zero t))

lemma unitPhaseParam_injective : Function.Injective unitPhaseParam := by
  intro s t h
  have hh := (div_eq_div_iff (unitPhaseParam_den_ne_zero s)
    (unitPhaseParam_den_ne_zero t)).mp h
  have hi := congrArg Complex.im hh
  simp at hi
  linarith

lemma infinite_unitComplex : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  apply (Set.infinite_range_of_injective unitPhaseParam_injective).mono
  rintro z ⟨t, rfl⟩
  exact unitPhaseParam_norm t

section MatrixPolynomials

variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable def matrixPolynomialEval (p : MvPolynomial (N × N) ℂ)
    (A : Matrix N N ℂ) : ℂ := MvPolynomial.eval (fun ij => A ij.1 ij.2) p

lemma diagonal_mem_unitary_of_norm_one (d : N → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup N ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (Matrix.diagonal d) = Matrix.diagonal (fun i => star (d i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.star_apply]
    · simp [Matrix.star_apply, Matrix.diagonal, hij, Ne.symm hij]
  rw [hstar, Matrix.diagonal_mul_diagonal]
  have heq : (fun i => d i * star (d i)) = (fun _ : N => (1 : ℂ)) := by
    funext i
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hd i]
  rw [heq, Matrix.diagonal_one]

/-- A polynomial vanishing on all unitary matrices vanishes on every Hermitian matrix. -/
theorem matrixPolynomialEval_zero_of_isHermitian
    (p : MvPolynomial (N × N) ℂ)
    (hp : ∀ U : Matrix.unitaryGroup N ℂ, matrixPolynomialEval p U.val = 0)
    (A : Matrix N N ℂ) (hA : A.IsHermitian) : matrixPolynomialEval p A = 0 := by
  let U := hA.eigenvectorUnitary
  let entryPoly (ij : N × N) : MvPolynomial N ℂ :=
    ∑ t, MvPolynomial.C (U.val ij.1 t * (star U.val) t ij.2) * MvPolynomial.X t
  let q := MvPolynomial.eval₂ MvPolynomial.C entryPoly p
  have hentry (d : N → ℂ) (ij : N × N) :
      MvPolynomial.eval d (entryPoly ij) =
        (U.val * Matrix.diagonal d * star U.val) ij.1 ij.2 := by
    simp only [entryPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have heval (d : N → ℂ) :
      MvPolynomial.eval d q = matrixPolynomialEval p
        (U.val * Matrix.diagonal d * star U.val) := by
    dsimp only [q]
    rw [MvPolynomial.eval_eval₂]
    have hc : (MvPolynomial.eval d).comp MvPolynomial.C = RingHom.id ℂ := by
      ext c
      simp
    rw [hc, MvPolynomial.eval₂_id]
    apply congrArg (fun v : N × N → ℂ => MvPolynomial.eval v p)
    funext ij
    exact hentry d ij
  have hq : q = 0 := by
    apply MvPolynomial.funext_set (fun _ : N => {z : ℂ | ‖z‖ = 1})
      (fun _ => infinite_unitComplex)
    intro d hd
    rw [heval, map_zero]
    let V : Matrix.unitaryGroup N ℂ :=
      ⟨Matrix.diagonal d, diagonal_mem_unitary_of_norm_one d (fun i => hd i (Set.mem_univ i))⟩
    exact hp (U * V * star U)
  have hh := congrArg (MvPolynomial.eval (RCLike.ofReal ∘ hA.eigenvalues)) hq
  rw [heval, map_zero] at hh
  change matrixPolynomialEval p (hA.eigenvectorUnitary.val *
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star hA.eigenvectorUnitary.val) = 0 at hh
  rwa [← hA.spectral_theorem] at hh

/-- Complex polynomials in matrix entries are determined by their values on
the unitary group. The proof first extends diagonal phases, then uses the
Hermitian spectral theorem and a real-to-complex polynomial pencil. -/
theorem matrixPolynomialEval_zero_of_unitary
    (p : MvPolynomial (N × N) ℂ)
    (hp : ∀ U : Matrix.unitaryGroup N ℂ, matrixPolynomialEval p U.val = 0)
    (A : Matrix N N ℂ) : matrixPolynomialEval p A = 0 := by
  let X : Matrix N N ℂ := realPart A
  let Y : Matrix N N ℂ := imaginaryPart A
  have hX : X.IsHermitian := (realPart A).property
  have hY : Y.IsHermitian := (imaginaryPart A).property
  let entryPoly (ij : N × N) : Polynomial ℂ :=
    Polynomial.C (X ij.1 ij.2) + Polynomial.X * Polynomial.C (Y ij.1 ij.2)
  let q := MvPolynomial.eval₂ Polynomial.C entryPoly p
  have heval (z : ℂ) : q.eval z = matrixPolynomialEval p (X + z • Y) := by
    dsimp only [q]
    rw [MvPolynomial.polynomial_eval_eval₂]
    have hc : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id ℂ := by
      ext c
      simp
    rw [hc, MvPolynomial.eval₂_id]
    apply congrArg (fun v : N × N → ℂ => MvPolynomial.eval v p)
    funext ij
    simp only [entryPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hq : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro z ⟨t, rfl⟩
    change q.eval (t : ℂ) = 0
    rw [heval]
    apply matrixPolynomialEval_zero_of_isHermitian p hp
    apply hX.add
    exact (show IsSelfAdjoint (t : ℂ) by simp [isSelfAdjoint_iff]).smul hY
  have hh := congrArg (Polynomial.eval Complex.I) hq
  rw [heval, Polynomial.eval_zero] at hh
  simpa only [X, Y, realPart_add_I_smul_imaginaryPart] using hh

/-- Commuting with the tensor powers of every genuine unitary matrix already
implies commuting with the tensor powers of all complex matrices. -/
theorem tensorPower_commute_all_of_unitary (r : ℕ)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup N ℂ, Commute T (tensorPowerMatrix r U.val)) :
    ∀ A : Matrix N N ℂ, Commute T (tensorPowerMatrix r A) := by
  classical
  intro A
  change T * tensorPowerMatrix r A = tensorPowerMatrix r A * T
  ext x y
  let p : MvPolynomial (N × N) ℂ :=
    (∑ z : Fin r → N, MvPolynomial.C (T x z) *
      ∏ t, MvPolynomial.X (z t, y t)) -
    (∑ z : Fin r → N, (∏ t, MvPolynomial.X (x t, z t)) * MvPolynomial.C (T z y))
  have heval (B : Matrix N N ℂ) : matrixPolynomialEval p B =
      (T * tensorPowerMatrix r B) x y - (tensorPowerMatrix r B * T) x y := by
    simp [matrixPolynomialEval, p, tensorPowerMatrix, Matrix.mul_apply]
  have hp : ∀ U : Matrix.unitaryGroup N ℂ, matrixPolynomialEval p U.val = 0 := by
    intro U
    rw [heval, (hT U).eq, sub_self]
  have hh := matrixPolynomialEval_zero_of_unitary p hp A
  rw [heval] at hh
  exact sub_eq_zero.mp hh

/-- The unitary tensor-power commutant is explicitly spanned by position
permutations, with no algebraic-extension or invariant-spanning assumption. -/
theorem tensorPower_unitary_commutant_eq_permutation_sum {r : ℕ}
    (e : Fin r → N) (he : Function.Injective e)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup N ℂ, Commute T (tensorPowerMatrix r U.val)) :
    T = ∑ σ : Equiv.Perm (Fin r), T (e ∘ σ) e • tensorPositionPermutation N σ :=
  tensorPower_commutant_eq_permutation_sum e he T (tensorPower_commute_all_of_unitary r T hT)

theorem tensorPower_unitary_commutant_mem_span {r : ℕ} (hcard : r ≤ Fintype.card N)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup N ℂ, Commute T (tensorPowerMatrix r U.val)) :
    T ∈ Submodule.span ℂ (Set.range (tensorPositionPermutation N (r := r))) :=
  tensorPower_commutant_mem_span hcard T (tensorPower_commute_all_of_unitary r T hT)

end MatrixPolynomials

end Fluctuations
