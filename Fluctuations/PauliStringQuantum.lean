import Fluctuations.PauliString

open scoped BigOperators Matrix Kronecker

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

omit [Fintype Site] [DecidableEq Site] in
lemma matrix_sum_kronecker {I A B : Type*} [Fintype I]
    (X : I → Matrix A A ℂ) (Y : Matrix B B ℂ) :
    (∑ i, X i) ⊗ₖ Y = ∑ i, X i ⊗ₖ Y := by
  ext x y
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

lemma fintype_prod_pair_split {M : Type*} [CommMonoid M]
    (i j : Site) (hij : i ≠ j) (f : Site → M) :
    (∏ s, f s) = f i * f j * ∏ s : PairSpectator i j, f s := by
  classical
  have hr : (∏ s ∈ (Finset.univ.erase i).erase j, f s) =
      ∏ s : PairSpectator i j, f s :=
    Finset.prod_subtype _ (by intro s; simp [and_comm]) f
  calc
    _ = f i * ∏ s ∈ Finset.univ.erase i, f s :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    _ = f i * (f j * ∏ s ∈ (Finset.univ.erase i).erase j, f s) := by
      exact congrArg (f i * ·)
        (Finset.mul_prod_erase (Finset.univ.erase i) f (a := j) (by simp [hij.symm])).symm
    _ = _ := by rw [hr, mul_assoc]

/-- The global tensor splits canonically into its ordered two-site factor
and the unchanged spectator tensor. -/
theorem pauliStringMatrix_pair_split (i j : Site) (hij : i ≠ j) (P : PauliString Site) :
    pauliStringMatrix P = reindexStarAlgHom (pairSplitEquiv i j hij (Fin 2)).symm
      (twoQubitPauli (P i, P j) ⊗ₖ pauliStringMatrix (fun s : PairSpectator i j => P s)) := by
  ext x y
  simp only [pauliStringMatrix, tensorMatrix, reindexStarAlgHom, pairSplitEquiv, twoQubitPauli]
  exact fintype_prod_pair_split i j hij (fun s => pauliMatrix (P s) (x s) (y s))

/-- The physical insertion of an ordered two-qubit gate in the global system. -/
def pauliPairEmbedding (i j : Site) (hij : i ≠ j) :
    Matrix TwoQubitBasis TwoQubitBasis ℂ →⋆ₐ[ℂ] QubitOperator Site :=
  (reindexStarAlgHom (pairSplitEquiv i j hij (Fin 2)).symm).comp
    (tensorIdentityEmbedding TwoQubitBasis (PairSpectator i j → Fin 2))

lemma pauliPairEmbedding_unitary (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary) :
    pauliPairEmbedding i j hij U.val ∈ Matrix.unitaryGroup (QubitState Site) ℂ :=
  unitary.map_mem (pauliPairEmbedding i j hij) U.prop

lemma pauliStringMatrix_pair_update_split (i j : Site) (hij : i ≠ j)
    (P : PauliString Site) (q : TwoQubitPauliLabel) :
    pauliStringMatrix (pauliPairUpdate i j P q) =
      reindexStarAlgHom (pairSplitEquiv i j hij (Fin 2)).symm
        (twoQubitPauli q ⊗ₖ pauliStringMatrix (fun s : PairSpectator i j => P s)) := by
  rw [pauliStringMatrix_pair_split i j hij, pauliPairUpdate_left i j hij,
    pauliPairUpdate_right, Prod.mk.eta]
  congr 3
  funext s
  exact pauliPairUpdate_other i j s s.prop.1 s.prop.2 P q

/-- The actual embedded gate action on a global Pauli is precisely its local
Pauli expansion, with the other sites held fixed. -/
theorem pauliPairEmbedding_conjugate_pauli (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (P : PauliString Site) :
    (pauliPairEmbedding i j hij U.val).conjTranspose * pauliStringMatrix P *
        pauliPairEmbedding i j hij U.val =
      ∑ q : TwoQubitPauliLabel, twoQubitPauliCoefficient (P i, P j) q U •
        pauliStringMatrix (pauliPairUpdate i j P q) := by
  let E := reindexStarAlgHom (pairSplitEquiv i j hij (Fin 2)).symm
  let S := pauliStringMatrix (fun s : PairSpectator i j => P s)
  have hs : pauliStringMatrix P = E (twoQubitPauli (P i, P j) ⊗ₖ S) :=
    pauliStringMatrix_pair_split i j hij P
  have hg : pauliPairEmbedding i j hij U.val = E (U.val ⊗ₖ 1) := rfl
  rw [hs, hg]
  change star (E (U.val ⊗ₖ 1)) * E (twoQubitPauli (P i, P j) ⊗ₖ S) * E (U.val ⊗ₖ 1) = _
  rw [← map_star, ← map_mul, ← map_mul]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have he := twoQubitPauli_expansion (globalHaarConjugate (twoQubitPauli (P i, P j)) U)
  change globalHaarConjugate (twoQubitPauli (P i, P j)) U = _ at he
  change E (globalHaarConjugate (twoQubitPauli (P i, P j)) U ⊗ₖ S) = _
  rw [he, matrix_sum_kronecker, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Matrix.smul_kronecker, map_smul, ← pauliStringMatrix_pair_update_split i j hij]
  congr 1
  change Matrix.trace (twoQubitPauli q * globalHaarConjugate (twoQubitPauli (P i, P j)) U) / 4 =
    (Fintype.card TwoQubitBasis : ℂ)⁻¹ * _
  norm_num
  ring

theorem pauliPairTransfer_sum_smul {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (P : PauliString Site) (f : PauliString Site → V) :
    (∑ Q, (pauliPairTransfer i j U Q P : ℂ) • f Q) =
      ∑ q : TwoQubitPauliLabel, (twoQubitPauliTransfer U q (P i, P j) : ℂ) •
        f (pauliPairUpdate i j P q) := by
  classical
  rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  have heq (x : PairSpectator i j → Fin 4) :
      (∀ s, s ≠ i → s ≠ j →
        (pairSplitEquiv i j hij (Fin 4)).symm (q, x) s = P s) ↔
          x = fun s : PairSpectator i j => P s := by
    constructor
    · intro h
      funext s
      simpa [pairSplitEquiv, s.prop.1, s.prop.2] using h s s.prop.1 s.prop.2
    · rintro rfl s hsi hsj
      simp [pairSplitEquiv, hsi, hsj]
  simp only [pauliPairTransfer, heq, apply_ite Complex.ofReal, Complex.ofReal_zero,
    ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, pairSplitEquiv_symm_pauli,
    pauliPairUpdate_left i j hij, pauliPairUpdate_right, Prod.mk.eta]

/-- Exact global transfer-matrix action of the actual embedded unitary. -/
theorem pauliPairEmbedding_conjugate_pauli_transfer (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (P : PauliString Site) :
    (pauliPairEmbedding i j hij U.val).conjTranspose * pauliStringMatrix P *
        pauliPairEmbedding i j hij U.val =
      ∑ Q : PauliString Site, (pauliPairTransfer i j U Q P : ℂ) • pauliStringMatrix Q := by
  rw [pauliPairTransfer_sum_smul i j hij, pauliPairEmbedding_conjugate_pauli]
  simp_rw [twoQubitPauliTransfer_cast]

theorem pauliPairEmbedding_conjugate_expansion (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (v : PauliString Site → ℝ) :
    (pauliPairEmbedding i j hij U.val).conjTranspose *
        (∑ P, (v P : ℂ) • pauliStringMatrix P) * pauliPairEmbedding i j hij U.val =
      ∑ Q : PauliString Site, ((Matrix.mulVec (pauliPairTransfer i j U) v Q : ℝ) : ℂ) •
        pauliStringMatrix Q := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [pauliPairEmbedding_conjugate_pauli_transfer i j hij, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro P _
  ring

theorem pauliPairTransfer_continuous (i j : Site) : Continuous (pauliPairTransfer i j) := by
  classical
  apply continuous_pi
  intro Q
  apply continuous_pi
  intro P
  unfold pauliPairTransfer
  split_ifs
  · exact Complex.continuous_re.comp (twoQubitPauliCoefficient (P i, P j) (Q i, Q j)).continuous
  · exact continuous_const

/-- Actual one-gate Haar averaging preserves diagonal global Pauli covariance
and evolves its diagonal by the stated local classical kernel. -/
theorem pauliPairTransfer_haar_column_covariance (i j : Site)
    (P Q R : PauliString Site) :
    (∫ U, pauliPairTransfer i j U Q P * pauliPairTransfer i j U R P
      ∂globalHaar TwoQubitBasis) = if Q = R then pauliPairKernel i j Q P else 0 := by
  classical
  by_cases hQ : ∀ s, s ≠ i → s ≠ j → Q s = P s
  · by_cases hR : ∀ s, s ≠ i → s ≠ j → R s = P s
    · have heq : (Q i, Q j) = (R i, R j) ↔ Q = R := by
        constructor
        · intro h
          funext s
          by_cases hs : s = i
          · subst s
            exact congrArg Prod.fst h
          by_cases ht : s = j
          · subst s
            exact congrArg Prod.snd h
          exact (hQ s hs ht).trans (hR s hs ht).symm
        · rintro rfl
          rfl
      simp only [pauliPairTransfer, if_pos hQ, if_pos hR]
      rw [twoQubitPauliTransfer_haar_covariance]
      unfold pauliPairKernel
      rw [if_pos hQ]
      simp only [true_and, heq]
    · have hne : Q ≠ R := by intro h; exact hR (h ▸ hQ)
      simp [pauliPairTransfer, hR, hne]
  · by_cases hQR : Q = R
    · subst R
      simp [pauliPairTransfer, pauliPairKernel, hQ]
    · simp [pauliPairTransfer, hQ, hQR]

end Fluctuations
