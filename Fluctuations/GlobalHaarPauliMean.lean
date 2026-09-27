import Fluctuations.UnitaryEquivariantClassification

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
/-- Trace zero gives equal multiplicities of the two eigenvalues of an involution. -/
lemma sign_eigenspaces_card_eq (q : N → ℂ) (hq : ∀ i, q i = 1 ∨ q i = -1)
    (hsum : ∑ i, q i = 0) :
    Fintype.card {i // q i = 1} = Fintype.card {i // q i = -1} := by
  classical
  have hpoint (i : N) : q i =
      (if q i = 1 then (1 : ℂ) else 0) - (if q i = -1 then (1 : ℂ) else 0) := by
    rcases hq i with hi | hi <;> norm_num [hi]
  have heq : (∑ i, q i) =
      (Fintype.card {i // q i = 1} : ℂ) - (Fintype.card {i // q i = -1} : ℂ) := by
    calc
      (∑ i, q i) = ∑ i, ((if q i = 1 then (1 : ℂ) else 0) -
          (if q i = -1 then (1 : ℂ) else 0)) := Finset.sum_congr rfl fun i _ => hpoint i
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_boole, Fintype.card_subtype]
  rw [hsum] at heq
  exact_mod_cast (sub_eq_zero.mp heq.symm)

omit [DecidableEq N] in
/-- Equal sign multiplicities produce an actual permutation reversing every sign. -/
theorem exists_sign_reversing_permutation (q : N → ℂ)
    (hq : ∀ i, q i = 1 ∨ q i = -1) (hsum : ∑ i, q i = 0) :
    ∃ τ : Equiv.Perm N, ∀ i, q (τ i) = -q i := by
  classical
  let e : {i // q i = 1} ≃ {i // q i = -1} :=
    Fintype.equivOfCardEq (sign_eigenspaces_card_eq q hq hsum)
  have hneg (i : N) (hi : q i ≠ 1) : q i = -1 := (hq i).resolve_left hi
  let f (i : N) : N := if hi : q i = 1 then (e ⟨i, hi⟩).val else
    (e.symm ⟨i, hneg i hi⟩).val
  have hf : Function.Involutive f := by
    intro i
    by_cases hi : q i = 1
    · have hn : q (e ⟨i, hi⟩).val ≠ 1 := by
        rw [(e ⟨i, hi⟩).property]
        norm_num
      simp [f, hi, hn]
    · have hp : q (e.symm ⟨i, hneg i hi⟩).val = 1 := (e.symm ⟨i, hneg i hi⟩).property
      simp [f, hi, hp]
  refine ⟨Function.Involutive.toPerm f hf, ?_⟩
  intro i
  change q (f i) = -q i
  by_cases hi : q i = 1
  · simp only [f, dif_pos hi]
    rw [(e ⟨i, hi⟩).property, hi]
  · simp only [f, dif_neg hi]
    rw [(e.symm ⟨i, hneg i hi⟩).property, hneg i hi]
    ring

omit [Fintype N] in
lemma swap_preserves_equal_values (q : N → ℂ) (i j : N) (hij : q i = q j) :
    ∀ l, q (Equiv.swap i j l) = q l := by
  intro l
  by_cases hli : l = i
  · subst l
    simpa using hij.symm
  · by_cases hlj : l = j
    · subst l
      simpa using hij
    · simp [Equiv.swap_apply_def, hli, hlj]

/-- Every balanced diagonal involution satisfies the existing transitivity
criterion for all-order Haar OTOC state independence. -/
theorem signedPermutationTransitive_of_signs_trace_zero (q : N → ℂ)
    (hq : ∀ i, q i = 1 ∨ q i = -1) (hsum : ∑ i, q i = 0) :
    SignedPermutationTransitive q := by
  classical
  obtain ⟨τ, hτ⟩ := exists_sign_reversing_permutation q hq hsum
  intro i j
  by_cases hij : q i = q j
  · exact ⟨Equiv.swap i j, Equiv.swap_apply_left i j,
      Or.inl (swap_preserves_equal_values q i j hij)⟩
  · have hsign : q j = -q i := by
      rcases hq i with hi | hi <;> rcases hq j with hj | hj <;> simp_all
    have hsame : q (τ i) = q j := (hτ i).trans hsign.symm
    refine ⟨τ.trans (Equiv.swap (τ i) j), by simp, Or.inr ?_⟩
    intro l
    change q (Equiv.swap (τ i) j (τ l)) = -q l
    rw [swap_preserves_equal_values q (τ i) j hsame, hτ]

/-- Spectral coordinates of a Hermitian involution are exactly signs. -/
lemma hermitian_involution_eigenvalues_sign (M : Matrix N N ℂ) (hM : M.IsHermitian)
    (hM2 : M * M = 1) :
    ∀ i, (RCLike.ofReal (hM.eigenvalues i) : ℂ) = 1 ∨
      (RCLike.ofReal (hM.eigenvalues i) : ℂ) = -1 := by
  let U := hM.eigenvectorUnitary
  let q : N → ℂ := RCLike.ofReal ∘ hM.eigenvalues
  have hdiag : U.val.conjTranspose * M * U.val = Matrix.diagonal q :=
    hM.star_mul_self_mul_eq_diagonal
  have hsq : Matrix.diagonal q * Matrix.diagonal q = 1 := by
    rw [← hdiag]
    exact unitary_conjugate_involution U.val M U.prop hM2
  intro i
  have hh := congrArg (fun A : Matrix N N ℂ => A i i) hsq
  simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hh
  exact mul_self_eq_one_iff.mp hh

/-- Scalarity of the actual global Haar OTOC matrix mean for every Hermitian
traceless involution probe, every butterfly matrix, and every OTOC order. -/
theorem globalHaarOTOCMatrixMean_scalar_of_traceless_involution [Nonempty N]
    (B M : Matrix N N ℂ) (hM : M.IsHermitian) (hM2 : M * M = 1)
    (htr : Matrix.trace M = 0) (k : ℕ) :
    ∃ α : ℂ, globalHaarOTOCMatrixMean B M k = α • (1 : Matrix N N ℂ) := by
  let U := hM.eigenvectorUnitary
  let q : N → ℂ := RCLike.ofReal ∘ hM.eigenvalues
  have hs : U.val * Matrix.diagonal q * U.val.conjTranspose = M := hM.spectral_theorem.symm
  have hdiag : U.val.conjTranspose * M * U.val = Matrix.diagonal q :=
    hM.star_mul_self_mul_eq_diagonal
  have hsum : ∑ i, q i = 0 := by
    rw [← Matrix.trace_diagonal, ← hdiag]
    exact (globalHaarConjugate_trace M U).trans htr
  have hq : SignedPermutationTransitive q :=
    signedPermutationTransitive_of_signs_trace_zero q
      (hermitian_involution_eigenvalues_sign M hM hM2) hsum
  obtain ⟨α, hα⟩ := globalHaarOTOCMatrixMean_scalar_of_transitive B q hq k
  refine ⟨α, ?_⟩
  have hh := globalHaarOTOCMatrixMean_scalar_conjugateProbe B (Matrix.diagonal q) k (star U) hα
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, hs] using hh

/-- All trace-one input matrices have the same actual Haar OTOC mean under
the structural Pauli assumptions on the probe; positivity of the state is unnecessary. -/
theorem globalHaarOTOCMean_state_independent_of_traceless_involution [Nonempty N]
    (B M : Matrix N N ℂ) (hM : M.IsHermitian) (hM2 : M * M = 1)
    (htr : Matrix.trace M = 0) (k : ℕ) :
    ∃ α : ℂ, ∀ ρ : Matrix N N ℂ, Matrix.trace ρ = 1 →
      globalHaarOTOCMean ρ B M k = α := by
  obtain ⟨α, hα⟩ := globalHaarOTOCMatrixMean_scalar_of_traceless_involution B M hM hM2 htr k
  refine ⟨α, ?_⟩
  intro ρ hρ
  rw [globalHaarOTOCMean_eq_trace_matrixMean, hα]
  simp [hρ]

/-- The actual mean equals the normalized trace of its actual Haar matrix
mean for any Hermitian trace-zero involution, uniformly in the trace-one state. -/
theorem globalHaarOTOCMean_traceless_involution_eq_normalized_trace [Nonempty N]
    (ρ B M : Matrix N N ℂ) (hρ : Matrix.trace ρ = 1)
    (hM : M.IsHermitian) (hM2 : M * M = 1) (htr : Matrix.trace M = 0) (k : ℕ) :
    globalHaarOTOCMean ρ B M k = (Fintype.card N : ℂ)⁻¹ *
      Matrix.trace (globalHaarOTOCMatrixMean B M k) := by
  obtain ⟨α, hα⟩ := globalHaarOTOCMean_state_independent_of_traceless_involution B M hM hM2 htr k
  rw [hα ρ hρ, ← hα (globalMaximallyMixedState N) globalMaximallyMixedState_trace,
    globalHaarOTOCMean_eq_trace_matrixMean]
  simp [globalMaximallyMixedState]

end Fluctuations
