import Fluctuations.SpatialSupport
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Concrete support of finite-qubit operators, defined by their tensor entries. -/

open scoped BigOperators Matrix

namespace Fluctuations

abbrev QubitState (Site : Type*) := Site → Fin 2
abbrev QubitOperator (Site : Type*) := Matrix (QubitState Site) (QubitState Site) ℂ

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The actual tensor matrix: every entry is a product of single-site entries. -/
def tensorMatrix (Q : Site → Matrix (Fin 2) (Fin 2) ℂ) : QubitOperator Site :=
  fun x y => ∏ s, Q s (x s) (y s)

lemma tensorMatrix_mul (Q R : Site → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix Q * tensorMatrix R = tensorMatrix (fun s => Q s * R s) := by
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun s z => Q s (x s) z * R s z (y s))).symm

omit [DecidableEq Site] in
lemma tensorMatrix_star (Q : Site → Matrix (Fin 2) (Fin 2) ℂ) :
    star (tensorMatrix Q) = tensorMatrix (fun s => star (Q s)) := by
  ext x y
  simp [tensorMatrix]

lemma tensorMatrix_commute (Q R : Site → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ s, Commute (Q s) (R s)) :
    Commute (tensorMatrix Q) (tensorMatrix R) := by
  change tensorMatrix Q * tensorMatrix R = tensorMatrix R * tensorMatrix Q
  rw [tensorMatrix_mul, tensorMatrix_mul]
  congr 1
  funext s
  exact (h s).eq

/-- Tensors that are the identity at every site outside `S`. -/
def supportGenerators (S : Finset Site) : Set (QubitOperator Site) :=
  {A | ∃ Q : Site → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ s, s ∉ S → Q s = 1) ∧ A = tensorMatrix Q}

/-- Concrete operator support: finite algebraic combinations of tensors whose
entries are identity entries outside `S`. No commutation is assumed here. -/
def Supported (S : Finset Site) (A : QubitOperator Site) : Prop :=
  A ∈ Algebra.adjoin ℂ (supportGenerators S)

lemma supported_tensorMatrix {S : Finset Site}
    (Q : Site → Matrix (Fin 2) (Fin 2) ℂ) (hQ : ∀ s, s ∉ S → Q s = 1) :
    Supported S (tensorMatrix Q) :=
  Algebra.subset_adjoin ⟨Q, hQ, rfl⟩

lemma Supported.mono {S T : Finset Site} {A : QubitOperator Site}
    (hA : Supported S A) (hST : S ⊆ T) : Supported T A := by
  apply Algebra.adjoin_mono (s := supportGenerators S) (t := supportGenerators T) _ hA
  rintro A ⟨Q, hQ, rfl⟩
  exact ⟨Q, fun s hs => hQ s (fun h => hs (hST h)), rfl⟩

lemma supported_one (S : Finset Site) : Supported S (1 : QubitOperator Site) :=
  (Algebra.adjoin ℂ (supportGenerators S)).one_mem

lemma supported_zero (S : Finset Site) : Supported S (0 : QubitOperator Site) :=
  (Algebra.adjoin ℂ (supportGenerators S)).zero_mem

lemma Supported.add {S : Finset Site} {A B : QubitOperator Site}
    (hA : Supported S A) (hB : Supported S B) : Supported S (A + B) :=
  (Algebra.adjoin ℂ (supportGenerators S)).add_mem hA hB

lemma Supported.mul {S : Finset Site} {A B : QubitOperator Site}
    (hA : Supported S A) (hB : Supported S B) : Supported S (A * B) :=
  (Algebra.adjoin ℂ (supportGenerators S)).mul_mem hA hB

lemma Supported.smul {S : Finset Site} {A : QubitOperator Site}
    (hA : Supported S A) (z : ℂ) : Supported S (z • A) :=
  (Algebra.adjoin ℂ (supportGenerators S)).smul_mem hA z

lemma Supported.star {S : Finset Site} {A : QubitOperator Site}
    (hA : Supported S A) : Supported S (star A) := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
      obtain ⟨Q, hQ, rfl⟩ := hA
      rw [tensorMatrix_star]
      exact supported_tensorMatrix _ (fun s hs => by simp [hQ s hs])
  | algebraMap z =>
      rw [← algebraMap_star_comm]
      exact (Algebra.adjoin ℂ (supportGenerators S)).algebraMap_mem _
  | add A B _ _ hA hB => simpa only [star_add] using hA.add hB
  | mul A B _ _ hA hB => simpa only [star_mul] using hB.mul hA

lemma Supported.conjTranspose {S : Finset Site} {A : QubitOperator Site}
    (hA : Supported S A) : Supported S A.conjTranspose := hA.star

/-- Disjoint physical site supports imply matrix commutation. -/
theorem Supported.commute {S T : Finset Site} {A B : QubitOperator Site}
    (hA : Supported S A) (hB : Supported T B) (hST : Disjoint S T) :
    Commute A B := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hB
  rintro B ⟨R, hR, rfl⟩
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hA
  rintro A ⟨Q, hQ, rfl⟩
  apply tensorMatrix_commute
  intro s
  by_cases hs : s ∈ S
  · have ht : s ∉ T := fun ht => Finset.disjoint_left.mp hST hs ht
    simp [hR s ht]
  · simp [hQ s hs]

lemma Supported.conjugate {S T : Finset Site} {U B : QubitOperator Site}
    (hU : Supported S U) (hB : Supported T B) :
    Supported (S ∪ T) (U.conjTranspose * B * U) := by
  exact ((hU.mono Finset.subset_union_left).conjTranspose.mul
    (hB.mono Finset.subset_union_right)).mul (hU.mono Finset.subset_union_left)

/-- Arbitrary patch matrices are placed using their matrix-unit expansion.
Each summand acts identically at every spectator site. -/
noncomputable def patchMatrix (S : Finset Site)
    (A : Matrix (↥S → Fin 2) (↥S → Fin 2) ℂ) : QubitOperator Site :=
  ∑ x, ∑ y, A x y • tensorMatrix (fun s =>
    if hs : s ∈ S then Matrix.single (x ⟨s, hs⟩) (y ⟨s, hs⟩) 1 else 1)

lemma supported_patchMatrix (S : Finset Site)
    (A : Matrix (↥S → Fin 2) (↥S → Fin 2) ℂ) : Supported S (patchMatrix S A) := by
  unfold patchMatrix
  apply Subalgebra.sum_mem
  intro x _
  apply Subalgebra.sum_mem
  intro y _
  apply Supported.smul
  apply supported_tensorMatrix
  intro s hs
  simp [hs]

end Fluctuations
