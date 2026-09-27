import Fluctuations.HaarSU4

open scoped Matrix Kronecker

namespace Fluctuations

/-- A two-qubit matrix acts on its subsystem and as the identity on the
spectator system. This is a unital complex star-algebra homomorphism. -/
def qubitEmbedding (S : Type*) [Fintype S] [DecidableEq S] :
    Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix (Fin 4 × S) (Fin 4 × S) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix S S ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    simpa only [mul_one] using
      Matrix.mul_kronecker_mul A B (1 : Matrix S S ℂ) (1 : Matrix S S ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker, Matrix.one_kronecker_one]
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker A (1 : Matrix S S ℂ)).symm

@[simp] lemma qubitEmbedding_apply (S : Type*) [Fintype S] [DecidableEq S]
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    qubitEmbedding S A = A ⊗ₖ (1 : Matrix S S ℂ) := rfl

/-- The tensor insertion is injective when the spectator space has positive dimension. -/
lemma qubitEmbedding_injective (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S] :
    Function.Injective (qubitEmbedding S) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  intro A B h
  ext i j
  have hs := congrArg (fun T => T (i, s) (j, s)) h
  simpa [qubitEmbedding, Matrix.kroneckerMap_apply] using hs

/-- Any unital star-algebra insertion sends a genuine SU(4) gate to a unitary
operator on the global matrix space. -/
lemma starAlgHom_su4_mem_unitary {N : Type*} [Fintype N] [DecidableEq N]
    (E : Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ) (U : SU4) :
    E U.val ∈ Matrix.unitaryGroup N ℂ :=
  unitary.map_mem E U.prop.1

/-- A Haar SU(4) gate tensored with the spectator identity is a physical unitary. -/
lemma qubitEmbedding_su4_mem_unitary (S : Type*) [Fintype S] [DecidableEq S]
    (U : SU4) : qubitEmbedding S U.val ∈ Matrix.unitaryGroup (Fin 4 × S) ℂ :=
  starAlgHom_su4_mem_unitary (qubitEmbedding S) U

end Fluctuations
