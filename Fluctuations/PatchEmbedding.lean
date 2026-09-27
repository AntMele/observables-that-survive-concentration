import Fluctuations.TensorSupport
import Fluctuations.QubitEmbedding
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Canonical physical insertion of a matrix on an arbitrary set of qubits. -/

open scoped BigOperators Matrix Kronecker

namespace Fluctuations

def tensorIdentityEmbedding (L R : Type*) [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] :
    Matrix L L ℂ →⋆ₐ[ℂ] Matrix (L × R) (L × R) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix R R ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    simpa only [mul_one] using
      Matrix.mul_kronecker_mul A B (1 : Matrix R R ℂ) (1 : Matrix R R ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker, Matrix.one_kronecker_one]
  map_star' A := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_one] using
      (Matrix.conjTranspose_kronecker A (1 : Matrix R R ℂ)).symm

def reindexStarAlgHom {L R : Type*} [Fintype L] [DecidableEq L]
    [Fintype R] [DecidableEq R] (e : L ≃ R) :
    Matrix L L ℂ →⋆ₐ[ℂ] Matrix R R ℂ where
  toAlgHom := (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom
  map_star' A := by
    exact (Matrix.conjTranspose_reindex e e A).symm

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Insert an arbitrary patch matrix and the spectator identity, then restore
the original ordering of the global qubit basis. -/
def patchEmbedding (S : Finset Site) :
    Matrix (↥S → Fin 2) (↥S → Fin 2) ℂ →⋆ₐ[ℂ] QubitOperator Site :=
  (reindexStarAlgHom
    (Equiv.piEquivPiSubtypeProd (fun s => s ∈ S) (fun _ => Fin 2)).symm).comp
    (tensorIdentityEmbedding (↥S → Fin 2) ({s // s ∉ S} → Fin 2))

@[simp] lemma patchEmbedding_apply (S : Finset Site)
    (A : Matrix (↥S → Fin 2) (↥S → Fin 2) ℂ) (x y : QubitState Site) :
    patchEmbedding S A x y =
      A (fun s => x s) (fun s => y s) *
        (if (fun s : {s // s ∉ S} => x s) = (fun s : {s // s ∉ S} => y s) then 1 else 0) := by
  simp [patchEmbedding, reindexStarAlgHom, tensorIdentityEmbedding,
    Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Equiv.piEquivPiSubtypeProd]

lemma patchEmbedding_single_one (S : Finset Site) (u v : ↥S → Fin 2) :
    patchEmbedding S (Matrix.single u v 1) =
      tensorMatrix (fun s =>
        if hs : s ∈ S then Matrix.single (u ⟨s, hs⟩) (v ⟨s, hs⟩) 1 else 1) := by
  classical
  ext x y
  rw [patchEmbedding_apply]
  simp only [tensorMatrix]
  let p (s : Site) : Prop :=
    if hs : s ∈ S then u ⟨s, hs⟩ = x s ∧ v ⟨s, hs⟩ = y s else x s = y s
  have hentry (s : Site) :
      (if hs : s ∈ S then Matrix.single (u ⟨s, hs⟩) (v ⟨s, hs⟩) (1 : ℂ)
        else 1) (x s) (y s) = if p s then 1 else 0 := by
    by_cases hs : s ∈ S <;> simp [p, hs, Matrix.single, Matrix.one_apply]
  simp_rw [hentry]
  have hp : (∀ s, p s) ↔
      (u = fun s : ↥S => x s) ∧ (v = fun s : ↥S => y s) ∧
        (fun s : {s // s ∉ S} => x s) = (fun s : {s // s ∉ S} => y s) := by
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · funext s
        exact ((by simpa [p, s.prop] using h s.val) :
          u s = x s ∧ v s = y s).1
      · funext s
        exact ((by simpa [p, s.prop] using h s.val) :
          u s = x s ∧ v s = y s).2
      · funext s
        simpa [p, s.prop] using h s.val
    · rintro ⟨hu, hv, ho⟩ s
      by_cases hs : s ∈ S
      · simp [p, hs, congrFun hu ⟨s, hs⟩, congrFun hv ⟨s, hs⟩]
      · simpa [p, hs] using congrFun ho ⟨s, hs⟩
  by_cases h : ∀ s, p s
  · obtain ⟨hu, hv, ho⟩ := hp.mp h
    simp [h, hu, hv, ho, Matrix.single]
  · have hz : (∏ s, if p s then (1 : ℂ) else 0) = 0 := by
      push_neg at h
      obtain ⟨s, hs⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])
    rw [hz]
    have hn := fun hc => h (hp.mpr hc)
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs <;> simp_all

/-- Canonical tensor insertion has the claimed concrete physical support. -/
theorem supported_patchEmbedding (S : Finset Site)
    (A : Matrix (↥S → Fin 2) (↥S → Fin 2) ℂ) :
    Supported S (patchEmbedding S A) := by
  classical
  induction A using Matrix.induction_on' with
  | h_zero => simpa using supported_zero S
  | h_add A B hA hB => simpa using hA.add hB
  | h_std_basis u v z =>
    have heq : Matrix.single u v z = z • Matrix.single u v (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [heq, map_smul, patchEmbedding_single_one]
    apply Supported.smul
    exact supported_tensorMatrix _ (fun s hs => by simp [hs])

theorem patchEmbedding_injective (S : Finset Site) :
    Function.Injective (patchEmbedding S) := by
  classical
  intro A B h
  ext u v
  let x : QubitState Site := fun s => if hs : s ∈ S then u ⟨s, hs⟩ else 0
  let y : QubitState Site := fun s => if hs : s ∈ S then v ⟨s, hs⟩ else 0
  have hx : (fun s : ↥S => x s) = u := by funext s; simp [x, s.prop]
  have hy : (fun s : ↥S => y s) = v := by funext s; simp [y, s.prop]
  have hxy : (fun s : {s // s ∉ S} => x s) =
      (fun s : {s // s ∉ S} => y s) := by funext s; simp [x, y, s.prop]
  have he := congrArg (fun Z : QubitOperator Site => Z x y) h
  simpa only [patchEmbedding_apply, hx, hy, hxy, if_true, mul_one] using he

/-- A two-site patch has precisely the four basis states of an SU(4) gate. -/
noncomputable def twoQubitPatchBasis (S : Finset Site) (hS : S.card = 2) :
    Fin 4 ≃ (↥S → Fin 2) :=
  (Fintype.equivFinOfCardEq (by simp [hS])).symm

/-- The physical two-qubit gate insertion on any pair of distinct sites. -/
noncomputable def twoQubitPatchEmbedding (S : Finset Site) (hS : S.card = 2) :
    Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] QubitOperator Site :=
  (patchEmbedding S).comp (reindexStarAlgHom (twoQubitPatchBasis S hS))

theorem supported_twoQubitPatchEmbedding (S : Finset Site) (hS : S.card = 2)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Supported S (twoQubitPatchEmbedding S hS A) :=
  supported_patchEmbedding S _

theorem twoQubitPatchEmbedding_mem_unitary (S : Finset Site) (hS : S.card = 2)
    (U : SU4) :
    twoQubitPatchEmbedding S hS U.val ∈ Matrix.unitaryGroup (QubitState Site) ℂ :=
  starAlgHom_su4_mem_unitary (twoQubitPatchEmbedding S hS) U

end Fluctuations
