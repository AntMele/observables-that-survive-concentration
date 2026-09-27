import Fluctuations.QubitEmbedding
import Fluctuations.HaarLocalVariance

open scoped Matrix Kronecker

namespace Fluctuations

/-- Cross-commutation permits collecting inactive factors on the left while
preserving the original order within each sublist. Active factors need not
commute with each other, nor do inactive factors. -/
theorem ordered_product_inactive_mul_active {A ι : Type*} [Monoid A]
    (l : List ι) (active : ι → Prop) [DecidablePred active] (g : ι → A)
    (hcross : ∀ i ∈ l, active i → ∀ j ∈ l, ¬active j → Commute (g i) (g j)) :
    (l.map g).prod = ((l.filter fun i => ¬active i).map g).prod *
      ((l.filter active).map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have htail : ∀ i ∈ l, active i → ∀ j ∈ l, ¬active j → Commute (g i) (g j) := by
        intro i hi hia j hj hja
        exact hcross i (by simp [hi]) hia j (by simp [hj]) hja
      rw [List.map_cons, List.prod_cons, ih htail]
      by_cases ha : active a
      · have hc : Commute (g a) (((l.filter fun i => ¬active i).map g).prod) := by
          apply Commute.list_prod_right
          intro z hz
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
          have hm := List.mem_filter.mp hj
          exact hcross a (by simp) ha j (by simp [hm.1]) (by simpa using hm.2)
        simp only [List.filter_cons, ha, not_true_eq_false, decide_false,
          Bool.false_eq_true, decide_true]
        exact hc.left_comm _
      · simp [ha, mul_assoc]

section Matrices

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A unitary that commutes with an observable disappears from its conjugation. -/
lemma unitary_conjugation_eq_self_of_commute (U B : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) (hcomm : Commute U B) :
    U.conjTranspose * B * U = B := by
  change star U * B * U = B
  calc
    star U * B * U = star U * (B * U) := mul_assoc _ _ _
    _ = star U * (U * B) := congrArg (star U * ·) hcomm.eq.symm
    _ = B := by rw [← mul_assoc, hU.1, one_mul]

/-- Every product of embedded genuine SU(4) gates is a global unitary. -/
lemma haarBlockMatrix_mem_unitary {m : ℕ}
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (x : SU4Block m) :
    haarBlockMatrix (fun i => (E i).toAlgHom.toLinearMap) x ∈
      Matrix.unitaryGroup N ℂ := by
  unfold haarBlockMatrix
  apply Submonoid.list_prod_mem
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact starAlgHom_su4_mem_unitary (E i) (x i)

/-- Any number of inactive gates cancels, provided their embedded action
commutes with the measured observable. No bound on that number is assumed. -/
lemma haarBlockMatrix_inactive_conjugation {q : ℕ}
    (I : Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (B : Matrix N N ℂ)
    (hcomm : ∀ i (U : SU4), Commute (I i U.val) B) (y : SU4Block q) :
    (haarBlockMatrix (fun i => (I i).toAlgHom.toLinearMap) y).conjTranspose * B *
      haarBlockMatrix (fun i => (I i).toAlgHom.toLinearMap) y = B := by
  apply unitary_conjugation_eq_self_of_commute
  · exact haarBlockMatrix_mem_unitary I y
  · unfold haarBlockMatrix
    apply Commute.list_prod_left
    intro A hA
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact hcomm i (y i)

/-- An arbitrarily interleaved parallel layer acts on `B` exactly through its
active sublist. Only the inactive gates must be unitary; cross-commutation
justifies moving them before the active subproduct. -/
theorem matrix_conjugate_layer_eq_active {ι : Type*}
    (l : List ι) (active : ι → Prop) [DecidablePred active]
    (g : ι → Matrix N N ℂ) (B : Matrix N N ℂ)
    (hcross : ∀ i ∈ l, active i → ∀ j ∈ l, ¬active j → Commute (g i) (g j))
    (hunitary : ∀ i ∈ l, ¬active i → g i ∈ Matrix.unitaryGroup N ℂ)
    (hinactive : ∀ i ∈ l, ¬active i → Commute (g i) B) :
    (l.map g).prod.conjTranspose * B * (l.map g).prod =
      ((l.filter active).map g).prod.conjTranspose * B *
        ((l.filter active).map g).prod := by
  let J := ((l.filter fun i => ¬active i).map g).prod
  let A := ((l.filter active).map g).prod
  have hJ : J ∈ Matrix.unitaryGroup N ℂ := by
    apply Submonoid.list_prod_mem
    intro U hU
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hU
    have hm := List.mem_filter.mp hi
    exact hunitary i hm.1 (by simpa using hm.2)
  have hJB : Commute J B := by
    apply Commute.list_prod_left
    intro U hU
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hU
    have hm := List.mem_filter.mp hi
    exact hinactive i hm.1 (by simpa using hm.2)
  have hcancel := unitary_conjugation_eq_self_of_commute J B hJ hJB
  have hsplit : (l.map g).prod = J * A :=
    ordered_product_inactive_mul_active l active g hcross
  rw [hsplit, Matrix.conjTranspose_mul]
  change A.conjTranspose * J.conjTranspose * B * (J * A) = A.conjTranspose * B * A
  calc
    A.conjTranspose * J.conjTranspose * B * (J * A) =
      A.conjTranspose * (J.conjTranspose * B * J) * A := by simp only [mul_assoc]
    _ = A.conjTranspose * B * A := by rw [hcancel]

/-- The interleaved cancellation theorem specialized to actual SU(4) gates
placed by unital star-algebra embeddings. Spatial disjointness can certify the
cross-commutation hypotheses without imposing any bound on inactive gates. -/
theorem embedded_su4_layer_eq_active {ι : Type*}
    (l : List ι) (active : ι → Prop) [DecidablePred active]
    (E : ι → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (x : ι → SU4) (B : Matrix N N ℂ)
    (hcross : ∀ i ∈ l, active i → ∀ j ∈ l, ¬active j →
      ∀ U V : SU4, Commute (E i U.val) (E j V.val))
    (hinactive : ∀ i ∈ l, ¬active i → ∀ U : SU4, Commute (E i U.val) B) :
    (l.map (fun i => E i (x i).val)).prod.conjTranspose * B *
        (l.map (fun i => E i (x i).val)).prod =
      ((l.filter active).map (fun i => E i (x i).val)).prod.conjTranspose * B *
        ((l.filter active).map (fun i => E i (x i).val)).prod := by
  apply matrix_conjugate_layer_eq_active
  · intro i hi hia j hj hja
    exact hcross i hi hia j hj hja (x i) (x j)
  · intro i _ _
    exact starAlgHom_su4_mem_unitary (E i) (x i)
  · intro i hi hia
    exact hinactive i hi hia (x i)

end Matrices

/-- Concrete disjoint-support witness: operators on separate tensor factors
commute, in every finite pair of factor dimensions. -/
lemma disjoint_tensor_factors_commute {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (A : Matrix L L ℂ) (B : Matrix R R ℂ) :
    Commute (A ⊗ₖ (1 : Matrix R R ℂ)) ((1 : Matrix L L ℂ) ⊗ₖ B) := by
  change (A ⊗ₖ (1 : Matrix R R ℂ)) * ((1 : Matrix L L ℂ) ⊗ₖ B) =
    ((1 : Matrix L L ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix R R ℂ))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- A two-qubit gate is inactive for every observable carried entirely by its
spectator tensor factor. This discharges the commutation premise concretely. -/
lemma qubitEmbedding_commutes_spectator (S : Type*) [Fintype S] [DecidableEq S]
    (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix S S ℂ) :
    Commute (qubitEmbedding S A) ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ B) :=
  disjoint_tensor_factors_commute A B

end Fluctuations
