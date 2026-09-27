import Mathlib

open scoped BigOperators

namespace Fluctuations

variable {X ι : Type*} [TopologicalSpace X]

/-- Products of exactly `r` continuous local features. -/
noncomputable def featureMonomial (φ : ι → C(X, ℂ)) (r : ℕ)
    (word : Fin r → ι) : C(X, ℂ) :=
  ∏ t, φ (word t)

/-- A finite feature space depending only on local data and the order. -/
noncomputable def polynomialFeatureSpace (φ : ι → C(X, ℂ)) (r : ℕ) :
    Submodule ℂ C(X, ℂ) :=
  Submodule.span ℂ (Set.range (featureMonomial φ r))

instance polynomialFeatureSpace_finiteDimensional [Finite ι]
    (φ : ι → C(X, ℂ)) (r : ℕ) :
    FiniteDimensional ℂ (polynomialFeatureSpace φ r) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem polynomialFeatureSpace_finrank_le [Fintype ι]
    (φ : ι → C(X, ℂ)) (r : ℕ) :
    Module.finrank ℂ (polynomialFeatureSpace φ r) ≤ Fintype.card ι ^ r := by
  simpa [polynomialFeatureSpace, Fintype.card_fun] using
    (finrank_range_le_card (R := ℂ) (featureMonomial φ r))

lemma featureMonomial_mem (φ : ι → C(X, ℂ)) (r : ℕ) (word : Fin r → ι) :
    featureMonomial φ r word ∈ polynomialFeatureSpace φ r :=
  Submodule.subset_span ⟨word, rfl⟩

lemma one_mem_polynomialFeatureSpace_zero (φ : ι → C(X, ℂ)) :
    (1 : C(X, ℂ)) ∈ polynomialFeatureSpace φ 0 := by
  simpa [featureMonomial] using
    featureMonomial_mem φ 0 (fun i => Fin.elim0 i)

lemma feature_mul_mem_polynomialFeatureSpace (φ : ι → C(X, ℂ)) (a : ι)
    (r : ℕ) {f : C(X, ℂ)} (hf : f ∈ polynomialFeatureSpace φ r) :
    φ a * f ∈ polynomialFeatureSpace φ (r + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨word, rfl⟩ := hf
      simpa [featureMonomial, Fin.prod_univ_succ] using
        featureMonomial_mem φ (r + 1) (Fin.cons a word)
  | zero => simp
  | add f g _ _ hf hg =>
      simpa [mul_add] using (polynomialFeatureSpace φ (r + 1)).add_mem hf hg
  | smul c f _ hf =>
      simpa [mul_smul_comm] using (polynomialFeatureSpace φ (r + 1)).smul_mem c hf

lemma linearFeature_mul_mem_polynomialFeatureSpace (φ : ι → C(X, ℂ))
    (r : ℕ) {f g : C(X, ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range φ))
    (hg : g ∈ polynomialFeatureSpace φ r) :
    f * g ∈ polynomialFeatureSpace φ (r + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      exact feature_mul_mem_polynomialFeatureSpace φ a r hg
  | zero => simp
  | add f h _ _ hf hh =>
      simpa [add_mul] using (polynomialFeatureSpace φ (r + 1)).add_mem hf hh
  | smul c f _ hf =>
      simpa [smul_mul_assoc] using (polynomialFeatureSpace φ (r + 1)).smul_mem c hf

lemma featureMonomial_mul_mem_polynomialFeatureSpace (φ : ι → C(X, ℂ))
    (d r : ℕ) (word : Fin d → ι) {g : C(X, ℂ)}
    (hg : g ∈ polynomialFeatureSpace φ r) :
    featureMonomial φ d word * g ∈ polynomialFeatureSpace φ (d + r) := by
  induction d with
  | zero => simpa [featureMonomial] using hg
  | succ d ih =>
      have h := feature_mul_mem_polynomialFeatureSpace φ (word 0) (d + r)
        (ih (fun t => word t.succ))
      simpa [featureMonomial, Fin.prod_univ_succ, mul_assoc, Nat.succ_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma mul_mem_polynomialFeatureSpace (φ : ι → C(X, ℂ)) (d r : ℕ)
    {f g : C(X, ℂ)} (hf : f ∈ polynomialFeatureSpace φ d)
    (hg : g ∈ polynomialFeatureSpace φ r) :
    f * g ∈ polynomialFeatureSpace φ (d + r) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨word, rfl⟩ := hf
      exact featureMonomial_mul_mem_polynomialFeatureSpace φ d r word hg
  | zero => simp
  | add f h _ _ hf hh =>
      simpa [add_mul] using (polynomialFeatureSpace φ (d + r)).add_mem hf hh
  | smul c f _ hf =>
      simpa [smul_mul_assoc] using (polynomialFeatureSpace φ (d + r)).smul_mem c hf

lemma star_mem_polynomialFeatureSpace (φ : ι → C(X, ℂ))
    (σ : ι → ι) (hσ : ∀ a, star (φ a) = φ (σ a))
    (r : ℕ) {f : C(X, ℂ)} (hf : f ∈ polynomialFeatureSpace φ r) :
    star f ∈ polynomialFeatureSpace φ r := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨word, rfl⟩ := hf
      simpa [featureMonomial, star_prod, hσ] using
        featureMonomial_mem φ r (fun t => σ (word t))
  | zero => simp
  | add f g _ _ hf hg =>
      simpa using (polynomialFeatureSpace φ r).add_mem hf hg
  | smul c f _ hf =>
      simpa using (polynomialFeatureSpace φ r).smul_mem (star c) hf

theorem matrix_mul_mem_polynomialFeatureSpace {N : Type*} [Fintype N]
    (φ : ι → C(X, ℂ)) (A B : Matrix N N C(X, ℂ)) (d r : ℕ)
    (hA : ∀ i j, A i j ∈ polynomialFeatureSpace φ d)
    (hB : ∀ i j, B i j ∈ polynomialFeatureSpace φ r) :
    ∀ i j, (A * B) i j ∈ polynomialFeatureSpace φ (d + r) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun k _ =>
    mul_mem_polynomialFeatureSpace φ d r (hA i k) (hB k j)

theorem matrix_pow_mem_polynomialFeatureSpace_degree {N : Type*}
    [Fintype N] [DecidableEq N]
    (φ : ι → C(X, ℂ)) (A : Matrix N N C(X, ℂ)) (d : ℕ)
    (hA : ∀ i j, A i j ∈ polynomialFeatureSpace φ d) (r : ℕ) :
    ∀ i j, (A ^ r) i j ∈ polynomialFeatureSpace φ (d * r) := by
  induction r with
  | zero =>
      intro i j
      by_cases h : i = j
      · subst j
        simpa using one_mem_polynomialFeatureSpace_zero φ
      · simp [h]
  | succ r ih =>
      rw [pow_succ']
      simpa [Nat.mul_succ, Nat.add_comm] using
        matrix_mul_mem_polynomialFeatureSpace φ A (A ^ r) d (d * r) hA ih

/-- Matrix powers have the expected homogeneous feature degree, regardless of
the dimension of their matrix index type. -/
theorem matrix_pow_mem_polynomialFeatureSpace {N : Type*} [Fintype N] [DecidableEq N]
    (φ : ι → C(X, ℂ)) (A : Matrix N N C(X, ℂ))
    (hA : ∀ i j, A i j ∈ Submodule.span ℂ (Set.range φ)) (r : ℕ) :
    ∀ i j, (A ^ r) i j ∈ polynomialFeatureSpace φ r := by
  induction r with
  | zero =>
      intro i j
      by_cases h : i = j
      · subst j
        simpa using one_mem_polynomialFeatureSpace_zero φ
      · simp [h]
  | succ r ih =>
      intro i j
      rw [pow_succ', Matrix.mul_apply]
      exact (polynomialFeatureSpace φ (r + 1)).sum_mem fun k _ =>
        linearFeature_mul_mem_polynomialFeatureSpace φ r (hA i k) (ih k j)

section MatrixFeatures

variable {L N : Type*} [Fintype L] [DecidableEq L] [Fintype N] [DecidableEq N]

/-- The local matrix entries, before any spectator system is introduced. -/
def matrixEntryFeatures (A : Matrix L L C(X, ℂ)) : (L × L) → C(X, ℂ) :=
  fun p => A p.1 p.2

/-- Apply an arbitrary linear embedding or contraction to a matrix of local
features. Its output matrix may have any finite dimension. -/
noncomputable def linearFeatureMatrix (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) : Matrix N N C(X, ℂ) :=
  fun i j => ∑ a, ∑ b, (E (Matrix.single a b 1) i j) • A a b

omit [Fintype N] [DecidableEq N] in
lemma linearFeatureMatrix_entry_mem_of (S : Submodule ℂ C(X, ℂ))
    (A : Matrix L L C(X, ℂ)) (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hA : ∀ a b, A a b ∈ S) (i j : N) : linearFeatureMatrix A E i j ∈ S := by
  apply S.sum_mem
  intro a _
  apply S.sum_mem
  intro b _
  exact S.smul_mem _ (hA a b)

omit [Fintype N] [DecidableEq N] in
lemma linearFeatureMatrix_entry_mem (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) (i j : N) :
    linearFeatureMatrix A E i j ∈ Submodule.span ℂ (Set.range (matrixEntryFeatures A)) := by
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

omit [Fintype N] [DecidableEq N] in
lemma linearFeatureMatrix_apply (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) (x : X) (i j : N) :
    linearFeatureMatrix A E i j x = E (fun a b => A a b x) i j := by
  have hsingle (a b : L) (c : ℂ) :
      Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
    simp [Matrix.smul_single]
  conv_rhs => rw [Matrix.matrix_eq_sum_single (fun a b => A a b x)]
  simp only [linearFeatureMatrix, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    map_sum, Matrix.sum_apply, smul_eq_mul]
  congr 1
  funext a
  congr 1
  funext b
  rw [hsingle a b (A a b x), map_smul]
  exact mul_comm _ _

/-- A trace of a matrix power, regarded as a continuous local function. -/
noncomputable def localTracePower (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) (ρ : Matrix N N ℂ) (r : ℕ) : C(X, ℂ) :=
  ∑ i, ∑ j, (ρ i j) • ((linearFeatureMatrix A E) ^ r) j i

theorem localTracePower_mem (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) (ρ : Matrix N N ℂ) (r : ℕ) :
    localTracePower A E ρ r ∈ polynomialFeatureSpace (matrixEntryFeatures A) r := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact matrix_pow_mem_polynomialFeatureSpace (matrixEntryFeatures A)
    (linearFeatureMatrix A E) (linearFeatureMatrix_entry_mem A E) r j i

lemma localTracePower_apply (A : Matrix L L C(X, ℂ))
    (E : Matrix L L ℂ →ₗ[ℂ] Matrix N N ℂ) (ρ : Matrix N N ℂ) (r : ℕ) (x : X) :
    localTracePower A E ρ r x = Matrix.trace (ρ * (E (fun a b => A a b x)) ^ r) := by
  let ev := ContinuousMap.evalAlgHom ℂ ℂ x
  have hpow : (((linearFeatureMatrix A E) ^ r).map ev) =
      (E (fun a b => A a b x)) ^ r := by
    change ev.toRingHom.mapMatrix ((linearFeatureMatrix A E) ^ r) = _
    rw [map_pow]
    congr 1
    ext i j
    exact linearFeatureMatrix_apply A E x i j
  simp only [localTracePower, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  exact congrFun (congrFun hpow j) i

end MatrixFeatures

section Blocks

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A matrix independent of local randomness. -/
def constantMatrix (A : Matrix N N ℂ) : Matrix N N C(X, ℂ) :=
  fun i j => ContinuousMap.const X (A i j)

omit [Fintype N] [DecidableEq N] in
lemma constantMatrix_entry_mem_zero (φ : ι → C(X, ℂ)) (A : Matrix N N ℂ)
    (i j : N) : constantMatrix (X := X) A i j ∈ polynomialFeatureSpace φ 0 := by
  have heq : constantMatrix (X := X) A i j = (A i j) • (1 : C(X, ℂ)) := by
    ext x
    simp [constantMatrix]
  rw [heq]
  exact Submodule.smul_mem _ _ (one_mem_polynomialFeatureSpace_zero φ)

omit [DecidableEq N] in
lemma constantMatrix_mul_mem (φ : ι → C(X, ℂ)) (A : Matrix N N ℂ)
    (B : Matrix N N C(X, ℂ)) (d : ℕ)
    (hB : ∀ i j, B i j ∈ polynomialFeatureSpace φ d) :
    ∀ i j, (constantMatrix (X := X) A * B) i j ∈ polynomialFeatureSpace φ d := by
  simpa using matrix_mul_mem_polynomialFeatureSpace φ (constantMatrix A) B 0 d
    (constantMatrix_entry_mem_zero φ A) hB

omit [DecidableEq N] in
lemma mul_constantMatrix_mem (φ : ι → C(X, ℂ)) (A : Matrix N N C(X, ℂ))
    (B : Matrix N N ℂ) (d : ℕ)
    (hA : ∀ i j, A i j ∈ polynomialFeatureSpace φ d) :
    ∀ i j, (A * constantMatrix (X := X) B) i j ∈ polynomialFeatureSpace φ d := by
  simpa using matrix_mul_mem_polynomialFeatureSpace φ A (constantMatrix B) d 0
    hA (constantMatrix_entry_mem_zero φ B)

lemma matrix_list_prod_mem (φ : ι → C(X, ℂ)) (gates : List (Matrix N N C(X, ℂ)))
    (hgates : ∀ A ∈ gates, ∀ i j, A i j ∈ Submodule.span ℂ (Set.range φ)) :
    ∀ i j, gates.prod i j ∈ polynomialFeatureSpace φ gates.length := by
  induction gates with
  | nil =>
      intro i j
      by_cases h : i = j
      · subst j
        simpa using one_mem_polynomialFeatureSpace_zero φ
      · simp [h]
  | cons A tail ih =>
      have htail := ih (fun B hB => hgates B (by simp [hB]))
      intro i j
      simp only [List.prod_cons, List.length_cons, Matrix.mul_apply]
      exact Submodule.sum_mem _ fun u _ =>
        linearFeature_mul_mem_polynomialFeatureSpace φ tail.length
          (hgates A (by simp) i u) (htail u j)

/-- Ordered product of local gates represented by continuous matrix entries. -/
noncomputable def matrixGateBlock {m : ℕ} (gates : Fin m → Matrix N N C(X, ℂ)) :
    Matrix N N C(X, ℂ) := (List.ofFn gates).prod

lemma matrixGateBlock_mem (φ : ι → C(X, ℂ)) {m : ℕ}
    (gates : Fin m → Matrix N N C(X, ℂ))
    (hgates : ∀ g i j, gates g i j ∈ Submodule.span ℂ (Set.range φ)) :
    ∀ i j, matrixGateBlock gates i j ∈ polynomialFeatureSpace φ m := by
  have hh : ∀ A ∈ List.ofFn gates, ∀ i j,
      A i j ∈ Submodule.span ℂ (Set.range φ) := by
    intro A hA
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hA
    exact hgates g
  simpa [matrixGateBlock] using matrix_list_prod_mem φ (List.ofFn gates) hh

/-- The actual matrix trace formula for the conditional OTOC, with an arbitrary
finite environment. No dimensional information about `N` enters the feature space. -/
noncomputable def matrixBlockOTOC {m : ℕ} (gates : Fin m → Matrix N N C(X, ℂ))
    (ρ B V M : Matrix N N ℂ) (k : ℕ) : C(X, ℂ) :=
  Matrix.trace (constantMatrix ρ *
    (constantMatrix V.conjTranspose *
      ((matrixGateBlock gates).conjTranspose * constantMatrix B * matrixGateBlock gates) *
      constantMatrix V * constantMatrix M) ^ (2 * k))

/-- The conditional OTOC belongs to a fixed space of raw local-entry monomials.
The coefficients may depend on every environment matrix; the space does not. -/
theorem matrixBlockOTOC_mem (φ : ι → C(X, ℂ)) (σ : ι → ι)
    (hσ : ∀ a, star (φ a) = φ (σ a)) {m : ℕ}
    (gates : Fin m → Matrix N N C(X, ℂ))
    (hgates : ∀ g i j, gates g i j ∈ Submodule.span ℂ (Set.range φ))
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    matrixBlockOTOC gates ρ B V M k ∈ polynomialFeatureSpace φ ((m + m) * (2 * k)) := by
  have hblock := matrixGateBlock_mem φ gates hgates
  have hstar : ∀ i j, (matrixGateBlock gates).conjTranspose i j ∈
      polynomialFeatureSpace φ m := by
    intro i j
    exact star_mem_polynomialFeatureSpace φ σ hσ m (hblock j i)
  have hB := mul_constantMatrix_mem φ (matrixGateBlock gates).conjTranspose B m hstar
  have hinner := matrix_mul_mem_polynomialFeatureSpace φ
    ((matrixGateBlock gates).conjTranspose * constantMatrix B) (matrixGateBlock gates)
    m m hB hblock
  have hleft := constantMatrix_mul_mem φ V.conjTranspose _ (m + m) hinner
  have hright := mul_constantMatrix_mem φ _ V (m + m) hleft
  have hdressed := mul_constantMatrix_mem φ _ M (m + m) hright
  have hpow := matrix_pow_mem_polynomialFeatureSpace_degree φ _ (m + m) hdressed (2 * k)
  have hρ := constantMatrix_mul_mem φ ρ _ ((m + m) * (2 * k)) hpow
  exact Submodule.sum_mem _ fun i _ => hρ i i

/-- Evaluation commutes with all matrix operations used in the OTOC. -/
def matrixEval (x : X) : Matrix N N C(X, ℂ) →+* Matrix N N ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix

@[simp] lemma matrixEval_apply (x : X) (A : Matrix N N C(X, ℂ)) (i j : N) :
    matrixEval x A i j = A i j x := rfl

@[simp] lemma matrixEval_constantMatrix (x : X) (A : Matrix N N ℂ) :
    matrixEval x (constantMatrix A) = A := rfl

@[simp] lemma matrixEval_conjTranspose (x : X) (A : Matrix N N C(X, ℂ)) :
    matrixEval x A.conjTranspose = (matrixEval x A).conjTranspose := by
  ext i j
  rfl

@[simp] lemma matrixEval_matrixGateBlock {m : ℕ}
    (gates : Fin m → Matrix N N C(X, ℂ)) (x : X) :
    matrixEval x (matrixGateBlock gates) =
      (List.ofFn (fun g => matrixEval x (gates g))).prod := by
  simpa [matrixGateBlock, List.map_ofFn, Function.comp_def] using
    map_list_prod (matrixEval (N := N) x) (List.ofFn gates)

/-- Explicit trace formula, with the original ordered gate product. -/
theorem matrixBlockOTOC_apply {m : ℕ} (gates : Fin m → Matrix N N C(X, ℂ))
    (ρ B V M : Matrix N N ℂ) (k : ℕ) (x : X) :
    matrixBlockOTOC gates ρ B V M k x =
      let W := (List.ofFn (fun g => matrixEval x (gates g))).prod
      Matrix.trace (ρ * (V.conjTranspose * (W.conjTranspose * B * W) * V * M) ^ (2 * k)) := by
  dsimp only
  change (ContinuousMap.evalAlgHom ℂ ℂ x) (Matrix.trace _) = _
  rw [AddMonoidHom.map_trace]
  change Matrix.trace (matrixEval x _) = _
  simp only [map_mul, map_pow, matrixEval_constantMatrix, matrixEval_conjTranspose,
    matrixEval_matrixGateBlock]

/-- If every local gate evaluates to the identity, the block OTOC is the
identity-block value appearing in the reverse-variance condition. -/
theorem matrixBlockOTOC_apply_identity {m : ℕ}
    (gates : Fin m → Matrix N N C(X, ℂ)) (ρ B V M : Matrix N N ℂ)
    (k : ℕ) (x₀ : X) (hgates : ∀ g, matrixEval x₀ (gates g) = 1) :
    matrixBlockOTOC gates ρ B V M k x₀ =
      Matrix.trace (ρ * (V.conjTranspose * B * V * M) ^ (2 * k)) := by
  rw [matrixBlockOTOC_apply]
  simp [hgates]

end Blocks

/-- Tensoring a local matrix with the identity on an arbitrary spectator type,
written entrywise so the spectator dimension is completely explicit. -/
def spectatorEmbedding (L S : Type*) [DecidableEq S] :
    Matrix L L ℂ →ₗ[ℂ] Matrix (L × S) (L × S) ℂ where
  toFun A i j := if i.2 = j.2 then A i.1 j.1 else 0
  map_add' A B := by
    ext i j
    by_cases h : i.2 = j.2 <;> simp [h]
  map_smul' c A := by
    ext i j
    by_cases h : i.2 = j.2 <;> simp [h]

@[simp] theorem spectatorEmbedding_one (L S : Type*) [DecidableEq L] [DecidableEq S] :
    spectatorEmbedding L S (1 : Matrix L L ℂ) = 1 := by
  ext i j
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [spectatorEmbedding, Matrix.one_apply, Prod.ext_iff, h₁, h₂]

end Fluctuations
