import Fluctuations.HaarLocalVariance
import Fluctuations.HaarEvaluationBound

open MeasureTheory
open scoped BigOperators ENNReal

namespace Fluctuations

section TensorFeatures

variable {X ι : Type*} [TopologicalSpace X]

/-- One feature from each gate. The gate word fixes the degree in every gate. -/
noncomputable def tensorFeatures {m : ℕ} (φ : Fin m → ι → C(X, ℂ))
    (word : Fin m → ι) : C(X, ℂ) := ∏ g, φ g (word g)

lemma tensorFeatures_cons_mul {m : ℕ} (φ : Fin (m + 1) → ι → C(X, ℂ))
    {f g : C(X, ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range (φ 0)))
    (hg : g ∈ Submodule.span ℂ (Set.range (tensorFeatures (fun t => φ t.succ)))) :
    f * g ∈ Submodule.span ℂ (Set.range (tensorFeatures φ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨word, rfl⟩ := hg
          apply Submodule.subset_span
          refine ⟨Fin.cons a word, ?_⟩
          simp [tensorFeatures, Fin.prod_univ_succ]
      | zero => simp
      | add g h _ _ hg hh =>
          simpa [mul_add] using (Submodule.span ℂ (Set.range (tensorFeatures φ))).add_mem hg hh
      | smul c g _ hg =>
          simpa [mul_smul_comm] using
            (Submodule.span ℂ (Set.range (tensorFeatures φ))).smul_mem c hg
  | zero => simp
  | add f h _ _ hf hh =>
      simpa [add_mul] using (Submodule.span ℂ (Set.range (tensorFeatures φ))).add_mem hf hh
  | smul c f _ hf =>
      simpa [smul_mul_assoc] using
        (Submodule.span ℂ (Set.range (tensorFeatures φ))).smul_mem c hf

lemma tensorFeatures_prod_mem {m : ℕ} (φ : Fin m → ι → C(X, ℂ))
    (f : Fin m → C(X, ℂ)) (hf : ∀ g, f g ∈ Submodule.span ℂ (Set.range (φ g))) :
    (∏ g, f g) ∈ Submodule.span ℂ (Set.range (tensorFeatures φ)) := by
  induction m with
  | zero =>
      simpa [tensorFeatures] using (Submodule.subset_span
        (R := ℂ) (s := Set.range (tensorFeatures φ)) ⟨(fun t => Fin.elim0 t), rfl⟩)
  | succ m ih =>
      rw [Fin.prod_univ_succ]
      exact tensorFeatures_cons_mul φ (hf 0)
        (ih (fun t => φ t.succ) (fun t => f t.succ) (fun t => hf t.succ))

lemma matrixGateBlock_tensor_mem {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]
    (φ : Fin m → ι → C(X, ℂ)) (gates : Fin m → Matrix N N C(X, ℂ))
    (hgates : ∀ g i j, gates g i j ∈ Submodule.span ℂ (Set.range (φ g))) :
    ∀ i j, matrixGateBlock gates i j ∈
      Submodule.span ℂ (Set.range (tensorFeatures φ)) := by
  induction m with
  | zero =>
      intro i j
      by_cases h : i = j
      · subst j
        simpa [matrixGateBlock, tensorFeatures] using (Submodule.subset_span
          (R := ℂ) (s := Set.range (tensorFeatures φ)) ⟨(fun t => Fin.elim0 t), rfl⟩)
      · simp [matrixGateBlock, h]
  | succ m ih =>
      intro i j
      have heq : matrixGateBlock gates = gates 0 *
          matrixGateBlock (fun t => gates t.succ) := by
        simp [matrixGateBlock, List.ofFn_succ]
      rw [heq, Matrix.mul_apply]
      apply Submodule.sum_mem
      intro u _
      exact tensorFeatures_cons_mul φ (hgates 0 i u)
        (ih (fun t => φ t.succ) (fun t => gates t.succ)
          (fun t => hgates t.succ) u j)

/-- Pairing a gate word with a conjugated gate word balances the two degrees. -/
noncomputable def pairedFeatures (φ : ι → C(X, ℂ)) (p : ι × ι) : C(X, ℂ) :=
  star (φ p.1) * φ p.2

lemma star_mul_mem_pairedFeatures (φ : ι → C(X, ℂ)) {f g : C(X, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range φ))
    (hg : g ∈ Submodule.span ℂ (Set.range φ)) :
    star f * g ∈ Submodule.span ℂ (Set.range (pairedFeatures φ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨b, rfl⟩ := hg
          exact Submodule.subset_span ⟨(a, b), rfl⟩
      | zero => simp
      | add g h _ _ hg hh =>
          simpa [mul_add] using (Submodule.span ℂ (Set.range (pairedFeatures φ))).add_mem hg hh
      | smul c g _ hg =>
          simpa [mul_smul_comm] using
            (Submodule.span ℂ (Set.range (pairedFeatures φ))).smul_mem c hg
  | zero => simp
  | add f h _ _ hf hh =>
      simpa [star_add, add_mul] using
        (Submodule.span ℂ (Set.range (pairedFeatures φ))).add_mem hf hh
  | smul c f _ hf =>
      simpa [star_smul, smul_mul_assoc] using
        (Submodule.span ℂ (Set.range (pairedFeatures φ))).smul_mem (star c) hf

end TensorFeatures

section MatrixPairing

variable {X ι N : Type*} [TopologicalSpace X] [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
lemma constantMatrix_mul_submodule (S : Submodule ℂ C(X, ℂ))
    (A : Matrix N N ℂ) (B : Matrix N N C(X, ℂ))
    (hB : ∀ i j, B i j ∈ S) : ∀ i j, (constantMatrix (X := X) A * B) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  apply S.sum_mem
  intro u _
  convert S.smul_mem (A i u) (hB u j) using 1

omit [DecidableEq N] in
lemma mul_constantMatrix_submodule (S : Submodule ℂ C(X, ℂ))
    (A : Matrix N N C(X, ℂ)) (B : Matrix N N ℂ)
    (hA : ∀ i j, A i j ∈ S) : ∀ i j, (A * constantMatrix (X := X) B) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  apply S.sum_mem
  intro u _
  convert S.smul_mem (B u j) (hA i u) using 1
  ext x
  simp [constantMatrix, mul_comm]

theorem matrixBlockOTOC_paired_mem {m : ℕ}
    (φ : ι → C(X, ℂ)) (gates : Fin m → Matrix N N C(X, ℂ))
    (hblock : ∀ i j, matrixGateBlock gates i j ∈ Submodule.span ℂ (Set.range φ))
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    matrixBlockOTOC gates ρ B V M k ∈ polynomialFeatureSpace (pairedFeatures φ) (2 * k) := by
  let S := Submodule.span ℂ (Set.range (pairedFeatures φ))
  have hBW := constantMatrix_mul_submodule (Submodule.span ℂ (Set.range φ))
    B (matrixGateBlock gates) hblock
  have hinner : ∀ i j, ((matrixGateBlock gates).conjTranspose * constantMatrix (X := X) B *
      matrixGateBlock gates) i j ∈ S := by
    intro i j
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    apply S.sum_mem
    intro u _
    exact star_mul_mem_pairedFeatures φ (hblock u i) (hBW u j)
  have hleft := constantMatrix_mul_submodule S V.conjTranspose _ hinner
  have hright := mul_constantMatrix_submodule S _ V hleft
  have hdressed := mul_constantMatrix_submodule S _ M hright
  have hpow := matrix_pow_mem_polynomialFeatureSpace (pairedFeatures φ) _ hdressed (2 * k)
  have hρ := constantMatrix_mul_mem (pairedFeatures φ) ρ _ (2 * k) hpow
  exact Submodule.sum_mem _ fun i _ => hρ i i

end MatrixPairing

/-- Gate-word products before pairing with their conjugates. -/
noncomputable def su4WordFeatures (m : ℕ) : (Fin m → Fin 4 × Fin 4) → C(SU4Block m, ℂ) :=
  tensorFeatures (fun g p => su4Entry m g p.1 p.2)

/-- Balanced block features. There are precisely `16^(2*m)` feature indices. -/
noncomputable def balancedSU4Features (m : ℕ) := pairedFeatures (su4WordFeatures m)

theorem haarLocalOTOC_balanced_mem {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    haarLocalOTOC E ρ B V M k ∈ polynomialFeatureSpace (balancedSU4Features m) (2 * k) := by
  apply matrixBlockOTOC_paired_mem (su4WordFeatures m) (haarGateMatrix E)
  apply matrixGateBlock_tensor_mem
  intro g i j
  apply linearFeatureMatrix_entry_mem_of
  intro a b
  exact Submodule.subset_span ⟨(a, b), rfl⟩

lemma algHom_polynomialFeatureSpace_mem {X ι : Type*} [TopologicalSpace X]
    (φ : ι → C(X, ℂ)) (A : C(X, ℂ) →ₐ[ℂ] C(X, ℂ))
    (hA : ∀ i, A (φ i) ∈ Submodule.span ℂ (Set.range φ)) (r : ℕ)
    {f : C(X, ℂ)} (hf : f ∈ polynomialFeatureSpace φ r) :
    A f ∈ polynomialFeatureSpace φ r := by
  have hmono : ∀ d (word : Fin d → ι),
      A (featureMonomial φ d word) ∈ polynomialFeatureSpace φ d := by
    intro d
    induction d with
    | zero =>
        intro word
        simpa [featureMonomial] using one_mem_polynomialFeatureSpace_zero φ
    | succ d ih =>
        intro word
        simpa [featureMonomial, Fin.prod_univ_succ, map_mul] using
          linearFeature_mul_mem_polynomialFeatureSpace φ d (hA (word 0))
            (ih (fun t => word t.succ))
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨word, rfl⟩ := hf
      exact hmono r word
  | zero => simp
  | add f g _ _ hf hg =>
      simpa using (polynomialFeatureSpace φ r).add_mem hf hg
  | smul c f _ hf =>
      simpa using (polynomialFeatureSpace φ r).smul_mem c hf

lemma leftTranslate_su4Entry (m : ℕ) (a : SU4Block m) (g : Fin m) (i j : Fin 4) :
    leftTranslate a (su4Entry m g i j) =
      ∑ u : Fin 4, ((a g).val i u) • su4Entry m g u j := by
  ext x
  change ((a g) * (x g)).val i j = _
  simp [Matrix.mul_apply]

lemma leftTranslate_su4Entry_mem (m : ℕ) (a : SU4Block m) (g : Fin m) (i j : Fin 4) :
    leftTranslate a (su4Entry m g i j) ∈
      Submodule.span ℂ (Set.range (fun p : Fin 4 × Fin 4 => su4Entry m g p.1 p.2)) := by
  rw [leftTranslate_su4Entry]
  apply Submodule.sum_mem
  intro u _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(u, j), rfl⟩

lemma leftTranslate_su4WordFeatures_mem (m : ℕ) (a : SU4Block m)
    (word : Fin m → Fin 4 × Fin 4) :
    leftTranslate a (su4WordFeatures m word) ∈
      Submodule.span ℂ (Set.range (su4WordFeatures m)) := by
  have hh := tensorFeatures_prod_mem (m := m) (ι := Fin 4 × Fin 4)
    (fun (g : Fin m) (p : Fin 4 × Fin 4) => su4Entry m g p.1 p.2)
    (fun (g : Fin m) => leftTranslate a (su4Entry m g (word g).1 (word g).2))
    (fun g => leftTranslate_su4Entry_mem m a g (word g).1 (word g).2)
  simpa only [su4WordFeatures, tensorFeatures, map_prod] using hh

lemma leftTranslate_balancedSU4Features_mem (m : ℕ) (a : SU4Block m)
    (p : (Fin m → Fin 4 × Fin 4) × (Fin m → Fin 4 × Fin 4)) :
    leftTranslate a (balancedSU4Features m p) ∈
      Submodule.span ℂ (Set.range (balancedSU4Features m)) := by
  have heq : leftTranslate a (balancedSU4Features m p) =
      star (leftTranslate a (su4WordFeatures m p.1)) *
        leftTranslate a (su4WordFeatures m p.2) := by
    ext x
    rfl
  rw [heq]
  exact star_mul_mem_pairedFeatures (su4WordFeatures m)
    (leftTranslate_su4WordFeatures_mem m a p.1)
    (leftTranslate_su4WordFeatures_mem m a p.2)

theorem balancedSU4_polynomial_translate_mem (m r : ℕ) (a : SU4Block m)
    (f : C(SU4Block m, ℂ))
    (hf : f ∈ polynomialFeatureSpace (balancedSU4Features m) r) :
    leftTranslate a f ∈ polynomialFeatureSpace (balancedSU4Features m) r :=
  algHom_polynomialFeatureSpace_mem (balancedSU4Features m) (leftTranslate a)
    (leftTranslate_balancedSU4Features_mem m a) r hf

theorem balancedSU4_polynomial_finrank_le (m k : ℕ) :
    Module.finrank ℂ (polynomialFeatureSpace (balancedSU4Features m) (2 * k)) ≤
      4 ^ (8 * k * m) := by
  have hh := polynomialFeatureSpace_finrank_le (balancedSU4Features m) (2 * k)
  convert hh using 1
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  calc
    4 ^ (8 * k * m) = ((4 * 4) ^ m * (4 * 4) ^ m) ^ (2 * k) := by
      simp only [← pow_mul, ← pow_two]
      congr 1
      ring

end Fluctuations
