import Fluctuations.HaarTensorInvariants
import Fluctuations.WeingartenGramBounds
import Fluctuations.GlobalHaarStateIndependence
import Fluctuations.GlobalHaarPauliMean

open scoped BigOperators Matrix

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] in
@[simp] theorem tensorPositionPermutation_one (r : ℕ) :
    tensorPositionPermutation N (1 : Equiv.Perm (Fin r)) = 1 := by
  ext x y
  simp [tensorPositionPermutation, Matrix.one_apply]

theorem tensorPositionPermutation_mul {r : ℕ} (σ τ : Equiv.Perm (Fin r)) :
    tensorPositionPermutation N σ * tensorPositionPermutation N τ =
      tensorPositionPermutation N (τ * σ) := by
  ext x y
  simp [Matrix.mul_apply, tensorPositionPermutation, mul_ite, Function.comp_def]

omit [Fintype N] in
theorem tensorPositionPermutation_star {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    star (tensorPositionPermutation N σ) = tensorPositionPermutation N σ⁻¹ := by
  ext x y
  have heq : y = x ∘ σ ↔ x = y ∘ (σ⁻¹ : Equiv.Perm (Fin r)) := by
    constructor
    · intro h
      funext t
      simpa using congrFun h (σ⁻¹ t) |>.symm
    · intro h
      funext t
      simpa using congrFun h (σ t) |>.symm
  simp [tensorPositionPermutation, Matrix.star_apply, heq]

/-- Cycle labels include fixed points as one-point cycles. -/
abbrev PermutationCycleIndex {r : ℕ} (σ : Equiv.Perm (Fin r)) :=
  Function.fixedPoints σ ⊕ σ.cycleFactorsFinset

noncomputable def permutationCycleLabel {r : ℕ} (σ : Equiv.Perm (Fin r))
    (t : Fin r) : PermutationCycleIndex σ :=
  if ht : σ t = t then Sum.inl ⟨t, ht⟩ else
    Sum.inr ⟨σ.cycleOf t, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr ht)⟩

lemma permutationCycleLabel_apply {r : ℕ} (σ : Equiv.Perm (Fin r)) (t : Fin r) :
    permutationCycleLabel σ (σ t) = permutationCycleLabel σ t := by
  classical
  by_cases ht : σ t = t
  · simp [ht]
  · have hst : σ (σ t) ≠ σ t := fun h => ht (σ.injective h)
    simp only [permutationCycleLabel, dif_neg ht, dif_neg hst]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact σ.cycleOf_self_apply t

noncomputable def permutationCycleRepresentative {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    PermutationCycleIndex σ → Fin r
  | Sum.inl t => t.val
  | Sum.inr c => (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support.choose

lemma permutationCycleRepresentative_mem {r : ℕ} (σ : Equiv.Perm (Fin r))
    (c : σ.cycleFactorsFinset) : permutationCycleRepresentative σ (Sum.inr c) ∈ c.val.support :=
  (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support.choose_spec

lemma permutationCycleLabel_representative {r : ℕ} (σ : Equiv.Perm (Fin r))
    (c : PermutationCycleIndex σ) :
    permutationCycleLabel σ (permutationCycleRepresentative σ c) = c := by
  classical
  rcases c with t | c
  · have ht : σ t.val = t.val := t.prop
    simp [permutationCycleRepresentative, permutationCycleLabel, ht]
  · have hc := permutationCycleRepresentative_mem σ c
    have hs : σ (permutationCycleRepresentative σ (Sum.inr c)) ≠
        permutationCycleRepresentative σ (Sum.inr c) :=
      Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hc)
    simp only [permutationCycleLabel, dif_neg hs]
    apply congrArg Sum.inr
    apply Subtype.ext
    exact (σ.eq_cycleOf_of_mem_cycleFactorsFinset_iff c.val c.prop _).mpr hc |>.symm

omit [Fintype N] [DecidableEq N] in
lemma invariant_word_sameCycle {r : ℕ} (σ : Equiv.Perm (Fin r))
    (x : Fin r → N) (hx : x = x ∘ σ) {i j : Fin r} (hij : σ.SameCycle i j) :
    x i = x j := by
  obtain ⟨n, hn⟩ := hij.exists_nat_pow_eq
  have hp : ∀ n : ℕ, x ((σ ^ n) i) = x i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (congrFun hx ((σ ^ n) i)).symm.trans ih
  rw [← hn]
  exact (hp n).symm

omit [Fintype N] [DecidableEq N] in
lemma invariant_word_cycleRepresentative {r : ℕ} (σ : Equiv.Perm (Fin r))
    (x : Fin r → N) (hx : x = x ∘ σ) (t : Fin r) :
    x (permutationCycleRepresentative σ (permutationCycleLabel σ t)) = x t := by
  classical
  by_cases ht : σ t = t
  · simp [permutationCycleLabel, ht, permutationCycleRepresentative]
  · simp only [permutationCycleLabel, dif_neg ht]
    apply invariant_word_sameCycle σ x hx
    have hc := permutationCycleRepresentative_mem σ
      ⟨σ.cycleOf t, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr ht)⟩
    exact (Equiv.Perm.mem_support_cycleOf_iff.mp hc).1.symm

/-- A word fixed by a permutation is precisely a choice of one color for
each cycle, including each fixed point. -/
noncomputable def invariantWordEquiv {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    {x : Fin r → N // x = x ∘ σ} ≃ (PermutationCycleIndex σ → N) where
  toFun x c := x.val (permutationCycleRepresentative σ c)
  invFun f := ⟨fun t => f (permutationCycleLabel σ t), by
    funext t
    simp [permutationCycleLabel_apply]⟩
  left_inv x := by
    apply Subtype.ext
    funext t
    exact invariant_word_cycleRepresentative σ x.val x.prop t
  right_inv f := by
    funext c
    simp [permutationCycleLabel_representative]

lemma card_permutationCycleIndex {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Fintype.card (PermutationCycleIndex σ) = permutationTotalCycles σ := by
  classical
  simp only [PermutationCycleIndex, Fintype.card_sum, Equiv.Perm.card_fixedPoints,
    Equiv.Perm.sum_cycleType, Fintype.card_fin, Fintype.card_coe, permutationTotalCycles]
  congr 1
  simp [Equiv.Perm.cycleType_def]

theorem tensorPositionPermutation_trace {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPositionPermutation N σ) =
      (Fintype.card N : ℂ) ^ permutationTotalCycles σ := by
  classical
  have hc := Fintype.card_congr (invariantWordEquiv (N := N) σ)
  simp only [Fintype.card_fun, card_permutationCycleIndex] at hc
  simp only [Matrix.trace, Matrix.diag, tensorPositionPermutation]
  rw [← Nat.cast_pow, ← hc]
  simp only [Finset.sum_boole, Nat.cast_inj]
  exact (Fintype.card_subtype _).symm

lemma permutationTotalCycles_conj {r : ℕ} (σ τ : Equiv.Perm (Fin r)) :
    permutationTotalCycles (τ * σ * τ⁻¹) = permutationTotalCycles σ := by
  simp only [permutationTotalCycles, Equiv.Perm.card_support_conj, Equiv.Perm.cycleType_conj]

lemma permutationTotalCycles_mul_comm {r : ℕ} (σ τ : Equiv.Perm (Fin r)) :
    permutationTotalCycles (σ * τ) = permutationTotalCycles (τ * σ) := by
  have heq : σ * (τ * σ) * σ⁻¹ = σ * τ := by group
  simpa only [heq] using permutationTotalCycles_conj (τ * σ) σ

/-- The true Hilbert-Schmidt Gram matrix of the permutation operators. -/
theorem tensorPositionPermutation_gram {r : ℕ} (σ τ : Equiv.Perm (Fin r)) :
    Matrix.trace ((tensorPositionPermutation N σ).conjTranspose *
      tensorPositionPermutation N τ) =
        (Fintype.card N : ℂ) ^ permutationTotalCycles (σ⁻¹ * τ) := by
  change Matrix.trace (star (tensorPositionPermutation N σ) *
    tensorPositionPermutation N τ) = _
  rw [tensorPositionPermutation_star, tensorPositionPermutation_mul,
    tensorPositionPermutation_trace, permutationTotalCycles_mul_comm]

lemma permutationCycleLabel_eq_inl {r : ℕ} (σ : Equiv.Perm (Fin r))
    (t : Fin r) (i : Function.fixedPoints σ) :
    permutationCycleLabel σ t = Sum.inl i ↔ t = i.val := by
  classical
  by_cases ht : σ t = t
  · simp only [permutationCycleLabel, dif_pos ht, Sum.inl.injEq, Subtype.ext_iff]
  · have hti : t ≠ i.val := by
      intro h
      subst t
      exact ht i.prop
    simp [permutationCycleLabel, ht, hti]

lemma permutationCycleLabel_eq_inr {r : ℕ} (σ : Equiv.Perm (Fin r))
    (t : Fin r) (c : σ.cycleFactorsFinset) :
    permutationCycleLabel σ t = Sum.inr c ↔ t ∈ c.val.support := by
  classical
  by_cases ht : σ t = t
  · have hc : t ∉ c.val.support := fun hc =>
      (Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hc)) ht
    simp [permutationCycleLabel, ht, hc]
  · simp only [permutationCycleLabel, dif_neg ht, Sum.inr.injEq, Subtype.ext_iff]
    rw [eq_comm]
    exact σ.eq_cycleOf_of_mem_cycleFactorsFinset_iff c.val c.prop t

def permutationCycleLength {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    PermutationCycleIndex σ → ℕ
  | Sum.inl _ => 1
  | Sum.inr c => c.val.support.card

lemma card_permutationCycleLabel_fiber {r : ℕ} (σ : Equiv.Perm (Fin r))
    (c : PermutationCycleIndex σ) :
    Fintype.card {t // permutationCycleLabel σ t = c} = permutationCycleLength σ c := by
  classical
  rcases c with i | c
  · simpa only [permutationCycleLength, Fintype.card_subtype_eq] using
      Fintype.card_congr (Equiv.subtypeEquivRight (fun t => permutationCycleLabel_eq_inl σ t i))
  · simpa only [permutationCycleLength, Fintype.card_coe] using
      Fintype.card_congr (Equiv.subtypeEquivRight (fun t => permutationCycleLabel_eq_inr σ t c))

/-- Diagonal tensor traces factor independently over the permutation cycles. -/
theorem tensorPowerMatrix_diagonal_trace_permutation {r : ℕ}
    (d : N → ℂ) (σ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPowerMatrix r (Matrix.diagonal d) * tensorPositionPermutation N σ) =
      ∏ c : PermutationCycleIndex σ, ∑ a : N, d a ^ permutationCycleLength σ c := by
  classical
  rw [tensorPowerMatrix_diagonal]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, tensorPositionPermutation]
  simp only [mul_ite, mul_one, mul_zero]
  have hsub : (∑ x : Fin r → N, if x = x ∘ σ then ∏ t, d (x t) else 0) =
      ∑ x : {x : Fin r → N // x = x ∘ σ}, ∏ t, d (x.val t) := by
    simp only [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hsub]
  have heq : (∑ x : {x : Fin r → N // x = x ∘ σ}, ∏ t, d (x.val t)) =
      ∑ f : PermutationCycleIndex σ → N, ∏ t, d (f (permutationCycleLabel σ t)) := by
    apply Fintype.sum_equiv (invariantWordEquiv (N := N) σ)
    intro x
    apply Finset.prod_congr rfl
    intro t _
    exact congrArg d (invariant_word_cycleRepresentative σ x.val x.prop t).symm
  rw [heq, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Fintype.prod_fiberwise' (permutationCycleLabel σ) (fun c => d (f c))]
  simp only [Finset.prod_const, Finset.card_univ, card_permutationCycleLabel_fiber]

lemma sum_balancedZSign_pow (S : Type*) [Fintype S] (n : ℕ) :
    (∑ a : Bool × S, balancedZSign a ^ n) =
      if Even n then (Fintype.card (Bool × S) : ℂ) else 0 := by
  classical
  rcases Nat.even_or_odd n with hn | hn
  · simp [balancedZSign, hn, hn.neg_pow]
  · have he : ¬Even n := Nat.not_even_iff_odd.mpr hn
    simp [Fintype.sum_prod_type, balancedZSign, he, hn.neg_pow]

theorem evenCyclePerms_iff_cycleLength_even {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    σ ∈ evenCyclePerms r ↔ ∀ c : PermutationCycleIndex σ, Even (permutationCycleLength σ c) := by
  classical
  constructor
  · intro hσ c
    have hh := (Finset.mem_filter.mp hσ).2
    rcases c with i | c
    · have hi : i.val ∈ σ.support := by rw [hh.1]; exact Finset.mem_univ _
      exact False.elim ((Equiv.Perm.mem_support.mp hi) i.prop)
    · apply hh.2
      rw [Equiv.Perm.cycleType_def]
      exact Multiset.mem_map.mpr ⟨c.val, c.prop, rfl⟩
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply Finset.eq_univ_of_forall
      intro t
      apply Equiv.Perm.mem_support.mpr
      intro ht
      have hh := h (Sum.inl ⟨t, ht⟩)
      norm_num [permutationCycleLength] at hh
    · intro d hd
      rw [Equiv.Perm.cycleType_def] at hd
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hd
      exact h (Sum.inr ⟨c, hc⟩)

/-- Actual trace contraction for the balanced Pauli probe: odd cycles,
including fixed points, vanish; each surviving cycle contributes dimension. -/
theorem tensorPowerMatrix_balancedZ_trace_permutation
    (S : Type*) [Fintype S] [DecidableEq S] {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPowerMatrix r (balancedZProbe S) *
      tensorPositionPermutation (Bool × S) σ) =
      if σ ∈ evenCyclePerms r then (Fintype.card (Bool × S) : ℂ) ^ haarCycleCount σ else 0 := by
  classical
  unfold balancedZProbe
  rw [tensorPowerMatrix_diagonal_trace_permutation]
  by_cases hσ : σ ∈ evenCyclePerms r
  · rw [if_pos hσ]
    have hall := (evenCyclePerms_iff_cycleLength_even σ).mp hσ
    simp_rw [sum_balancedZSign_pow S, if_pos (hall _)]
    simp only [Finset.prod_const, Finset.card_univ, card_permutationCycleIndex,
      permutationTotalCycles, evenCyclePerms_support hσ, Finset.card_univ,
      Fintype.card_fin, Nat.sub_self, zero_add, haarCycleCount]
  · rw [if_neg hσ]
    have hnot : ¬∀ c : PermutationCycleIndex σ, Even (permutationCycleLength σ c) :=
      fun h => hσ ((evenCyclePerms_iff_cycleLength_even σ).mpr h)
    push_neg at hnot
    obtain ⟨c, hc⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    rw [sum_balancedZSign_pow S, if_neg hc]

/-- Conjugating all tensor factors leaves contraction against a position
permutation unchanged. -/
theorem tensorPowerMatrix_unitary_conjugate_trace_permutation {r : ℕ}
    (U : Matrix.unitaryGroup N ℂ) (B : Matrix N N ℂ) (σ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPowerMatrix r (U.val * B * U.val.conjTranspose) *
      tensorPositionPermutation N σ) =
    Matrix.trace (tensorPowerMatrix r B * tensorPositionPermutation N σ) := by
  let R := tensorPowerMatrix r U.val
  let X := tensorPowerMatrix r B
  let P := tensorPositionPermutation N σ
  have hRU : R ∈ Matrix.unitaryGroup (Fin r → N) ℂ :=
    tensorPowerMatrix_mem_unitary r U.val U.prop
  have hPR : P * R = R * P := (tensorPositionPermutation_commute r σ U.val).eq
  have hRR : star R * R = 1 := hRU.1
  rw [tensorPowerMatrix_mul, tensorPowerMatrix_mul]
  change Matrix.trace (R * X * tensorPowerMatrix r (star U.val) * P) = _
  rw [tensorPowerMatrix_star]
  change Matrix.trace (R * X * star R * P) = Matrix.trace (X * P)
  calc
    Matrix.trace (R * X * star R * P) = Matrix.trace (X * (star R * (P * R))) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm R (X * star R * P)
    _ = Matrix.trace (X * P) := by rw [hPR, ← Matrix.mul_assoc (star R), hRR, Matrix.one_mul]

omit [DecidableEq N] in
lemma sum_sign_pow (q : N → ℂ) (hq : ∀ i, q i = 1 ∨ q i = -1)
    (htr : ∑ i, q i = 0) (n : ℕ) :
    (∑ i, q i ^ n) = if Even n then (Fintype.card N : ℂ) else 0 := by
  classical
  rcases Nat.even_or_odd n with hn | hn
  · rw [if_pos hn]
    have hp : ∀ i, q i ^ n = 1 := by
      intro i
      rcases hq i with h | h <;> simp [h, hn.neg_pow]
    simp [hp]
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have hp : ∀ i, q i ^ n = q i := by
      intro i
      rcases hq i with h | h <;> simp [h, hn.neg_pow]
    simp only [hp, htr]

/-- The exact tensor contraction for every Hermitian traceless involution.
All odd cycles vanish and each even cycle contributes the full dimension. -/
theorem tensorPowerMatrix_traceless_involution_trace_permutation
    (B : Matrix N N ℂ) (hB : B.IsHermitian) (hB2 : B * B = 1)
    (htr : Matrix.trace B = 0) {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Matrix.trace (tensorPowerMatrix r B * tensorPositionPermutation N σ) =
      if σ ∈ evenCyclePerms r then (Fintype.card N : ℂ) ^ haarCycleCount σ else 0 := by
  classical
  let U := hB.eigenvectorUnitary
  let q : N → ℂ := RCLike.ofReal ∘ hB.eigenvalues
  have hs : U.val * Matrix.diagonal q * U.val.conjTranspose = B := hB.spectral_theorem.symm
  have hdiag : U.val.conjTranspose * B * U.val = Matrix.diagonal q :=
    hB.star_mul_self_mul_eq_diagonal
  have hsum : ∑ i, q i = 0 := by
    rw [← Matrix.trace_diagonal, ← hdiag]
    exact (globalHaarConjugate_trace B U).trans htr
  have hq : ∀ i, q i = 1 ∨ q i = -1 := hermitian_involution_eigenvalues_sign B hB hB2
  rw [← hs, tensorPowerMatrix_unitary_conjugate_trace_permutation,
    tensorPowerMatrix_diagonal_trace_permutation]
  by_cases hσ : σ ∈ evenCyclePerms r
  · rw [if_pos hσ]
    have hall := (evenCyclePerms_iff_cycleLength_even σ).mp hσ
    simp_rw [sum_sign_pow q hq hsum, if_pos (hall _)]
    simp only [Finset.prod_const, Finset.card_univ, card_permutationCycleIndex,
      permutationTotalCycles, evenCyclePerms_support hσ, Finset.card_univ,
      Fintype.card_fin, Nat.sub_self, zero_add, haarCycleCount]
  · rw [if_neg hσ]
    have hnot : ¬∀ c : PermutationCycleIndex σ, Even (permutationCycleLength σ c) :=
      fun h => hσ ((evenCyclePerms_iff_cycleLength_even σ).mpr h)
    push_neg at hnot
    obtain ⟨c, hc⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    rw [sum_sign_pow q hq hsum, if_neg hc]

end Fluctuations
