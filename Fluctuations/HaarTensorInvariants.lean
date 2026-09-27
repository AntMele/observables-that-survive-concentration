import Fluctuations.GlobalHaarMean
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The algebraic tensor-power commutant, proved by evaluating an injective
basis word and transporting it using arbitrary column-selection matrices. -/

open scoped BigOperators Matrix

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The tensor power on the actual computational basis of words. -/
def tensorPowerMatrix (r : ℕ) (A : Matrix N N ℂ) :
    Matrix (Fin r → N) (Fin r → N) ℂ :=
  fun x y => ∏ t, A (x t) (y t)

omit [DecidableEq N] in
lemma tensorPowerMatrix_mul (r : ℕ) (A B : Matrix N N ℂ) :
    tensorPowerMatrix r (A * B) = tensorPowerMatrix r A * tensorPowerMatrix r B := by
  ext x y
  simp only [Matrix.mul_apply, tensorPowerMatrix, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun t z => A (x t) z * B z (y t))

omit [Fintype N] [DecidableEq N] in
lemma tensorPowerMatrix_star (r : ℕ) (A : Matrix N N ℂ) :
    tensorPowerMatrix r (star A) = star (tensorPowerMatrix r A) := by
  ext x y
  simp [tensorPowerMatrix]

omit [Fintype N] in
lemma word_product_indicator (r : ℕ) (x y : Fin r → N) :
    (∏ t, if x t = y t then (1 : ℂ) else 0) = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · simp [h]
  · rw [if_neg h]
    have hex : ∃ t, x t ≠ y t := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨t, ht⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

omit [Fintype N] in
@[simp] lemma tensorPowerMatrix_one (r : ℕ) :
    tensorPowerMatrix r (1 : Matrix N N ℂ) = 1 := by
  ext x y
  simp only [tensorPowerMatrix, Matrix.one_apply]
  exact word_product_indicator r x y

omit [Fintype N] in
lemma tensorPowerMatrix_diagonal (r : ℕ) (d : N → ℂ) :
    tensorPowerMatrix r (Matrix.diagonal d) =
      Matrix.diagonal (fun x : Fin r → N => ∏ t, d (x t)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorPowerMatrix]
  · have hex : ∃ t, x t ≠ y t := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨t, ht⟩ := hex
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    simp [ht]

lemma tensorPowerMatrix_mem_unitary (r : ℕ) (U : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) :
    tensorPowerMatrix r U ∈ Matrix.unitaryGroup (Fin r → N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [← tensorPowerMatrix_star, ← tensorPowerMatrix_mul, hU.2, tensorPowerMatrix_one]

omit [Fintype N] [DecidableEq N] in
lemma tensorPowerMatrix_continuous (r : ℕ) :
    Continuous (tensorPowerMatrix r : Matrix N N ℂ → Matrix (Fin r → N) (Fin r → N) ℂ) := by
  unfold tensorPowerMatrix
  fun_prop

/-- Permute tensor positions, retaining the physical site dimension. -/
def tensorPositionPermutation (N : Type*) [DecidableEq N] {r : ℕ}
    (σ : Equiv.Perm (Fin r)) : Matrix (Fin r → N) (Fin r → N) ℂ :=
  fun x y => if x = y ∘ σ then 1 else 0

/-- Each position permutation commutes with every tensor power. -/
lemma tensorPositionPermutation_commute (r : ℕ) (σ : Equiv.Perm (Fin r))
    (A : Matrix N N ℂ) :
    Commute (tensorPositionPermutation N σ) (tensorPowerMatrix r A) := by
  change tensorPositionPermutation N σ * tensorPowerMatrix r A =
    tensorPowerMatrix r A * tensorPositionPermutation N σ
  ext x y
  simp only [Matrix.mul_apply, tensorPositionPermutation]
  have hleft : (∑ z : Fin r → N, (if x = z ∘ σ then (1 : ℂ) else 0) *
      tensorPowerMatrix r A z y) = tensorPowerMatrix r A (x ∘ σ.symm) y := by
    rw [Finset.sum_eq_single (x ∘ σ.symm)]
    · simp [Function.comp_def]
    · intro z _ hz
      have hxz : x ≠ z ∘ σ := by
        intro h
        apply hz
        funext t
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (σ.symm t) |>.symm
      simp [hxz]
    · simp
  have hright : (∑ z : Fin r → N, tensorPowerMatrix r A x z *
      (if z = y ∘ σ then (1 : ℂ) else 0)) = tensorPowerMatrix r A x (y ∘ σ) := by
    simp
  rw [hleft, hright]
  unfold tensorPowerMatrix
  exact Fintype.prod_equiv σ.symm (fun t => A ((x ∘ σ.symm) t) (y t))
    (fun t => A (x t) ((y ∘ σ) t)) (fun t => by simp)

omit [Fintype N] [DecidableEq N] in
lemma word_eq_permute_of_cover {r : ℕ} (e x : Fin r → N)
    (he : Function.Injective e) (hcover : ∀ t, ∃ i, x i = e t) :
    ∃ σ : Equiv.Perm (Fin r), x = e ∘ σ := by
  classical
  choose f hf using hcover
  have hfi : Function.Injective f := by
    intro i j hij
    apply he
    rw [← hf i, ← hf j, hij]
  let τ : Equiv.Perm (Fin r) := Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  refine ⟨τ.symm, ?_⟩
  funext t
  have ht := hf (τ.symm t)
  change x (τ (τ.symm t)) = e (τ.symm t) at ht
  simpa only [Equiv.apply_symm_apply, Function.comp_apply] using ht

/-- The distinguished injective column of a tensor-power intertwiner can
only contain permutations of that word. Zero-one diagonal projectors suffice. -/
lemma tensorPower_commutant_reference_column {r : ℕ}
    (e : Fin r → N) (he : Function.Injective e)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ A : Matrix N N ℂ, Commute T (tensorPowerMatrix r A))
    (x : Fin r → N) (hx : ¬∃ σ : Equiv.Perm (Fin r), x = e ∘ σ) : T x e = 0 := by
  classical
  have hmissing : ∃ t, ∀ i, x i ≠ e t := by
    by_contra h
    push_neg at h
    exact hx (word_eq_permute_of_cover e x he h)
  obtain ⟨t, ht⟩ := hmissing
  let d : N → ℂ := fun z => if z = e t then 0 else 1
  have hz : (∏ i, d (e i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ t) (by simp [d])
  have ho : (∏ i, d (x i)) = 1 := by simp [d, ht]
  have hc := (hT (Matrix.diagonal d)).eq
  rw [tensorPowerMatrix_diagonal] at hc
  have hh := congrArg (fun Z : Matrix (Fin r → N) (Fin r → N) ℂ => Z x e) hc
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul, hz, ho, mul_zero, one_mul] using hh.symm

/-- A concrete matrix mapping each distinct reference basis vector to the
corresponding (possibly repeated) target basis vector. -/
noncomputable def tensorColumnSelector {r : ℕ} (e b : Fin r → N) : Matrix N N ℂ :=
  fun x y => Function.extend e (fun t => if x = b t then 1 else 0) (fun _ => 0) y

omit [Fintype N] in
lemma tensorColumnSelector_apply {r : ℕ} (e b : Fin r → N)
    (he : Function.Injective e) (x : N) (t : Fin r) :
    tensorColumnSelector e b x (e t) = if x = b t then 1 else 0 :=
  he.extend_apply _ _ _

omit [Fintype N] in
lemma tensorPowerMatrix_selector_permute {r : ℕ} (e b : Fin r → N)
    (he : Function.Injective e) (x : Fin r → N) (σ : Equiv.Perm (Fin r)) :
    tensorPowerMatrix r (tensorColumnSelector e b) x (e ∘ σ) =
      tensorPositionPermutation N σ x b := by
  simp only [tensorPowerMatrix, Function.comp_apply, tensorColumnSelector_apply e b he,
    tensorPositionPermutation]
  exact word_product_indicator r x (b ∘ σ)

/-- For dimension at least the tensor order, the full tensor-power commutant
is explicitly the span of tensor-position permutations. No invariant-spanning
hypothesis is assumed: the coefficients are entries of one injective column. -/
theorem tensorPower_commutant_eq_permutation_sum {r : ℕ}
    (e : Fin r → N) (he : Function.Injective e)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ A : Matrix N N ℂ, Commute T (tensorPowerMatrix r A)) :
    T = ∑ σ : Equiv.Perm (Fin r), T (e ∘ σ) e • tensorPositionPermutation N σ := by
  classical
  ext x b
  have hsel : ∀ z, tensorPowerMatrix r (tensorColumnSelector e b) z e =
      if z = b then 1 else 0 := by
    intro z
    simpa [tensorPositionPermutation] using
      tensorPowerMatrix_selector_permute e b he z (1 : Equiv.Perm (Fin r))
  have hc := congrArg (fun Z : Matrix (Fin r → N) (Fin r → N) ℂ => Z x e)
    (hT (tensorColumnSelector e b)).eq
  simp only [Matrix.mul_apply, hsel] at hc
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  rw [hc]
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin r) => e ∘ σ) := by
    intro σ τ hστ
    apply Equiv.ext
    intro i
    exact he (congrFun hστ i)
  rw [← Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin r) => e ∘ σ) hinj
    (fun σ => tensorPowerMatrix r (tensorColumnSelector e b) x (e ∘ σ) * T (e ∘ σ) e)
    (fun z => tensorPowerMatrix r (tensorColumnSelector e b) x z * T z e)
    (fun z hz => by
      dsimp only
      rw [tensorPower_commutant_reference_column e he T hT z (by
        intro ⟨σ, hσ⟩
        exact hz ⟨σ, hσ.symm⟩), mul_zero]) (fun _ => rfl)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorPowerMatrix_selector_permute e b he, mul_comm]

theorem tensorPower_commutant_mem_span {r : ℕ} (hcard : r ≤ Fintype.card N)
    (T : Matrix (Fin r → N) (Fin r → N) ℂ)
    (hT : ∀ A : Matrix N N ℂ, Commute T (tensorPowerMatrix r A)) :
    T ∈ Submodule.span ℂ (Set.range (tensorPositionPermutation N (r := r))) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := N)
    (by simpa using hcard)
  rw [tensorPower_commutant_eq_permutation_sum e e.injective T hT]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨σ, rfl⟩

end Fluctuations
