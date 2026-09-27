import Fluctuations.HaarTensorProjection
import Fluctuations.TensorPermutationTrace

/-! The actual Haar tensor average, with coefficients obtained from the
proved inverse of the permutation Gram matrix. -/

open scoped BigOperators Matrix

namespace Fluctuations

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The full Haar tensor integration formula. Invariant spanning, trace pairing,
and the Gram inverse are all proved, rather than assumed. -/
theorem globalHaarTensorMean_weingarten {r : ℕ}
    (hcard : r ≤ Fintype.card N) (hD : 1 ≤ (Fintype.card N : ℝ))
    (hlarge : 2 * (r.factorial : ℝ) ≤ Fintype.card N)
    (X : Matrix (Fin r → N) (Fin r → N) ℂ) :
    globalHaarRepresentationMean (tensorPowerRepresentation r) X =
      ∑ σ : Equiv.Perm (Fin r),
        (∑ τ : Equiv.Perm (Fin r),
          gramWeingartenCoefficient (Fintype.card N) r (σ⁻¹ * τ) *
            Matrix.trace ((tensorPositionPermutation N τ).conjTranspose * X)) •
          tensorPositionPermutation N σ := by
  classical
  let G : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℂ :=
    fun σ τ => (Fintype.card N : ℂ) ^ permutationTotalCycles (σ⁻¹ * τ)
  let V : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℂ :=
    fun σ τ => gramWeingartenCoefficient (Fintype.card N) r (σ⁻¹ * τ)
  have hGV : G * V = 1 := by
    ext σ τ
    simpa only [G, V, Matrix.mul_apply, Matrix.one_apply, Complex.ofReal_natCast] using
      gramWeingarten_inverse_identity hD r hlarge σ τ
  have hunit : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr
    (isUnit_of_mul_eq_one G.det V.det (by simpa using congrArg Matrix.det hGV))
  have hinv : G⁻¹ = V := Matrix.inv_eq_right_inv hGV
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := N)
    (by simpa using hcard)
  have hspan := globalHaarTensorMean_eq_permutation_sum e e.injective X
  have hp (σ : Equiv.Perm (Fin r)) :
      Matrix.trace ((tensorPositionPermutation N σ).conjTranspose *
        globalHaarRepresentationMean (tensorPowerRepresentation r) X) =
      Matrix.trace ((tensorPositionPermutation N σ).conjTranspose * X) := by
    apply globalHaarRepresentationMean_trace_pairing (tensorPowerRepresentation r)
      (tensorPowerRepresentation_continuous r) (tensorPowerRepresentation_unitary r)
    intro U
    change Commute (tensorPowerMatrix r U.val) (star (tensorPositionPermutation N σ))
    rw [tensorPositionPermutation_star]
    exact (tensorPositionPermutation_commute r σ⁻¹ U.val).symm
  have hh := matrix_expansion_of_gram (tensorPositionPermutation N) G
    (fun σ τ => (tensorPositionPermutation_gram σ τ).symm) hunit
    (globalHaarRepresentationMean (tensorPowerRepresentation r) X) X
    ⟨_, hspan⟩ hp
  simpa only [hinv, V] using hh

end Fluctuations
