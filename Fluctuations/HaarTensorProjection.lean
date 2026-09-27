import Fluctuations.GlobalHaarMean
import Fluctuations.HaarTensorInvariants
import Fluctuations.TensorUnitaryExtension

/-! Haar averaging in a continuous unitary matrix representation. -/

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace Fluctuations

variable {N W : Type*} [Fintype N] [DecidableEq N] [Fintype W] [DecidableEq W]

/-- Actual Haar conjugation average in a matrix representation. -/
noncomputable def globalHaarRepresentationMean
    (R : GlobalUnitary N →* Matrix W W ℂ) (X : Matrix W W ℂ) : Matrix W W ℂ :=
  ∫ U, (R U).conjTranspose * X * R U ∂globalHaar N

lemma globalHaarRepresentationMean_integrable
    (R : GlobalUnitary N →* Matrix W W ℂ) (hR : Continuous R) (X : Matrix W W ℂ) :
    Integrable (fun U => (R U).conjTranspose * X * R U) (globalHaar N) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

/-- Haar averaging is fixed by conjugation in the representation. -/
theorem globalHaarRepresentationMean_conjugation
    (R : GlobalUnitary N →* Matrix W W ℂ) (hR : Continuous R)
    (X : Matrix W W ℂ) (S : GlobalUnitary N) :
    (R S).conjTranspose * globalHaarRepresentationMean R X * R S =
      globalHaarRepresentationMean R X := by
  have hi := (matrixSandwichCLM (R S).conjTranspose (R S)).integral_comp_comm
    (globalHaarRepresentationMean_integrable R hR X)
  calc
    (R S).conjTranspose * globalHaarRepresentationMean R X * R S =
        ∫ U, (R S).conjTranspose * ((R U).conjTranspose * X * R U) * R S ∂globalHaar N := hi.symm
    _ = ∫ U, (R (U * S)).conjTranspose * X * R (U * S) ∂globalHaar N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => by
        simp only [map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = globalHaarRepresentationMean R X :=
      integral_mul_right_eq_self (fun U => (R U).conjTranspose * X * R U) S

/-- The actual Haar representation average belongs to the unitary commutant. -/
theorem globalHaarRepresentationMean_commute
    (R : GlobalUnitary N →* Matrix W W ℂ) (hR : Continuous R)
    (hunitary : ∀ U, R U ∈ Matrix.unitaryGroup W ℂ)
    (X : Matrix W W ℂ) (S : GlobalUnitary N) :
    Commute (R S) (globalHaarRepresentationMean R X) := by
  have h := congrArg (fun Y : Matrix W W ℂ => R S * Y)
    (globalHaarRepresentationMean_conjugation R hR X S)
  have hSS : R S * (R S).conjTranspose = 1 := (hunitary S).2
  simpa only [← Matrix.mul_assoc, hSS, Matrix.one_mul] using h.symm

/-- Trace pairing with a commuting test operator is preserved by the actual
Haar average. This determines projection coefficients once the commutant is known. -/
theorem globalHaarRepresentationMean_trace_pairing
    (R : GlobalUnitary N →* Matrix W W ℂ) (hR : Continuous R)
    (hunitary : ∀ U, R U ∈ Matrix.unitaryGroup W ℂ)
    (X Q : Matrix W W ℂ) (hQ : ∀ U, Commute (R U) Q) :
    Matrix.trace (Q * globalHaarRepresentationMean R X) = Matrix.trace (Q * X) := by
  have hi := (stateTraceCLM Q).integral_comp_comm
    (globalHaarRepresentationMean_integrable R hR X)
  have htrace (U : GlobalUnitary N) :
      Matrix.trace (Q * ((R U).conjTranspose * X * R U)) = Matrix.trace (Q * X) := by
    have hcontract : R U * Q * (R U).conjTranspose = Q := by
      rw [(hQ U).eq, Matrix.mul_assoc]
      have hUU : R U * (R U).conjTranspose = 1 := (hunitary U).2
      rw [hUU, Matrix.mul_one]
    calc
      Matrix.trace (Q * ((R U).conjTranspose * X * R U)) =
          Matrix.trace (R U * Q * (R U).conjTranspose * X) := by
        simpa only [Matrix.mul_assoc] using
          Matrix.trace_mul_comm (Q * (R U).conjTranspose * X) (R U)
      _ = Matrix.trace (Q * X) := by rw [hcontract]
  change (∫ U, Matrix.trace (Q * ((R U).conjTranspose * X * R U)) ∂globalHaar N) =
    Matrix.trace (Q * globalHaarRepresentationMean R X) at hi
  rw [← hi]
  simp_rw [htrace]
  simp

/-- Averaging acts as identity on the commutant. -/
theorem globalHaarRepresentationMean_eq_self
    (R : GlobalUnitary N →* Matrix W W ℂ)
    (hunitary : ∀ U, R U ∈ Matrix.unitaryGroup W ℂ)
    (X : Matrix W W ℂ) (hX : ∀ U, Commute (R U) X) :
    globalHaarRepresentationMean R X = X := by
  unfold globalHaarRepresentationMean
  have hp (U : GlobalUnitary N) : (R U).conjTranspose * X * R U = X :=
    unitary_conjugation_eq_self_of_commute (R U) X (hunitary U) (hX U)
  simp_rw [hp]
  simp

/-- The actual tensor-power representation of the global unitary group. -/
def tensorPowerRepresentation (r : ℕ) :
    GlobalUnitary N →* Matrix (Fin r → N) (Fin r → N) ℂ where
  toFun U := tensorPowerMatrix r U.val
  map_one' := tensorPowerMatrix_one r
  map_mul' U V := tensorPowerMatrix_mul r U.val V.val

lemma tensorPowerRepresentation_continuous (r : ℕ) :
    Continuous (tensorPowerRepresentation (N := N) r) := by
  exact (tensorPowerMatrix_continuous r).comp continuous_subtype_val

lemma tensorPowerRepresentation_unitary (r : ℕ) (U : GlobalUnitary N) :
    tensorPowerRepresentation r U ∈ Matrix.unitaryGroup (Fin r → N) ℂ := by
  constructor
  · change star (tensorPowerMatrix r U.val) * tensorPowerMatrix r U.val = 1
    rw [← tensorPowerMatrix_star, ← tensorPowerMatrix_mul, U.prop.1, tensorPowerMatrix_one]
  · change tensorPowerMatrix r U.val * star (tensorPowerMatrix r U.val) = 1
    rw [← tensorPowerMatrix_star, ← tensorPowerMatrix_mul, U.prop.2, tensorPowerMatrix_one]

lemma tensorPowerRepresentation_conjugate (r : ℕ) (B : Matrix N N ℂ)
    (U : GlobalUnitary N) :
    (tensorPowerRepresentation r U).conjTranspose * tensorPowerMatrix r B *
      tensorPowerRepresentation r U = tensorPowerMatrix r (U.val.conjTranspose * B * U.val) := by
  change star (tensorPowerMatrix r U.val) * tensorPowerMatrix r B * tensorPowerMatrix r U.val = _
  rw [← tensorPowerMatrix_star, ← tensorPowerMatrix_mul, ← tensorPowerMatrix_mul]
  rfl

/-- The genuine Haar tensor average is a sum of position permutations. The
invariant-space spanning theorem is proved, not supplied as a hypothesis. -/
theorem globalHaarTensorMean_eq_permutation_sum {r : ℕ}
    (e : Fin r → N) (he : Function.Injective e)
    (X : Matrix (Fin r → N) (Fin r → N) ℂ) :
    globalHaarRepresentationMean (tensorPowerRepresentation r) X =
      ∑ σ : Equiv.Perm (Fin r),
        globalHaarRepresentationMean (tensorPowerRepresentation r) X (e ∘ σ) e •
          tensorPositionPermutation N σ := by
  apply tensorPower_unitary_commutant_eq_permutation_sum e he
  intro U
  exact (globalHaarRepresentationMean_commute (tensorPowerRepresentation r)
    (tensorPowerRepresentation_continuous r) (tensorPowerRepresentation_unitary r) X U).symm

theorem globalHaarTensorMean_mem_span {r : ℕ} (hcard : r ≤ Fintype.card N)
    (X : Matrix (Fin r → N) (Fin r → N) ℂ) :
    globalHaarRepresentationMean (tensorPowerRepresentation r) X ∈
      Submodule.span ℂ (Set.range (tensorPositionPermutation N (r := r))) := by
  apply tensorPower_unitary_commutant_mem_span hcard
  intro U
  exact (globalHaarRepresentationMean_commute (tensorPowerRepresentation r)
    (tensorPowerRepresentation_continuous r) (tensorPowerRepresentation_unitary r) X U).symm

omit [DecidableEq W] in
/-- Gram inversion determines the matrix expansion of a trace-pairing projection.
This algebraic identity is used after the invariant subspace has been proved. -/
theorem matrix_expansion_of_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Matrix W W ℂ) (G : Matrix ι ι ℂ)
    (hG : ∀ i j, G i j = Matrix.trace ((P i).conjTranspose * P j))
    (hunit : IsUnit G) (T X : Matrix W W ℂ)
    (hspan : ∃ c : ι → ℂ, T = ∑ j, c j • P j)
    (hpair : ∀ i, Matrix.trace ((P i).conjTranspose * T) =
      Matrix.trace ((P i).conjTranspose * X)) :
    T = ∑ i, (∑ j, G⁻¹ i j * Matrix.trace ((P j).conjTranspose * X)) • P i := by
  obtain ⟨c, hc⟩ := hspan
  have hv : G.mulVec c = fun i => Matrix.trace ((P i).conjTranspose * X) := by
    funext i
    rw [← hpair i, hc]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, hG, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdet := (Matrix.isUnit_iff_isUnit_det G).mp hunit
  have hinv := congrArg (fun v => G⁻¹.mulVec v) hv
  dsimp only at hinv
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hdet, Matrix.one_mulVec] at hinv
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun hinv i]
  rfl

end Fluctuations
