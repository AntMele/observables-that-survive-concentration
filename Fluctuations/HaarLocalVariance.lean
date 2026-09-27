import Fluctuations.HaarSU4
import Fluctuations.FiniteDimensionalVariance
import Fluctuations.LocalPolynomial
import Fluctuations.ProductVariance

open MeasureTheory
open scoped ENNReal

namespace Fluctuations

/-- A uniform local reverse-variance constant for all degree-`D` functions in
the raw gate entries and their conjugates. The constant depends only on the
number of local gates and their degree, not on any polynomial coefficients. -/
theorem haar_polynomial_reverseVariance (m D : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ f : C(SU4Block m, ℂ),
      f ∈ polynomialFeatureSpace (rawSU4Features m) D →
      η * ‖(∫ x, f x ∂su4Haar m) - f 1‖ ^ 2 ≤ complexVariance (su4Haar m) f := by
  obtain ⟨η, hη, hbound⟩ := finiteDimensional_reverseVariance (su4Haar m)
    (polynomialFeatureSpace (rawSU4Features m) D) (1 : SU4Block m)
  exact ⟨η, hη, fun f hf => hbound ⟨f, hf⟩⟩


/-- A positive constant chosen solely from the number of local gates and OTOC
order. In particular, it does not depend on the Hilbert-space dimension,
embeddings, state, observables, or spectator circuit. -/
noncomputable def haarLocalConstant (m k : ℕ) : ℝ :=
  Classical.choose (haar_polynomial_reverseVariance m ((m + m) * (2 * k)))

lemma haarLocalConstant_pos (m k : ℕ) : 0 < haarLocalConstant m k :=
  (Classical.choose_spec (haar_polynomial_reverseVariance m ((m + m) * (2 * k)))).1

lemma haarLocalConstant_bound (m k : ℕ) (f : C(SU4Block m, ℂ))
    (hf : f ∈ polynomialFeatureSpace (rawSU4Features m) ((m + m) * (2 * k))) :
    haarLocalConstant m k * ‖(∫ x, f x ∂su4Haar m) - f 1‖ ^ 2 ≤
      complexVariance (su4Haar m) f :=
  (Classical.choose_spec (haar_polynomial_reverseVariance m ((m + m) * (2 * k)))).2 f hf

section EmbeddedGates

variable {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- Actual Haar gate coordinates embedded linearly in any finite ambient matrix
space. Tensoring with an identity and placing a gate on a pair of sites are
examples of these linear maps. -/
noncomputable def haarGateMatrix
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (g : Fin m) : Matrix N N C(SU4Block m, ℂ) :=
  linearFeatureMatrix (su4CoordinateMatrix m g) (E g)

omit [Fintype N] [DecidableEq N] in
lemma haarGateMatrix_apply
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (g : Fin m) (x : SU4Block m) (i j : N) :
    haarGateMatrix E g i j x = E g (x g).val i j := by
  exact linearFeatureMatrix_apply (su4CoordinateMatrix m g) (E g) x i j

omit [Fintype N] [DecidableEq N] in
lemma haarGateMatrix_entry_mem
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (g : Fin m) (i j : N) :
    haarGateMatrix E g i j ∈ Submodule.span ℂ (Set.range (rawSU4Features m)) := by
  unfold haarGateMatrix linearFeatureMatrix
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (su4CoordinateMatrix_entry_mem m g a b)

/-- The concrete ordered product of the embedded Haar gates. -/
noncomputable def haarBlockMatrix
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (x : SU4Block m) : Matrix N N ℂ :=
  (List.ofFn fun g => E g (x g).val).prod

lemma haarBlockMatrix_one
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) : haarBlockMatrix E 1 = 1 := by
  simp [haarBlockMatrix, hE]

/-- The local conditional OTOC, as its actual matrix trace formula. -/
noncomputable def haarLocalOTOC
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) : C(SU4Block m, ℂ) :=
  matrixBlockOTOC (haarGateMatrix E) ρ B V M k

lemma haarLocalOTOC_apply
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) (x : SU4Block m) :
    haarLocalOTOC E ρ B V M k x =
      Matrix.trace (ρ * (V.conjTranspose *
        ((haarBlockMatrix E x).conjTranspose * B * haarBlockMatrix E x) *
        V * M) ^ (2 * k)) := by
  have heq : (fun g => matrixEval x (haarGateMatrix E g)) =
      (fun g => E g (x g).val) := by
    funext g
    ext i j
    exact haarGateMatrix_apply E g x i j
  simpa only [haarLocalOTOC, heq, haarBlockMatrix] using
    matrixBlockOTOC_apply (haarGateMatrix E) ρ B V M k x

lemma haarBlockMatrix_continuous
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ) :
    Continuous (haarBlockMatrix E) := by
  have heq : haarBlockMatrix E = fun x => matrixEval x (matrixGateBlock (haarGateMatrix E)) := by
    funext x
    rw [matrixEval_matrixGateBlock]
    unfold haarBlockMatrix
    congr 2
    funext g
    ext i j
    exact (haarGateMatrix_apply E g x i j).symm
  rw [heq]
  exact continuous_pi fun i => continuous_pi fun j =>
    (matrixGateBlock (haarGateMatrix E) i j).continuous

lemma haarLocalOTOC_one
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    haarLocalOTOC E ρ B V M k 1 =
      Matrix.trace (ρ * (V.conjTranspose * B * V * M) ^ (2 * k)) := by
  rw [haarLocalOTOC_apply, haarBlockMatrix_one E hE]
  simp

lemma haarLocalOTOC_mem
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    haarLocalOTOC E ρ B V M k ∈
      polynomialFeatureSpace (rawSU4Features m) ((m + m) * (2 * k)) := by
  exact matrixBlockOTOC_mem (rawSU4Features m)
    (fun p => (p.1, p.2.1, p.2.2.1, !p.2.2.2))
    (star_rawSU4Features m) (haarGateMatrix E) (haarGateMatrix_entry_mem E)
    ρ B V M k

/-- The local Haar reverse-variance condition is a theorem, uniformly in all
ambient matrices and all embeddings. No reverse-variance premise is assumed. -/
theorem haarLocalOTOC_reverseVariance
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    haarLocalConstant m k *
      ‖(∫ x, haarLocalOTOC E ρ B V M k x ∂su4Haar m) -
        haarLocalOTOC E ρ B V M k 1‖ ^ 2 ≤
      complexVariance (su4Haar m) (haarLocalOTOC E ρ B V M k) :=
  haarLocalConstant_bound m k _ (haarLocalOTOC_mem E ρ B V M k)

/-- The same local theorem with the no-new-gate value written explicitly.
Unitality of the embeddings is the only requirement for this identification. -/
theorem haarLocalOTOC_reverseVariance_identity
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) (ρ B V M : Matrix N N ℂ) (k : ℕ) :
    haarLocalConstant m k *
      ‖(∫ x, haarLocalOTOC E ρ B V M k x ∂su4Haar m) -
        Matrix.trace (ρ * (V.conjTranspose * B * V * M) ^ (2 * k))‖ ^ 2 ≤
      complexVariance (su4Haar m) (haarLocalOTOC E ρ B V M k) := by
  simpa only [haarLocalOTOC_one E hE] using haarLocalOTOC_reverseVariance E ρ B V M k

end EmbeddedGates

section Conditional

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [SecondCountableTopology X] [mX : MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {m : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

omit [CompactSpace X] [T2Space X] [SecondCountableTopology X] mX [BorelSpace X] in
/-- Joint continuity when the already-built circuit varies continuously. -/
lemma haarLocalOTOC_joint_continuous
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (V : X → Matrix N N ℂ) (hV : Continuous V) (k : ℕ) :
    Continuous (fun p : X × SU4Block m => haarLocalOTOC E ρ B (V p.1) M k p.2) := by
  simp_rw [haarLocalOTOC_apply]
  have hVp := hV.comp (continuous_fst : Continuous (Prod.fst : X × SU4Block m → X))
  have hWp := (haarBlockMatrix_continuous E).comp
    (continuous_snd : Continuous (Prod.snd : X × SU4Block m → SU4Block m))
  exact (continuous_const.mul
    ((((hVp.matrix_conjTranspose.mul
      ((hWp.matrix_conjTranspose.mul continuous_const).mul hWp)).mul hVp).mul
        continuous_const).pow (2 * k))).matrix_trace

/-- The genuine conditional local reverse-variance assumption for an
independent Haar gate block is discharged from the matrix OTOC formula. -/
theorem haarLocalOTOC_conditional_reverseVariance
    (E : Fin m → Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix N N ℂ)
    (hE : ∀ g, E g 1 = 1) (ρ B M : Matrix N N ℂ)
    (V : X → Matrix N N ℂ) (hV : Continuous V) (k : ℕ) :
    LocalReverseVariance (μ.prod (su4Haar m)) (mX.comap Prod.fst)
      (haarLocalConstant m k)
      (fun p : X × SU4Block m =>
        Matrix.trace (ρ * ((V p.1).conjTranspose * B * V p.1 * M) ^ (2 * k)))
      (fun p : X × SU4Block m => haarLocalOTOC E ρ B (V p.1) M k p.2) := by
  have hh := product_localReverseVariance (μ := μ) (ν := su4Haar m)
    (fun p : X × SU4Block m => haarLocalOTOC E ρ B (V p.1) M k p.2)
    (haarLocalOTOC_joint_continuous E ρ B M V hV k) (1 : SU4Block m)
    (haarLocalConstant m k)
    (fun x => haarLocalOTOC_reverseVariance E ρ B (V x) M k)
  simpa only [haarLocalOTOC_one E hE] using hh

end Conditional

end Fluctuations
