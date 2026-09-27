import Fluctuations.CoordinateAverages

/-! Full second moments of an actual independently sampled linear gate evolution. -/

open MeasureTheory Filter
open scoped BigOperators

namespace Fluctuations

section OneStep

variable {G Ω Q : Type*} [Fintype Q]
  [TopologicalSpace G] [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {ν : Measure G} {μ : Measure Ω} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

/-- The exact full covariance update on an independent new-gate/old-circuit
product. Off-diagonal input moments are retained, including for a fixed gate. -/
theorem integral_independent_matrix_update
    (K : G → Matrix Q Q ℝ) (hK : Continuous K)
    (v : Ω → Q → ℝ) (hv : Continuous v) (i j : Q) :
    (∫ p : G × Ω, (K p.1).mulVec (v p.2) i * (K p.1).mulVec (v p.2) j ∂ν.prod μ) =
      ∑ a : Q, ∑ b : Q, (∫ g, K g i a * K g j b ∂ν) *
        (∫ x, v x a * v x b ∂μ) := by
  have heq (p : G × Ω) : (K p.1).mulVec (v p.2) i * (K p.1).mulVec (v p.2) j =
      ∑ a : Q, ∑ b : Q, (K p.1 i a * K p.1 j b) * (v p.2 a * v p.2 b) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [heq]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro b _
      exact integral_prod_mul (fun g => K g i a * K g j b) (fun x => v x a * v x b)
    · intro b _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
  · intro a _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop

end OneStep

section FiniteEvolution

variable {G Q : Type*} [Fintype Q]
  [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [IsProbabilityMeasure ν]

/-- Actual coefficient evolution driven by a finite list of independent gate
samples. Coordinate `t` is the gate used at time `t`. -/
def randomLinearEvolution (K : ℕ → G → Matrix Q Q ℝ) (v₀ : Q → ℝ) :
    (n : ℕ) → (Fin n → G) → Q → ℝ
  | 0, _ => v₀
  | n + 1, x => (K n (x (Fin.last n))).mulVec
      (randomLinearEvolution K v₀ n (fun a => x a.castSucc))

omit [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
lemma randomLinearEvolution_snoc (K : ℕ → G → Matrix Q Q ℝ) (v₀ : Q → ℝ)
    (n : ℕ) (x : Fin n → G) (g : G) :
    randomLinearEvolution K v₀ (n + 1) (Fin.snoc x g) =
      (K n g).mulVec (randomLinearEvolution K v₀ n x) := by
  simp [randomLinearEvolution]

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
lemma randomLinearEvolution_continuous (K : ℕ → G → Matrix Q Q ℝ)
    (hK : ∀ t, Continuous (K t)) (v₀ : Q → ℝ) (n : ℕ) :
    Continuous (randomLinearEvolution K v₀ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun x : Fin (n + 1) → G =>
      (K n (x (Fin.last n))).mulVec (randomLinearEvolution K v₀ n (fun a => x a.castSucc)))
    apply continuous_pi
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

/-- The actual single-gate second-moment matrix, keeping all input/output pairs. -/
noncomputable def gateSecondMoment (K : G → Matrix Q Q ℝ) :
    Matrix (Q × Q) (Q × Q) ℝ :=
  fun ij ab => ∫ g, K g ij.1 ab.1 * K g ij.2 ab.2 ∂ν

/-- Deterministic evolution of the full second-moment matrix. -/
noncomputable def fullSecondMomentEvolution (K : ℕ → G → Matrix Q Q ℝ) (v₀ : Q → ℝ) :
    ℕ → Matrix Q Q ℝ
  | 0 => fun i j => v₀ i * v₀ j
  | n + 1 => fun i j => ∑ a : Q, ∑ b : Q,
      gateSecondMoment ν (K n) (i, j) (a, b) * fullSecondMomentEvolution K v₀ n a b

/-- Every matrix entry of the true product-space second moment satisfies the
full local-moment recurrence. No diagonal covariance or Markov hypothesis is needed. -/
theorem integral_randomLinearEvolution_mul
    (K : ℕ → G → Matrix Q Q ℝ) (hK : ∀ t, Continuous (K t))
    (v₀ : Q → ℝ) (n : ℕ) (i j : Q) :
    (∫ x : Fin n → G, randomLinearEvolution K v₀ n x i *
      randomLinearEvolution K v₀ n x j ∂Measure.pi (fun _ => ν)) =
      fullSecondMomentEvolution ν K v₀ n i j := by
  induction n generalizing i j with
  | zero => simp [randomLinearEvolution, fullSecondMomentEvolution]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) (Fin.last n)
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)).symm e
    calc
      _ = ∫ p : G × (Fin n → G), (K n p.1).mulVec (randomLinearEvolution K v₀ n p.2) i *
          (K n p.1).mulVec (randomLinearEvolution K v₀ n p.2) j
          ∂ν.prod (Measure.pi (fun _ => ν)) := by
        rw [← hp.integral_comp']
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          rcases p with ⟨g, x⟩
          simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv, randomLinearEvolution_snoc]
      _ = ∑ a : Q, ∑ b : Q, (∫ g, K n g i a * K n g j b ∂ν) *
          (∫ x : Fin n → G, randomLinearEvolution K v₀ n x a * randomLinearEvolution K v₀ n x b
            ∂Measure.pi (fun _ => ν)) :=
        integral_independent_matrix_update (K n) (hK n) (randomLinearEvolution K v₀ n)
          (randomLinearEvolution_continuous K hK v₀ n) i j
      _ = fullSecondMomentEvolution ν K v₀ (n + 1) i j := by
        simp only [fullSecondMomentEvolution, gateSecondMoment]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [ih]

/-- The ordinary diagonal probability-weight recurrence. -/
def markovWeightEvolution (P : ℕ → Matrix Q Q ℝ) (w₀ : Q → ℝ) : ℕ → Q → ℝ
  | 0 => w₀
  | n + 1 => (P n).mulVec (markovWeightEvolution P w₀ n)

omit [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [BorelSpace G] [IsProbabilityMeasure ν] in
/-- Diagonal local column covariance makes the full covariance recurrence
exactly the Pauli-weight Markov recurrence. The local covariance premise is
an explicit integral identity for the actual matrices, to be supplied by the
separate Haar calculation. -/
theorem fullSecondMomentEvolution_diagonal [DecidableEq Q]
    (K : ℕ → G → Matrix Q Q ℝ) (P : ℕ → Matrix Q Q ℝ) (v₀ w₀ : Q → ℝ)
    (hinit : ∀ i j, v₀ i * v₀ j = if i = j then w₀ i else 0)
    (hlocal : ∀ t i j a, gateSecondMoment ν (K t) (i, j) (a, a) =
      if i = j then P t i a else 0) (n : ℕ) (i j : Q) :
    fullSecondMomentEvolution ν K v₀ n i j =
      if i = j then markovWeightEvolution P w₀ n i else 0 := by
  classical
  induction n generalizing i j with
  | zero => exact hinit i j
  | succ n ih =>
    simp only [fullSecondMomentEvolution]
    simp_rw [ih, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp_rw [hlocal]
    by_cases hij : i = j
    · subst j
      simp [markovWeightEvolution, Matrix.mulVec, dotProduct]
    · simp [hij]

/-- True independent-product second moments reduce to Markov weights under
the proved local diagonal-covariance identity. -/
theorem integral_randomLinearEvolution_diagonal [DecidableEq Q]
    (K : ℕ → G → Matrix Q Q ℝ) (hK : ∀ t, Continuous (K t))
    (P : ℕ → Matrix Q Q ℝ) (v₀ w₀ : Q → ℝ)
    (hinit : ∀ i j, v₀ i * v₀ j = if i = j then w₀ i else 0)
    (hlocal : ∀ t i j a, gateSecondMoment ν (K t) (i, j) (a, a) =
      if i = j then P t i a else 0) (n : ℕ) (i j : Q) :
    (∫ x : Fin n → G, randomLinearEvolution K v₀ n x i *
      randomLinearEvolution K v₀ n x j ∂Measure.pi (fun _ => ν)) =
      if i = j then markovWeightEvolution P w₀ n i else 0 := by
  rw [integral_randomLinearEvolution_mul ν K hK,
    fullSecondMomentEvolution_diagonal ν K P v₀ w₀ hinit hlocal]

/-- Replace one gate by a fixed value while retaining the real sampled matrix
at every other coordinate. -/
def freezeGateKernel (K : ℕ → G → Matrix Q Q ℝ) (t : ℕ) (g : G) :
    ℕ → G → Matrix Q Q ℝ := fun u x => if u = t then K u g else K u x

omit [Fintype Q] [CompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
lemma freezeGateKernel_continuous (K : ℕ → G → Matrix Q Q ℝ)
    (hK : ∀ u, Continuous (K u)) (t : ℕ) (g : G) (u : ℕ) :
    Continuous (freezeGateKernel K t g u) := by
  unfold freezeGateKernel
  split_ifs
  · exact continuous_const
  · exact hK u

omit [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
lemma randomLinearEvolution_freeze (K : ℕ → G → Matrix Q Q ℝ) (v₀ : Q → ℝ)
    (t : ℕ) (g : G) (n : ℕ) (x : Fin n → G) :
    randomLinearEvolution (freezeGateKernel K t g) v₀ n x =
      randomLinearEvolution K v₀ n (fun i => if i.val = t then g else x i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [randomLinearEvolution, freezeGateKernel, Fin.val_last]
    rw [ih]
    by_cases h : n = t <;> simp [h]

omit [TopologicalSpace G] [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
lemma randomLinearEvolution_freeze_eq_update
    (K : ℕ → G → Matrix Q Q ℝ) (v₀ : Q → ℝ) (n : ℕ)
    (t : Fin n) (g : G) (x : Fin n → G) :
    randomLinearEvolution (freezeGateKernel K t.val g) v₀ n x =
      randomLinearEvolution K v₀ n (Function.update x t g) := by
  rw [randomLinearEvolution_freeze]
  congr 1
  funext i
  by_cases hi : i = t
  · subst i
    simp
  · have hv : i.val ≠ t.val := fun h => hi (Fin.ext h)
    simp [hi, hv, Function.update_of_ne]

/-- The full covariance with one physical gate fixed is obtained by freezing
that gate's matrix in the recurrence. This is an identity for the actual
integral over all other gates, not a conditional-moment assumption. -/
theorem coordinateAverage_randomLinearEvolution_mul
    (K : ℕ → G → Matrix Q Q ℝ) (hK : ∀ u, Continuous (K u))
    (v₀ : Q → ℝ) (n : ℕ) (t : Fin n) (g : G) (i j : Q) :
    coordinateAverage (fun _ : Fin n => ν) t
      (fun x => ((randomLinearEvolution K v₀ n x i * randomLinearEvolution K v₀ n x j : ℝ) : ℂ)) g =
      (fullSecondMomentEvolution ν (freezeGateKernel K t.val g) v₀ n i j : ℂ) := by
  rw [coordinateAverage_eq_integral_update]
  simp_rw [← randomLinearEvolution_freeze_eq_update K v₀ n t g]
  rw [integral_complex_ofReal, integral_randomLinearEvolution_mul ν
    (freezeGateKernel K t.val g) (freezeGateKernel_continuous K hK t.val g)]

/-- A general quadratic coefficient observable, allowing arbitrary complex
state-dependent matrix-trace weights. -/
noncomputable def quadraticCoefficientObservable (H : Matrix Q Q ℂ) (v : Q → ℝ) : ℂ :=
  ∑ i : Q, ∑ j : Q, H i j * ((v i * v j : ℝ) : ℂ)

/-- Actual Haar/product averaging of any quadratic observable is determined
by the full second-moment recurrence. -/
theorem integral_randomLinearEvolution_quadratic
    (K : ℕ → G → Matrix Q Q ℝ) (hK : ∀ u, Continuous (K u))
    (v₀ : Q → ℝ) (n : ℕ) (H : Matrix Q Q ℂ) :
    (∫ x : Fin n → G, quadraticCoefficientObservable H (randomLinearEvolution K v₀ n x)
      ∂Measure.pi (fun _ => ν)) =
      ∑ i : Q, ∑ j : Q, H i j * (fullSecondMomentEvolution ν K v₀ n i j : ℂ) := by
  have hc := randomLinearEvolution_continuous K hK v₀ n
  unfold quadraticCoefficientObservable
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_complex_ofReal,
        integral_randomLinearEvolution_mul ν K hK v₀ n i j]
    · intro j _
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop

/-- Exact conditional mean of a quadratic observable with one gate held
fixed, expressed using the proved full second-moment recurrence. -/
theorem coordinateAverage_randomLinearEvolution_quadratic
    (K : ℕ → G → Matrix Q Q ℝ) (hK : ∀ u, Continuous (K u))
    (v₀ : Q → ℝ) (n : ℕ) (t : Fin n) (g : G) (H : Matrix Q Q ℂ) :
    coordinateAverage (fun _ : Fin n => ν) t
      (fun x => quadraticCoefficientObservable H (randomLinearEvolution K v₀ n x)) g =
      ∑ i : Q, ∑ j : Q, H i j *
        (fullSecondMomentEvolution ν (freezeGateKernel K t.val g) v₀ n i j : ℂ) := by
  rw [coordinateAverage_eq_integral_update]
  simp_rw [← randomLinearEvolution_freeze_eq_update K v₀ n t g]
  exact integral_randomLinearEvolution_quadratic ν (freezeGateKernel K t.val g)
    (freezeGateKernel_continuous K hK t.val g) v₀ n H

end FiniteEvolution

end Fluctuations
