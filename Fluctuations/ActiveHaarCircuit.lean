import Fluctuations.HaarCircuit
import Fluctuations.SpatialSupport
import Fluctuations.MeanChange

/-!
# Haar layers with an active patch and arbitrarily many inactive gates

Every layer samples `m` active and `q` inactive Haar SU(4) gates independently.
The layer is written `inactive * active`. Commutation with `B` removes the
inactive block from that layer's Heisenberg conjugation, but those gates remain
in the circuit history and can affect later layers. The local constant depends
only on `m,k`, not on `q` or on the global matrix dimension.

The algebraic commutation certificate is explicit. This file does not construct
a lattice, identify a graph light cone, or prove its gate-count bound.
-/

open MeasureTheory

namespace Fluctuations

/-- The two independently sampled parts of a full layer. -/
abbrev ActiveHaarLayer (m q : ℕ) := SU4Block m × SU4Block q

/-- Full-layer sampling retains the inactive gates as independent random data. -/
noncomputable def activeHaarLayerMeasure (m q : ℕ) : Measure (ActiveHaarLayer m q) :=
  (su4Haar m).prod (su4Haar q)

instance activeHaarLayerMeasure_probability (m q : ℕ) :
    IsProbabilityMeasure (activeHaarLayerMeasure m q) :=
  inferInstanceAs (IsProbabilityMeasure ((su4Haar m).prod (su4Haar q)))

section Circuit

variable {N : Type*} [Fintype N] [DecidableEq N] {m q : ℕ}

/-- All gates, including inactive ones, enter the physical circuit matrix. -/
noncomputable def activeHaarCircuitMatrix
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ) :
    (d : ℕ) → GateHistory (ActiveHaarLayer m q) d → Matrix N N ℂ
  | 0, _ => 1
  | d + 1, p =>
    (haarBlockMatrix (fun i => (I d i).toAlgHom.toLinearMap) p.2.2 *
      haarBlockMatrix (fun i => (A d i).toAlgHom.toLinearMap) p.2.1) *
        activeHaarCircuitMatrix A I d p.1

lemma activeHaarCircuitMatrix_continuous
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (d : ℕ) : Continuous (activeHaarCircuitMatrix A I d) := by
  induction d with
  | zero => exact continuous_const
  | succ d ih =>
    exact (((haarBlockMatrix_continuous _).comp (continuous_snd.comp continuous_snd)).mul
      ((haarBlockMatrix_continuous _).comp (continuous_fst.comp continuous_snd))).mul
      (ih.comp continuous_fst)

/-- The complete circuit is unitary, including every inactive gate. -/
lemma activeHaarCircuitMatrix_mem_unitary
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (d : ℕ) (x : GateHistory (ActiveHaarLayer m q) d) :
    activeHaarCircuitMatrix A I d x ∈ Matrix.unitaryGroup N ℂ := by
  induction d with
  | zero => exact (Matrix.unitaryGroup N ℂ).one_mem
  | succ d ih =>
    exact (Matrix.unitaryGroup N ℂ).mul_mem
      ((Matrix.unitaryGroup N ℂ).mul_mem
        (haarBlockMatrix_mem_unitary (I d) x.2.2)
        (haarBlockMatrix_mem_unitary (A d) x.2.1)) (ih x.1)

/-- The actual OTOC of the full circuit, not of a circuit with inactive gates deleted. -/
noncomputable def activeHaarCircuitOTOC
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ) :
    C(GateHistory (ActiveHaarLayer m q) d, ℂ) where
  toFun x := Matrix.trace
    (ρ * ((activeHaarCircuitMatrix A I d x).conjTranspose * B *
      activeHaarCircuitMatrix A I d x * M) ^ (2 * k))
  continuous_toFun := by
    have hc := activeHaarCircuitMatrix_continuous A I d
    fun_prop

lemma activeHaarCircuitOTOC_identity
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ)
    (x : GateHistory (ActiveHaarLayer m q) d) :
    activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, (1, 1)) =
      activeHaarCircuitOTOC A I ρ B M k d x := by
  simp only [activeHaarCircuitOTOC, ContinuousMap.coe_mk, activeHaarCircuitMatrix,
    haarBlockMatrix_one (fun i => (I d i).toAlgHom.toLinearMap) (fun i => (I d i).map_one),
    haarBlockMatrix_one (fun i => (A d i).toAlgHom.toLinearMap) (fun i => (A d i).map_one),
    one_mul]

/-- With earlier gates fixed, only the fresh active gates affect the OTOC.
The inactive gates are integrated out exactly, without a loss in the constant. -/
lemma activeHaarCircuitOTOC_section
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ)
    (hI : ∀ i (U : SU4), Commute (I d i U.val) B)
    (x : GateHistory (ActiveHaarLayer m q) d) (g : ActiveHaarLayer m q) :
    activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, g) =
      haarLocalOTOC (fun i => (A d i).toAlgHom.toLinearMap)
        ρ B (activeHaarCircuitMatrix A I d x) M k g.1 := by
  rw [haarLocalOTOC_apply]
  simp only [activeHaarCircuitOTOC, ContinuousMap.coe_mk, activeHaarCircuitMatrix,
    Matrix.conjTranspose_mul]
  have hi := haarBlockMatrix_inactive_conjugation (I d) B hI g.2
  simpa only [Matrix.mul_assoc] using congrArg
    (fun T => Matrix.trace (ρ * ((activeHaarCircuitMatrix A I d x).conjTranspose *
      ((haarBlockMatrix (fun i => (A d i).toAlgHom.toLinearMap) g.1).conjTranspose *
        T * haarBlockMatrix (fun i => (A d i).toAlgHom.toLinearMap) g.1) *
      activeHaarCircuitMatrix A I d x * M) ^ (2 * k))) hi

/-- The local inequality for the full fresh layer uses the active-block constant. -/
theorem activeHaarCircuit_localReverseVariance
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k d : ℕ)
    (hI : ∀ i (U : SU4), Commute (I d i U.val) B)
    (x : GateHistory (ActiveHaarLayer m q) d) :
    haarLocalConstant m k *
      ‖(∫ g, activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, g)
          ∂activeHaarLayerMeasure m q) - activeHaarCircuitOTOC A I ρ B M k d x‖ ^ 2 ≤
      complexVariance (activeHaarLayerMeasure m q)
        (fun g => activeHaarCircuitOTOC A I ρ B M k (d + 1) (x, g)) := by
  simp_rw [activeHaarCircuitOTOC_section A I ρ B M k d hI x]
  unfold activeHaarLayerMeasure
  rw [complexVariance_fst, integral_fun_fst, measureReal_univ_eq_one, one_smul]
  exact haarLocalOTOC_reverseVariance_identity
    (fun i => (A d i).toAlgHom.toLinearMap) (fun i => (A d i).map_one)
    ρ B (activeHaarCircuitMatrix A I d x) M k

set_option maxHeartbeats 800000 in
/-- Slope and persistence for full layers, uniformly in the inactive gate count. -/
theorem activeHaarCircuit_step_bounds
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k : ℕ)
    (hI : ∀ d i (U : SU4), Commute (I d i U.val) B) (d : ℕ) :
    (haarLocalConstant m k *
      ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k (d + 1) x
          ∂historyMeasure (activeHaarLayerMeasure m q) (d + 1)) -
        ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
          ∂historyMeasure (activeHaarLayerMeasure m q) d‖ ^ 2 ≤
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + 1))
        (activeHaarCircuitOTOC A I ρ B M k (d + 1))) ∧
    ((haarLocalConstant m k / (1 + haarLocalConstant m k)) *
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
        (activeHaarCircuitOTOC A I ρ B M k d) ≤
      complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + 1))
        (activeHaarCircuitOTOC A I ρ B M k (d + 1))) := by
  have hb := product_step_bounds (μ := historyMeasure (activeHaarLayerMeasure m q) d)
    (ν := activeHaarLayerMeasure m q)
    (activeHaarCircuitOTOC A I ρ B M k (d + 1))
    (activeHaarCircuitOTOC A I ρ B M k (d + 1)).continuous (1, 1)
    (haarLocalConstant_pos m k) (fun x => by
      rw [activeHaarCircuitOTOC_identity]
      exact activeHaarCircuit_localReverseVariance A I ρ B M k d (hI d) x)
  simpa only [activeHaarCircuitOTOC_identity] using hb

/-- The circuit's early mean equals one once spatial separation supplies the
commutation certificate. Unitarity is proved from the actual sampled gates. -/
lemma activeHaarCircuit_early_mean
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k a : ℕ)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1)
    (hpre : ∀ x : GateHistory (ActiveHaarLayer m q) a,
      Commute ((activeHaarCircuitMatrix A I a x).conjTranspose * B *
        activeHaarCircuitMatrix A I a x) M) :
    (∫ x, activeHaarCircuitOTOC A I ρ B M k a x
      ∂historyMeasure (activeHaarLayerMeasure m q) a) = 1 := by
  exact integral_preLightCone_otoc_eq_one _ ρ B M (activeHaarCircuitMatrix A I a)
    hρ (Filter.Eventually.of_forall (activeHaarCircuitMatrix_mem_unitary A I a)) hB hM
    (Filter.Eventually.of_forall hpre) k

end Circuit

set_option maxHeartbeats 800000 in
/-- A variance window for growing full layers: the constant is chosen before
the inactive gate count `q`, the global dimension, and all embeddings. Only an
algebraic locality certificate, the endpoint gap, and the width are inputs. -/
theorem activeHaarCircuit_theorem_VI_14 (m k : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (q : ℕ) (N : Type*) [Fintype N] [DecidableEq N]
      (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
      (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
      (ρ B M : Matrix N N ℂ),
      (∀ d i (U : SU4), Commute (I d i U.val) B) →
      ∀ {a b : ℕ}, a < b →
      (1 / 2 : ℝ) ≤
        ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k b x
            ∂historyMeasure (activeHaarLayerMeasure m q) b) -
          ∫ x, activeHaarCircuitOTOC A I ρ B M k a x
            ∂historyMeasure (activeHaarLayerMeasure m q) a‖ →
      ∀ (R : ℕ) {P : ℝ}, ((b - a : ℕ) : ℝ) ≤ P →
      ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
        η * (η / (1 + η)) ^ R / (4 * P ^ 2) ≤
          complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
            (activeHaarCircuitOTOC A I ρ B M k (d + r)) := by
  refine ⟨haarLocalConstant m k, haarLocalConstant_pos m k, ?_⟩
  intro q N _ _ A I ρ B M hI a b hab hchange R P hwidth
  exact theorem_VI_14_of_step_bounds
    (fun d => ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
      ∂historyMeasure (activeHaarLayerMeasure m q) d)
    (fun d => complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
      (activeHaarCircuitOTOC A I ρ B M k d)) (haarLocalConstant_pos m k)
    (fun d => (activeHaarCircuit_step_bounds A I ρ B M k hI d).1)
    (fun d => (activeHaarCircuit_step_bounds A I ρ B M k hI d).2)
    hab hchange R hwidth

set_option maxHeartbeats 800000 in
/-- The variance theorem with the mean gap derived from the paper's two
quarter-unit estimates. `referenceMean` is intended to be the global Haar
mean; the moment-control and reference-mean estimates are explicit inputs.
The early commutation and inactive-gate commutation certificates encode the
remaining geometric connection to a particular spatial architecture. -/
theorem activeHaarCircuit_theorem_of_moment_control
    {N : Type*} [Fintype N] [DecidableEq N] {m q : ℕ}
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] Matrix N N ℂ)
    (ρ B M : Matrix N N ℂ) (k : ℕ)
    (hI : ∀ d i (U : SU4), Commute (I d i U.val) B)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1)
    {a b : ℕ} (hab : a < b)
    (hpre : ∀ x : GateHistory (ActiveHaarLayer m q) a,
      Commute ((activeHaarCircuitMatrix A I a x).conjTranspose * B *
        activeHaarCircuitMatrix A I a x) M)
    (referenceMean : ℂ)
    (hcontrol : ‖(∫ x, activeHaarCircuitOTOC A I ρ B M k b x
      ∂historyMeasure (activeHaarLayerMeasure m q) b) - referenceMean‖ ≤ (1 / 4 : ℝ))
    (href : ‖referenceMean‖ ≤ (1 / 4 : ℝ))
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      haarLocalConstant m k * (haarLocalConstant m k / (1 + haarLocalConstant m k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC A I ρ B M k (d + r)) := by
  have hchange := mean_gap_one_half
    (activeHaarCircuit_early_mean A I ρ B M k a hρ hB hM hpre) hcontrol href
  exact theorem_VI_14_of_step_bounds
    (fun d => ∫ x, activeHaarCircuitOTOC A I ρ B M k d x
      ∂historyMeasure (activeHaarLayerMeasure m q) d)
    (fun d => complexVariance (historyMeasure (activeHaarLayerMeasure m q) d)
      (activeHaarCircuitOTOC A I ρ B M k d)) (haarLocalConstant_pos m k)
    (fun d => (activeHaarCircuit_step_bounds A I ρ B M k hI d).1)
    (fun d => (activeHaarCircuit_step_bounds A I ρ B M k hI d).2)
    hab hchange R hwidth

end Fluctuations
