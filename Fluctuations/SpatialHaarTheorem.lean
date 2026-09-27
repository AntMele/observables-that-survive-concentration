import Fluctuations.SpatialHaarGeometry
import Fluctuations.PatchEmbedding
import Fluctuations.ExplicitHaarCircuit
import Fluctuations.GlobalHaarMean

/-!
# Spatial Haar circuit variance theorem

Physical patches supply the commutation and light-cone certificates. The
active count is bounded by the observable support, so the numerical constant
is independent of the number of qubits and of inactive gates. The late mean
is compared with the actual global-Haar mean. Its smallness remains an
explicit input, rather than being hidden in the geometric assumptions.
-/

open MeasureTheory

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site] {m q : ℕ}

namespace HaarSpatialArchitecture

noncomputable def activeEmbedding (P : HaarSpatialArchitecture Site m q)
    (hpair : ∀ d i, (P.activePatch d i).card = 2) (d : ℕ) (i : Fin m) :
    Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] QubitOperator Site :=
  twoQubitPatchEmbedding (P.activePatch d i) (hpair d i)

noncomputable def inactiveEmbedding (P : HaarSpatialArchitecture Site m q)
    (hpair : ∀ d i, (P.inactivePatch d i).card = 2) (d : ℕ) (i : Fin q) :
    Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] QubitOperator Site :=
  twoQubitPatchEmbedding (P.inactivePatch d i) (hpair d i)

lemma activeEmbedding_supported (P : HaarSpatialArchitecture Site m q)
    (hpair : ∀ d i, (P.activePatch d i).card = 2) (d : ℕ) (i : Fin m) (U : SU4) :
    Supported (P.activePatch d i) (P.activeEmbedding hpair d i U.val) :=
  supported_twoQubitPatchEmbedding _ _ _

lemma inactiveEmbedding_supported (P : HaarSpatialArchitecture Site m q)
    (hpair : ∀ d i, (P.inactivePatch d i).card = 2) (d : ℕ) (i : Fin q) (U : SU4) :
    Supported (P.inactivePatch d i) (P.inactiveEmbedding hpair d i U.val) :=
  supported_twoQubitPatchEmbedding _ _ _

end HaarSpatialArchitecture

set_option maxHeartbeats 1000000 in
/-- With the mean-change assumption, the spatial Haar theorem has no local
reverse-variance or algebraic commutation assumption. Both are proved. -/
theorem spatialHaarCircuit_variance_window
    (L : HaarSpatialArchitecture Site m q)
    (hApair : ∀ d i, (L.activePatch d i).card = 2)
    (hIpair : ∀ d i, (L.inactivePatch d i).card = 2)
    (ρ B M : QubitOperator Site) (k : ℕ) (S : Finset Site)
    (hB : Supported S B)
    (hactive : ∀ d i, ¬Disjoint (L.activePatch d i) S)
    (hinactive : ∀ d i, Disjoint (L.inactivePatch d i) S)
    {a b : ℕ} (hab : a < b)
    (hchange : (1 / 2 : ℝ) ≤
      ‖(∫ x, activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
        ρ B M k b x ∂historyMeasure (activeHaarLayerMeasure m q) b) -
        ∫ x, activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
        ρ B M k a x ∂historyMeasure (activeHaarLayerMeasure m q) a‖)
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant S.card k *
        (explicitHaarConstant S.card k / (1 + explicitHaarConstant S.card k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
            ρ B M k (d + r)) := by
  have hI := L.inactive_commute (L.inactiveEmbedding hIpair)
    (L.inactiveEmbedding_supported hIpair) hB hinactive
  obtain ⟨d, hda, hdb, hd⟩ := activeHaarCircuit_explicit_variance_window
    (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair) ρ B M k hI hab hchange R hwidth
  refine ⟨d, hda, hdb, fun r hr => ?_⟩
  exact (explicitHaarWindowConstant_antitone (L.active_count_le 0 S (hactive 0)) k R P).trans
    (hd r hr)

set_option maxHeartbeats 1000000 in
/-- The reference is the genuine U(2^n) Haar mean of the same observable.
Architecture separation proves the early mean is one. The actual global-Haar
mean's quarter-bound is still explicit: the all-orders estimate has not yet
been discharged by this formalization. -/
theorem spatialHaarCircuit_of_globalHaar_control
    (L : HaarSpatialArchitecture Site m q)
    (hApair : ∀ d i, (L.activePatch d i).card = 2)
    (hIpair : ∀ d i, (L.inactivePatch d i).card = 2)
    (ρ B M : QubitOperator Site) (k : ℕ) (S T : Finset Site)
    (hBsupport : Supported S B) (hMsupport : Supported T M)
    (hactive : ∀ d i, ¬Disjoint (L.activePatch d i) S)
    (hinactive : ∀ d i, Disjoint (L.inactivePatch d i) S)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1)
    {a b : ℕ} (hab : a < b) (hsep : Disjoint (L.lightCone a S) T)
    (hcontrol : ‖(∫ x,
        activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
          ρ B M k b x ∂historyMeasure (activeHaarLayerMeasure m q) b) -
        globalHaarOTOCMean ρ B M k‖ ≤ (1 / 4 : ℝ))
    (hsmall : ‖globalHaarOTOCMean ρ B M k‖ ≤ (1 / 4 : ℝ))
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant S.card k *
        (explicitHaarConstant S.card k / (1 + explicitHaarConstant S.card k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
            ρ B M k (d + r)) := by
  have hearly := L.early_mean (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
    (L.activeEmbedding_supported hApair) (L.inactiveEmbedding_supported hIpair)
    ρ B M k a hBsupport hMsupport hsep hρ hB hM
  exact spatialHaarCircuit_variance_window L hApair hIpair ρ B M k S hBsupport
    hactive hinactive hab (mean_gap_one_half hearly hcontrol hsmall) R hwidth

end Fluctuations
