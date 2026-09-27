import Fluctuations.SpatialHaarTheorem
import Fluctuations.GlobalHaarMeanAllDimensions

open MeasureTheory

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site] {m q : ℕ}

/-- The complete spatial Haar variance-window deduction at every fixed positive
order. Actual Haar smallness, the local numerical variance coefficient, and the
early mean are proved. The late observable-specific moment control, physical
architecture, support/cone separation, and transition width are hypotheses. -/
theorem spatialHaarCircuit_allOrders_of_globalHaar_control
    (L : HaarSpatialArchitecture Site m q)
    (hApair : ∀ d i, (L.activePatch d i).card = 2)
    (hIpair : ∀ d i, (L.inactivePatch d i).card = 2)
    (ρ B M : QubitOperator Site) (k : ℕ) (hk : 0 < k) (S T : Finset Site)
    (hBsupport : Supported S B) (hMsupport : Supported T M)
    (hactive : ∀ d i, ¬Disjoint (L.activePatch d i) S)
    (hinactive : ∀ d i, Disjoint (L.inactivePatch d i) S)
    (hρ : Matrix.trace ρ = 1)
    (hBHerm : B.IsHermitian) (hB : B * B = 1) (hBtr : Matrix.trace B = 0)
    (hMHerm : M.IsHermitian) (hM : M * M = 1) (hMtr : Matrix.trace M = 0)
    (hDimension : 8 * ((2 * k).factorial : ℝ) ^ 3 ≤
      ((2 : ℝ) ^ Fintype.card Site) ^ 2)
    {a b : ℕ} (hab : a < b) (hsep : Disjoint (L.lightCone a S) T)
    (hcontrol : ‖(∫ x,
        activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
          ρ B M k b x ∂historyMeasure (activeHaarLayerMeasure m q) b) -
        globalHaarOTOCMean ρ B M k‖ ≤ (1 / 4 : ℝ))
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant S.card k *
        (explicitHaarConstant S.card k / (1 + explicitHaarConstant S.card k)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
            ρ B M k (d + r)) := by
  have hcard : (Fintype.card (QubitState Site) : ℝ) =
      (2 : ℝ) ^ Fintype.card Site := by
    simp [QubitState]
  have hsmall := globalHaarOTOCMean_norm_le_quarter_all_dimensions ρ B M hρ
    hBHerm hB hBtr hMHerm hM hMtr k hk (by rwa [hcard])
  exact spatialHaarCircuit_of_globalHaar_control L hApair hIpair ρ B M k S T
    hBsupport hMsupport hactive hinactive hρ hB hM hab hsep hcontrol hsmall R hwidth

end Fluctuations
