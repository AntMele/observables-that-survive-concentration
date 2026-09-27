import Fluctuations.SpatialHaarTheorem
import Fluctuations.GlobalHaarFirstOrderValue

open MeasureTheory

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site] {m q : ℕ}

/-- Two or more qubits suffice for the actual first-order Haar quarter-bound. -/
theorem qubit_globalHaarOTOCMean_one_norm_le_quarter
    (ρ B M : QubitOperator Site) (hρ : Matrix.trace ρ = 1)
    (hBB : B * B = 1) (hB : Matrix.trace B = 0)
    (hMM : M * M = 1) (hM : Matrix.trace M = 0)
    (hsize : 2 ≤ Fintype.card Site) :
    ‖globalHaarOTOCMean ρ B M 1‖ ≤ (1 / 4 : ℝ) := by
  have hdim : 3 ≤ Fintype.card (QubitState Site) := by
    simp only [QubitState, Fintype.card_fun, Fintype.card_fin]
    have hp : (2 : ℕ) ^ 2 ≤ 2 ^ Fintype.card Site := by
      gcongr
      norm_num
    omega
  letI : Nontrivial (QubitState Site) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact globalHaarOTOCMean_one_norm_le_quarter ρ B M hρ hBB hB hMM hM hdim

/-- The first-order spatial variance window with actual Haar smallness proved
for trace-one inputs and traceless involutions on at least two qubits.
The late observable-specific moment control remains a hypothesis. -/
theorem spatialHaarCircuit_firstOrder_of_globalHaar_control
    (L : HaarSpatialArchitecture Site m q)
    (hApair : ∀ d i, (L.activePatch d i).card = 2)
    (hIpair : ∀ d i, (L.inactivePatch d i).card = 2)
    (ρ B M : QubitOperator Site) (S T : Finset Site)
    (hBsupport : Supported S B) (hMsupport : Supported T M)
    (hactive : ∀ d i, ¬Disjoint (L.activePatch d i) S)
    (hinactive : ∀ d i, Disjoint (L.inactivePatch d i) S)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1)
    (hBtr : Matrix.trace B = 0) (hMtr : Matrix.trace M = 0)
    (hsize : 2 ≤ Fintype.card Site)
    {a b : ℕ} (hab : a < b) (hsep : Disjoint (L.lightCone a S) T)
    (hcontrol : ‖(∫ x,
        activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
          ρ B M 1 b x ∂historyMeasure (activeHaarLayerMeasure m q) b) -
        globalHaarOTOCMean ρ B M 1‖ ≤ (1 / 4 : ℝ))
    (R : ℕ) {P : ℝ} (hwidth : ((b - a : ℕ) : ℝ) ≤ P) :
    ∃ d, a < d ∧ d ≤ b ∧ ∀ r : ℕ, r ≤ R →
      explicitHaarConstant S.card 1 *
        (explicitHaarConstant S.card 1 / (1 + explicitHaarConstant S.card 1)) ^ R /
        (4 * P ^ 2) ≤
        complexVariance (historyMeasure (activeHaarLayerMeasure m q) (d + r))
          (activeHaarCircuitOTOC (L.activeEmbedding hApair) (L.inactiveEmbedding hIpair)
            ρ B M 1 (d + r)) := by
  exact spatialHaarCircuit_of_globalHaar_control L hApair hIpair ρ B M 1 S T
    hBsupport hMsupport hactive hinactive hρ hB hM hab hsep hcontrol
    (qubit_globalHaarOTOCMean_one_norm_le_quarter ρ B M hρ hB hBtr hM hMtr hsize) R hwidth

end Fluctuations
