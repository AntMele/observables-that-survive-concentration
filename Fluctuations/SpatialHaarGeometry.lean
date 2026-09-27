import Fluctuations.CircuitGeometry
import Fluctuations.ActiveHaarCircuit
import Mathlib.Data.List.OfFn

open MeasureTheory
open scoped Matrix

namespace Fluctuations

variable {Site : Type*} [Fintype Site] [DecidableEq Site] {m q : ℕ}

/-- The actual active/inactive Haar layer's spatial architecture. Its combined
patch list is pairwise disjoint; sampled gate values are absent from the data. -/
structure HaarSpatialArchitecture (Site : Type*) [Fintype Site] [DecidableEq Site]
    (m q : ℕ) where
  activePatch : ℕ → Fin m → Finset Site
  inactivePatch : ℕ → Fin q → Finset Site
  disjoint : ∀ d, Pairwise (fun i j =>
    Disjoint (Fin.append (inactivePatch d) (activePatch d) i)
      (Fin.append (inactivePatch d) (activePatch d) j))

namespace HaarSpatialArchitecture

def layer (P : HaarSpatialArchitecture Site m q) (d : ℕ) : LayerArchitecture Site where
  gateCount := q + m
  patch := Fin.append (P.inactivePatch d) (P.activePatch d)
  disjoint := P.disjoint d

/-- Backwards propagation uses the newest physical layer first, as required
by `U_(d+1) = L_d U_d`. -/
def lightCone (P : HaarSpatialArchitecture Site m q) : ℕ → Finset Site → Finset Site
  | 0, S => S
  | d + 1, S => P.lightCone d ((P.layer d).pullback S)

lemma lightCone_mono_support (P : HaarSpatialArchitecture Site m q) (d : ℕ)
    {S T : Finset Site} (hST : S ⊆ T) : P.lightCone d S ⊆ P.lightCone d T := by
  induction d generalizing S T with
  | zero => exact hST
  | succ d ih => exact ih ((P.layer d).pullback_mono hST)

lemma lightCone_mono_depth (P : HaarSpatialArchitecture Site m q) (S : Finset Site) :
    Monotone (fun d => P.lightCone d S) := by
  apply monotone_nat_of_le_succ
  intro d
  exact P.lightCone_mono_support d ((P.layer d).subset_pullback S)

/-- Labeling all active Haar gates by patches meeting `S` proves the uniform
gate-count bound used to choose the local variance constant. -/
theorem active_count_le (P : HaarSpatialArchitecture Site m q) (d : ℕ)
    (S : Finset Site) (hactive : ∀ i, ¬Disjoint (P.activePatch d i) S) : m ≤ S.card := by
  let L : LayerArchitecture Site := {
    gateCount := m
    patch := P.activePatch d
    disjoint := by
      intro i j hij
      have hne : Fin.natAdd q i ≠ Fin.natAdd q j := by
        intro heq
        apply hij
        apply Fin.ext
        simpa using congrArg Fin.val heq
      simpa [Fin.append] using P.disjoint d hne }
  exact L.gateCount_le_of_all_active S hactive

/-- Uniform patch size gives an explicit support bound at every fixed depth,
independent of the total number of sites and inactive gates. -/
theorem card_lightCone_le (P : HaarSpatialArchitecture Site m q)
    (r : ℕ) (hsize : ∀ d i, ((P.layer d).patch i).card ≤ r)
    (d : ℕ) (S : Finset Site) :
    (P.lightCone d S).card ≤ (r + 1) ^ d * S.card := by
  induction d generalizing S with
  | zero => simp [lightCone]
  | succ d ih =>
    calc
      (P.lightCone (d + 1) S).card ≤
          (r + 1) ^ d * ((P.layer d).pullback S).card := ih _
      _ ≤ (r + 1) ^ d * ((r + 1) * S.card) :=
        Nat.mul_le_mul_left _ ((P.layer d).card_pullback_le S r (hsize d))
      _ = (r + 1) ^ (d + 1) * S.card := by rw [pow_succ, Nat.mul_assoc]

variable (P : HaarSpatialArchitecture Site m q)
    (A : ℕ → Fin m → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] QubitOperator Site)
    (I : ℕ → Fin q → Matrix (Fin 4) (Fin 4) ℂ →⋆ₐ[ℂ] QubitOperator Site)

noncomputable def gates (d : ℕ) (x : ActiveHaarLayer m q) :
    Fin (q + m) → QubitOperator Site :=
  Fin.append (fun i => I d i (x.2 i).val) (fun i => A d i (x.1 i).val)

lemma matrix_gates (d : ℕ) (x : ActiveHaarLayer m q) :
    (P.layer d).matrix (gates A I d x) =
      haarBlockMatrix (fun i => (I d i).toAlgHom.toLinearMap) x.2 *
        haarBlockMatrix (fun i => (A d i).toAlgHom.toLinearMap) x.1 := by
  simp only [LayerArchitecture.matrix, layer, gates, ← List.ofFn_eq_map,
    List.ofFn_fin_append, List.prod_append, haarBlockMatrix]
  rfl

variable
    (hA : ∀ d i (U : SU4), Supported (P.activePatch d i) (A d i U.val))
    (hI : ∀ d i (U : SU4), Supported (P.inactivePatch d i) (I d i U.val))

include hA hI

lemma gates_supported (d : ℕ) (x : ActiveHaarLayer m q) :
    ∀ i, Supported ((P.layer d).patch i) (gates A I d x i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [layer, gates, Fin.append] using hI d j (x.2 j)
  · intro j
    simpa [layer, gates, Fin.append] using hA d j (x.1 j)

omit hA hI in
lemma gates_unitary (d : ℕ) (x : ActiveHaarLayer m q) :
    ∀ i, gates A I d x i ∈ Matrix.unitaryGroup (QubitState Site) ℂ := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [gates, Fin.append] using starAlgHom_su4_mem_unitary (I d j) (x.2 j)
  · intro j
    simpa [gates, Fin.append] using starAlgHom_su4_mem_unitary (A d j) (x.1 j)

/-- The actual sampled circuit, including every inactive gate, obeys the
deterministic architecture cone. -/
theorem circuit_supported (d : ℕ) (x : GateHistory (ActiveHaarLayer m q) d)
    {S : Finset Site} {B : QubitOperator Site} (hB : Supported S B) :
    Supported (P.lightCone d S)
      ((activeHaarCircuitMatrix A I d x).conjTranspose * B * activeHaarCircuitMatrix A I d x) := by
  induction d generalizing S B with
  | zero => simpa [lightCone, activeHaarCircuitMatrix] using hB
  | succ d ih =>
    have hL := (P.layer d).supported_conjugate (gates A I d x.2)
      (P.gates_supported A I hA hI d x.2) (gates_unitary A I d x.2) hB
    rw [P.matrix_gates A I d x.2] at hL
    have ht := ih x.1 hL
    simpa only [lightCone, activeHaarCircuitMatrix, Matrix.conjTranspose_mul,
      Matrix.mul_assoc] using ht

/-- This supplies `activeHaarCircuit_early_mean`'s commutation input purely
from concrete physical support and architecture separation. -/
theorem early_commute (d : ℕ) (x : GateHistory (ActiveHaarLayer m q) d)
    {S T : Finset Site} {B M : QubitOperator Site}
    (hB : Supported S B) (hM : Supported T M)
    (hsep : Disjoint (P.lightCone d S) T) :
    Commute ((activeHaarCircuitMatrix A I d x).conjTranspose * B *
      activeHaarCircuitMatrix A I d x) M :=
  (P.circuit_supported A I hA hI d x hB).commute hM hsep

omit hA in
/-- This supplies the inactive-gate commutation input in the Haar variance
theorem from disjoint site patches and actual operator support. -/
theorem inactive_commute {S : Finset Site} {B : QubitOperator Site}
    (hB : Supported S B)
    (hsep : ∀ d i, Disjoint (P.inactivePatch d i) S) :
    ∀ d i (U : SU4), Commute (I d i U.val) B := by
  intro d i U
  exact (hI d i U).commute hB (hsep d i)

theorem early_mean (ρ B M : QubitOperator Site) (k d : ℕ)
    {S T : Finset Site} (hBsupport : Supported S B) (hMsupport : Supported T M)
    (hsep : Disjoint (P.lightCone d S) T)
    (hρ : Matrix.trace ρ = 1) (hB : B * B = 1) (hM : M * M = 1) :
    (∫ x, activeHaarCircuitOTOC A I ρ B M k d x
      ∂historyMeasure (activeHaarLayerMeasure m q) d) = 1 := by
  exact activeHaarCircuit_early_mean A I ρ B M k d hρ hB hM
    (fun x => P.early_commute A I hA hI d x hBsupport hMsupport hsep)

end HaarSpatialArchitecture

end Fluctuations
