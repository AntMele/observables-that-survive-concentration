import Fluctuations.TensorSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union

open scoped BigOperators Matrix

namespace Fluctuations

variable (Site : Type*) [Fintype Site] [DecidableEq Site]

/-- A finite parallel layer consists of pairwise disjoint physical patches.
Its gate count is unrestricted and can vary from layer to layer. -/
structure LayerArchitecture where
  gateCount : ℕ
  patch : Fin gateCount → Finset Site
  disjoint : Pairwise (fun i j => Disjoint (patch i) (patch j))

variable {Site}

namespace LayerArchitecture

def active (L : LayerArchitecture Site) (S : Finset Site) : Finset (Fin L.gateCount) :=
  Finset.univ.filter (fun i => ¬Disjoint (L.patch i) S)

omit [Fintype Site] in
@[simp] lemma mem_active (L : LayerArchitecture Site) (S : Finset Site)
    (i : Fin L.gateCount) : i ∈ L.active S ↔ ¬Disjoint (L.patch i) S := by
  simp [active]

/-- Pull a support backwards through one parallel layer, using only patches. -/
def pullback (L : LayerArchitecture Site) (S : Finset Site) : Finset Site :=
  S ∪ (L.active S).biUnion L.patch

omit [Fintype Site] in
lemma subset_pullback (L : LayerArchitecture Site) (S : Finset Site) :
    S ⊆ L.pullback S := Finset.subset_union_left

omit [Fintype Site] in
lemma patch_subset_pullback (L : LayerArchitecture Site) (S : Finset Site)
    {i : Fin L.gateCount} (hi : i ∈ L.active S) : L.patch i ⊆ L.pullback S := by
  intro s hs
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)

omit [Fintype Site] in
lemma active_mono (L : LayerArchitecture Site) {S T : Finset Site} (hST : S ⊆ T) :
    L.active S ⊆ L.active T := by
  intro i hi
  simp only [L.mem_active] at hi ⊢
  exact fun h => hi (h.mono_right hST)

omit [Fintype Site] in
lemma pullback_mono (L : LayerArchitecture Site) {S T : Finset Site} (hST : S ⊆ T) :
    L.pullback S ⊆ L.pullback T := by
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact (L.subset_pullback T) (hST hs)
  · obtain ⟨i, hi, hs⟩ := Finset.mem_biUnion.mp hs
    exact L.patch_subset_pullback T (L.active_mono hST hi) hs

/-- Every active patch contains a different site of `S`, so there are at most
`|S|` active gates regardless of the total layer size. -/
theorem card_active_le (L : LayerArchitecture Site) (S : Finset Site) :
    (L.active S).card ≤ S.card := by
  classical
  have hex : ∀ i : ↥(L.active S), ∃ s, s ∈ L.patch i.val ∧ s ∈ S := by
    intro i
    exact Finset.not_disjoint_iff.mp ((L.mem_active S i).mp i.prop)
  let f : ↥(L.active S) → ↥S := fun i => ⟨(hex i).choose, (hex i).choose_spec.2⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hsite : (hex i).choose = (hex j).choose := congrArg Subtype.val hij
  exact Finset.disjoint_left.mp (L.disjoint hne)
    (hex i).choose_spec.1 (hsite ▸ (hex j).choose_spec.1)

theorem gateCount_le_of_all_active (L : LayerArchitecture Site) (S : Finset Site)
    (hactive : ∀ i, ¬Disjoint (L.patch i) S) : L.gateCount ≤ S.card := by
  have heq : L.active S = Finset.univ := by
    ext i
    simp [hactive i]
  simpa only [heq, Finset.card_univ, Fintype.card_fin] using L.card_active_le S

lemma card_pullback_le (L : LayerArchitecture Site) (S : Finset Site)
    (r : ℕ) (hsize : ∀ i, (L.patch i).card ≤ r) :
    (L.pullback S).card ≤ (r + 1) * S.card := by
  calc
    (L.pullback S).card ≤ S.card + ((L.active S).biUnion L.patch).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + (L.active S).card * r := by
      gcongr
      exact Finset.card_biUnion_le_card_mul _ _ _ (fun i _ => hsize i)
    _ ≤ S.card + S.card * r := by gcongr; exact L.card_active_le S
    _ = (r + 1) * S.card := by ring

noncomputable def matrix (L : LayerArchitecture Site)
    (g : Fin L.gateCount → QubitOperator Site) : QubitOperator Site :=
  ((List.finRange L.gateCount).map g).prod

/-- Actual site support discharges both cross-commutation and inactive
commutation in the exact full-layer cancellation theorem. -/
theorem conjugate_eq_active (L : LayerArchitecture Site)
    (g : Fin L.gateCount → QubitOperator Site)
    (hlocal : ∀ i, Supported (L.patch i) (g i))
    (hunitary : ∀ i, g i ∈ Matrix.unitaryGroup (QubitState Site) ℂ)
    {S : Finset Site} {B : QubitOperator Site} (hB : Supported S B) :
    (L.matrix g).conjTranspose * B * L.matrix g =
      (((List.finRange L.gateCount).filter (fun i => i ∈ L.active S)).map g).prod.conjTranspose * B *
        (((List.finRange L.gateCount).filter (fun i => i ∈ L.active S)).map g).prod := by
  apply matrix_conjugate_layer_eq_active
  · intro i _ hi j _ hj
    exact (hlocal i).commute (hlocal j) (L.disjoint (fun heq => hj (heq ▸ hi)))
  · intro i _ _
    exact hunitary i
  · intro i _ hi
    exact (hlocal i).commute hB (by simpa only [L.mem_active, not_not] using hi)

/-- One Heisenberg layer propagates support only across active patches. -/
theorem supported_conjugate (L : LayerArchitecture Site)
    (g : Fin L.gateCount → QubitOperator Site)
    (hlocal : ∀ i, Supported (L.patch i) (g i))
    (hunitary : ∀ i, g i ∈ Matrix.unitaryGroup (QubitState Site) ℂ)
    {S : Finset Site} {B : QubitOperator Site} (hB : Supported S B) :
    Supported (L.pullback S) ((L.matrix g).conjTranspose * B * L.matrix g) := by
  rw [L.conjugate_eq_active g hlocal hunitary hB]
  have hprod : Supported (L.pullback S)
      ((((List.finRange L.gateCount).filter (fun i => i ∈ L.active S)).map g).prod) := by
    apply Subalgebra.list_prod_mem
    intro A hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    exact (hlocal i).mono (L.patch_subset_pullback S (by simpa using (List.mem_filter.mp hi).2))
  exact (hprod.conjTranspose.mul (hB.mono (L.subset_pullback S))).mul hprod

end LayerArchitecture

/-- Gate values are carried separately from the architecture determining the
light cone; locality is the concrete tensor support defined above. -/
structure SpatialLayer (Site : Type*) [Fintype Site] [DecidableEq Site] where
  architecture : LayerArchitecture Site
  gate : Fin architecture.gateCount → QubitOperator Site
  supported : ∀ i, Supported (architecture.patch i) (gate i)
  unitary : ∀ i, gate i ∈ Matrix.unitaryGroup (QubitState Site) ℂ

noncomputable def SpatialLayer.matrix (L : SpatialLayer Site) : QubitOperator Site :=
  L.architecture.matrix L.gate

/-- Architecture-only backward cone, ordered from the layer adjacent to the
observable to the layer furthest from it. -/
def backwardCone : List (LayerArchitecture Site) → Finset Site → Finset Site
  | [], S => S
  | L :: ls, S => backwardCone ls (L.pullback S)

theorem backwardCone_mono (ls : List (LayerArchitecture Site))
    {S T : Finset Site} (hST : S ⊆ T) : backwardCone ls S ⊆ backwardCone ls T := by
  induction ls generalizing S T with
  | nil => exact hST
  | cons L ls ih => exact ih (L.pullback_mono hST)

/-- Total number of gates in the architecture's backwards active block. -/
def backwardActiveGateCount : List (LayerArchitecture Site) → Finset Site → ℕ
  | [], _ => 0
  | L :: ls, S => (L.active S).card + backwardActiveGateCount ls (L.pullback S)

noncomputable def spatialCircuitMatrix (ls : List (SpatialLayer Site)) : QubitOperator Site :=
  (ls.map SpatialLayer.matrix).prod

/-- The architecture determines a support bound for every compatible choice
of gate matrices. The number and patches of gates may change in every layer. -/
theorem supported_spatialCircuit (ls : List (SpatialLayer Site))
    {S : Finset Site} {B : QubitOperator Site} (hB : Supported S B) :
    Supported (backwardCone (ls.map SpatialLayer.architecture) S)
      ((spatialCircuitMatrix ls).conjTranspose * B * spatialCircuitMatrix ls) := by
  induction ls generalizing S B with
  | nil => simpa [spatialCircuitMatrix, backwardCone] using hB
  | cons L ls ih =>
    have hL := L.architecture.supported_conjugate L.gate L.supported L.unitary hB
    have ht := ih hL
    simpa only [spatialCircuitMatrix, List.map_cons, List.prod_cons,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, backwardCone, SpatialLayer.matrix] using ht

/-- Spatial separation of the deterministic cone proves the early
commutation certificate used by the OTOC identity. -/
theorem spatialCircuit_commute_of_disjoint (ls : List (SpatialLayer Site))
    {S T : Finset Site} {B M : QubitOperator Site}
    (hB : Supported S B) (hM : Supported T M)
    (hseparated : Disjoint (backwardCone (ls.map SpatialLayer.architecture) S) T) :
    Commute ((spatialCircuitMatrix ls).conjTranspose * B * spatialCircuitMatrix ls) M :=
  (supported_spatialCircuit ls hB).commute hM hseparated

/-- Explicit fixed-depth support bound independent of total qubit count. -/
theorem card_backwardCone_le (ls : List (LayerArchitecture Site)) (S : Finset Site)
    (r : ℕ) (hsize : ∀ L ∈ ls, ∀ i, (L.patch i).card ≤ r) :
    (backwardCone ls S).card ≤ (r + 1) ^ ls.length * S.card := by
  induction ls generalizing S with
  | nil => simp [backwardCone]
  | cons L ls ih =>
    calc
      (backwardCone (L :: ls) S).card ≤
          (r + 1) ^ ls.length * (L.pullback S).card :=
        ih _ (fun K hK => hsize K (by simp [hK]))
      _ ≤ (r + 1) ^ ls.length * ((r + 1) * S.card) :=
        Nat.mul_le_mul_left _ (L.card_pullback_le S r (hsize L (by simp)))
      _ = (r + 1) ^ (L :: ls).length * S.card := by
        simp [pow_succ, Nat.mul_assoc]

/-- A constant-depth block has a bounded number of active gates, independently
of all inactive gates and the total number of qubits. -/
theorem backwardActiveGateCount_le (ls : List (LayerArchitecture Site)) (S : Finset Site)
    (r : ℕ) (hsize : ∀ L ∈ ls, ∀ i, (L.patch i).card ≤ r) :
    backwardActiveGateCount ls S ≤ ls.length * (r + 1) ^ ls.length * S.card := by
  induction ls generalizing S with
  | nil => simp [backwardActiveGateCount]
  | cons L ls ih =>
    have hp : 0 < (r + 1) ^ (ls.length + 1) := pow_pos (by omega) _
    calc
      backwardActiveGateCount (L :: ls) S ≤
          S.card + ls.length * (r + 1) ^ ls.length * (L.pullback S).card :=
        Nat.add_le_add (L.card_active_le S) (ih _ (fun K hK => hsize K (by simp [hK])))
      _ ≤ S.card + ls.length * (r + 1) ^ ls.length * ((r + 1) * S.card) := by
        gcongr
        exact L.card_pullback_le S r (hsize L (by simp))
      _ = S.card + ls.length * (r + 1) ^ (ls.length + 1) * S.card := by
        rw [pow_succ]
        ring
      _ ≤ (L :: ls).length * (r + 1) ^ (L :: ls).length * S.card := by
        simp only [List.length_cons]
        nlinarith

end Fluctuations
