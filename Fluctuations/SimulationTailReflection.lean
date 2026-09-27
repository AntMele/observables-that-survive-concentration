import Fluctuations.SimulationPrefixBridge
import Mathlib.Data.Fin.Rev

open scoped BigOperators
namespace Fluctuations
noncomputable section

section Relabel
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

def simulationRelabel (e : Site ≃ Site) (w : (Site → Fin 4) → ℝ) : (Site → Fin 4) → ℝ :=
  fun P => w (P ∘ e)

omit [Fintype Site] in
lemma simulationRelabel_replace (e : Site ≃ Site) (i j : Site)
    (P : Site → Fin 4) (q : TwoQubitPauliLabel) :
    (pauliPairReplace (e i) (e j) P q) ∘ e = pauliPairReplace i j (P ∘ e) q := by
  funext s
  by_cases hi : s = i <;> by_cases hj : s = j <;>
    simp_all [pauliPairReplace, Function.update_apply]

omit [Fintype Site] in
theorem simulationRelabel_pair (e : Site ≃ Site) (i j : Site)
    (w : (Site → Fin 4) → ℝ) :
    simulationRelabel e (pauliPairEvolution i j localPauliHaarKernel w) =
      pauliPairEvolution (e i) (e j) localPauliHaarKernel (simulationRelabel e w) := by
  funext P
  simp only [simulationRelabel, pauliPairEvolution, Function.comp_apply,
    simulationRelabel_replace]

theorem simulationRelabel_touching (e : Site ≃ Site) (i j : Site)
    (w : (Site → Fin 4) → ℝ) :
    simulationTouching (e i) (e j) (simulationRelabel e w) = simulationTouching i j w := by
  unfold simulationTouching simulationRelabel
  rw [← Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl (Fin 4)))]
  apply Finset.sum_congr rfl
  intro P _
  simp [Equiv.arrowCongr_apply, Function.comp_def]

lemma simulationPairKernel_swap (i j : Site) (Q P : PauliString Site) :
    pauliPairKernel i j Q P = pauliPairKernel j i Q P := by
  have he : (∀ s, s ≠ i → s ≠ j → Q s = P s) ↔
      (∀ s, s ≠ j → s ≠ i → Q s = P s) := by tauto
  simp only [pauliPairKernel, he]
  congr 1
  simp [localPauliHaarKernel, and_comm]

theorem simulationPairEvolution_swap (i j : Site) (hij : i ≠ j)
    (w : (Site → Fin 4) → ℝ) :
    pauliPairEvolution i j localPauliHaarKernel w = pauliPairEvolution j i localPauliHaarKernel w := by
  funext P
  calc
    _ = ∑ Q, pauliPairKernel i j P Q * w Q := (pauliPairKernel_mul i j hij w P).symm
    _ = ∑ Q, pauliPairKernel j i P Q * w Q := by simp_rw [simulationPairKernel_swap i j]
    _ = _ := pauliPairKernel_mul j i hij.symm w P

theorem simulationRelabel_layer_swap (e : Site ≃ Site) (bs : List (Site × Site))
    (hd : ∀ p ∈ bs, p.1 ≠ p.2) (w : (Site → Fin 4) → ℝ) :
    simulationRelabel e (pauliLayerEvolution bs w) =
      pauliLayerEvolution (bs.map (fun p => (e p.2, e p.1))) (simulationRelabel e w) := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    simp only [pauliLayerEvolution, List.map_cons]
    rw [ih (fun p hp => hd p (by simp [hp])), simulationRelabel_pair,
      simulationPairEvolution_swap (e p.1) (e p.2) (fun h => hd p (by simp) (e.injective h))]


omit [DecidableEq Site] in
theorem simulationRelabel_initial (e : Site ≃ Site) (P₀ : Site → Fin 4) :
    simulationRelabel e (pauliInitialVector P₀) = pauliInitialVector (P₀ ∘ e.symm) := by
  funext P
  have he : P ∘ e = P₀ ↔ P = P₀ ∘ e.symm := by
    constructor
    · intro h
      funext s
      have hs := congrFun h (e.symm s)
      simpa using hs
    · rintro rfl
      ext s
      simp
  simp only [simulationRelabel, pauliInitialVector, he]

lemma simulationTouching_symm (i j : Site) (w : (Site → Fin 4) → ℝ) :
    simulationTouching i j w = simulationTouching j i w := by
  simp only [simulationTouching, and_comm]

lemma simulationInitial_pair_fixed (i j : Site) (hij : i ≠ j) (P₀ : Site → Fin 4)
    (hi : P₀ i = 0) (hj : P₀ j = 0) :
    pauliPairEvolution i j localPauliHaarKernel (pauliInitialVector P₀) =
      pauliInitialVector P₀ := by
  rw [pauliInitialVector_product]
  funext P
  apply pauliPairEvolution_product_fixed _ i j hij
  intro q
  simpa only [hi, hj, pauliIdentityWeight] using pauliHaar_identity_product q

lemma simulationInitial_layer_fixed (bs : List (Site × Site)) (P₀ : Site → Fin 4)
    (hd : ∀ p ∈ bs, p.1 ≠ p.2) (hzero : ∀ p ∈ bs, P₀ p.1 = 0 ∧ P₀ p.2 = 0) :
    pauliLayerEvolution bs (pauliInitialVector P₀) = pauliInitialVector P₀ := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    rw [pauliLayerEvolution, simulationInitial_pair_fixed _ _ (hd p (by simp)) P₀
      (hzero p (by simp)).1 (hzero p (by simp)).2]
    exact ih (fun p hp => hd p (by simp [hp])) (fun p hp => hzero p (by simp [hp]))

end Relabel

/-- Reflection of the actual qubit chain, including the order within a cell. -/
def simulationSiteReflection (c : ℕ) : BrickworkSite c ≃ BrickworkSite c :=
  Equiv.prodCongr Fin.revPerm Fin.revPerm

@[simp] lemma simulationSiteReflection_apply (c : ℕ) (a : Fin (c+1)) (b : Fin 2) :
    simulationSiteReflection c (a,b) = (a.rev,b.rev) := rfl

def simulationReflectBond (c : ℕ) (p : BrickworkSite c × BrickworkSite c) :=
  (simulationSiteReflection c p.2, simulationSiteReflection c p.1)

def simulationReverseBonds (c : ℕ) (bs : List (BrickworkSite c × BrickworkSite c)) :=
  bs.reverse.map (simulationReflectBond c)

@[simp] lemma simulationReflectBond_odd {c : ℕ} (a : Fin (c+1)) :
    simulationReflectBond c (brickworkOddBond a) = brickworkOddBond a.rev := by
  simp [simulationReflectBond, brickworkOddBond, simulationSiteReflection_apply]

@[simp] lemma simulationReflectBond_even {c : ℕ} (a : Fin c) :
    simulationReflectBond c (brickworkEvenBond a) = brickworkEvenBond a.rev := by
  simp [simulationReflectBond, brickworkEvenBond, simulationSiteReflection_apply,
    Fin.rev_castSucc, Fin.rev_succ]

lemma simulationMap_reverse_ofFn {A B : Type*} {n : ℕ} (f : A → B) (g : Fin n → A) :
    (List.ofFn g).reverse.map f = List.ofFn (fun i => f (g i.rev)) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_ofFn]
    congr 2
    apply Fin.ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

@[simp] theorem simulationReverseBonds_odd (c : ℕ) :
    simulationReverseBonds c (brickworkOddBonds c) = brickworkOddBonds c := by
  rw [simulationReverseBonds, brickworkOddBonds, simulationMap_reverse_ofFn]
  simp only [simulationReflectBond_odd, Fin.rev_rev]

@[simp] theorem simulationReverseBonds_even (c : ℕ) :
    simulationReverseBonds c (brickworkEvenBonds c) = brickworkEvenBonds c := by
  rw [simulationReverseBonds, brickworkEvenBonds, simulationMap_reverse_ofFn]
  simp only [simulationReflectBond_even, Fin.rev_rev]

lemma simulationReverseBonds_append (c : ℕ) (bs cs : List (BrickworkSite c × BrickworkSite c)) :
    simulationReverseBonds c (bs ++ cs) = simulationReverseBonds c cs ++ simulationReverseBonds c bs := by
  simp [simulationReverseBonds]


@[simp] lemma simulationSiteReflection_symm (c : ℕ) :
    (simulationSiteReflection c).symm = simulationSiteReflection c := rfl

theorem simulationReflection_rightInitial (c : ℕ) :
    simulationRelabel (simulationSiteReflection c)
      (pauliInitialVector (pauliSiteZ (Fin.last c, (1 : Fin 2)))) =
      pauliInitialVector (brickworkInitialZ c) := by
  rw [simulationRelabel_initial]
  congr 1
  funext s
  rcases s with ⟨a,b⟩
  simp [pauliSiteZ, brickworkInitialZ, simulationSiteReflection_symm,
    Fin.rev_eq_iff]

/-- The complete terminal even layer is idle on the endpoint Pauli before
backward evolution starts; this removes the apparent one-layer shift. -/
theorem simulationEven_initial_fixed (c : ℕ) :
    pauliLayerEvolution (brickworkEvenBonds c) (pauliInitialVector (brickworkInitialZ c)) =
      pauliInitialVector (brickworkInitialZ c) := by
  apply simulationInitial_layer_fixed
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond]
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond, brickworkInitialZ]

theorem simulationReverseSchedule_action (c T : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    pauliLayerEvolution (simulationReverseBonds c (brickworkGateSchedule c T)) w =
      (brickworkPeriod c)^[T] w := by
  induction T generalizing w with
  | zero => rfl
  | succ T ih =>
    rw [brickworkGateSchedule, simulationReverseBonds_append, brickworkBlock,
      simulationReverseBonds_append, simulationReverseBonds_even, simulationReverseBonds_odd,
      pauliLayerEvolution_append, pauliLayerEvolution_append, ih]
    exact (Function.iterate_succ_apply (brickworkPeriod c) T w).symm

theorem simulationReverseSchedule_initial (c s : ℕ) :
    pauliLayerEvolution (simulationReverseBonds c (brickworkGateSchedule c (s+1)))
      (pauliInitialVector (brickworkInitialZ c)) = simulationBeforeEven c s := by
  rw [simulationReverseSchedule_action, Function.iterate_succ_apply]
  unfold brickworkPeriod
  rw [simulationEven_initial_fixed]
  rfl

theorem simulationReverseBonds_drop_even (c : ℕ) (a : Fin c) :
    simulationReverseBonds c ((brickworkEvenBonds c).drop (a.val+1)) =
      (brickworkEvenBonds c).take a.rev.val := by
  unfold simulationReverseBonds
  rw [List.reverse_drop, List.map_take]
  change (simulationReverseBonds c (brickworkEvenBonds c)).take _ = _
  rw [simulationReverseBonds_even]
  congr 1
  simp [brickworkEvenBonds, Fin.val_rev]

theorem simulationReverseBonds_drop_odd (c : ℕ) (a : Fin (c+1)) :
    simulationReverseBonds c ((brickworkOddBonds c).drop (a.val+1)) =
      (brickworkOddBonds c).take a.rev.val := by
  unfold simulationReverseBonds
  rw [List.reverse_drop, List.map_take]
  change (simulationReverseBonds c (brickworkOddBonds c)).take _ = _
  rw [simulationReverseBonds_odd]
  congr 1
  simp [brickworkOddBonds, Fin.val_rev]

/-- Exact reflection of the full reversed future law and its touching
observable. This retains all suffix gates and their chronological order. -/
theorem simulationBackward_reflect (c : ℕ)
    (bs : List (BrickworkSite c × BrickworkSite c))
    (hd : ∀ p ∈ bs, p.1 ≠ p.2) (p : BrickworkSite c × BrickworkSite c) :
    simulationTouching p.1 p.2
      (pauliLayerEvolution bs.reverse (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) =
      simulationTouching (simulationReflectBond c p).1 (simulationReflectBond c p).2
        (pauliLayerEvolution (simulationReverseBonds c bs)
          (pauliInitialVector (brickworkInitialZ c))) := by
  rw [← simulationRelabel_touching (simulationSiteReflection c),
    simulationRelabel_layer_swap _ _ (fun p hp => hd p (List.mem_reverse.mp hp)),
    simulationReflection_rightInitial]
  exact simulationTouching_symm _ _ _


/-- Backward future of an interior even gate, with the final idle layer
removed and the reflected physical bond identified exactly. -/
theorem simulationBackward_even (c T s : ℕ) (hs : s + 1 < T) (a : Fin c) :
    simulationTouching (a.castSucc,1) (a.succ,0)
      (pauliLayerEvolution
        ((brickworkGateSchedule c T).drop (s*(2*c+1)+(c+1)+a.val+1)).reverse
        (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) =
      simulationTouching (a.rev.castSucc,1) (a.rev.succ,0)
        (simulationBeforeEven c (T-s-2)) := by
  have hd (p : BrickworkSite c × BrickworkSite c)
      (hp : p ∈ (brickworkGateSchedule c T).drop (s*(2*c+1)+(c+1)+a.val+1)) : p.1 ≠ p.2 :=
    brickworkGateSchedule_distinct (List.mem_of_mem_drop hp)
  change simulationTouching (brickworkEvenBond a).1 (brickworkEvenBond a).2 _ = _
  rw [simulationBackward_reflect c _ hd (brickworkEvenBond a), simulationReflectBond_even,
    brickworkGateSchedule_drop_even c T s (by omega) a, simulationReverseBonds_append,
    simulationReverseBonds_drop_even, pauliLayerEvolution_append]
  change simulationTouching (a.rev.castSucc,1) (a.rev.succ,0) _ = _
  rw [simulationTouching_layer_misses]
  · rw [show T-s-1 = (T-s-2)+1 by omega, simulationReverseSchedule_initial]
  · intro p hp
    obtain ⟨b,_,rfl⟩ := brickworkEvenBonds_take_mem a.rev p hp
    simp [brickworkEvenBond]
  · exact brickworkEvenPrefix_misses a.rev

/-- Backward future of an odd gate with at least one later odd layer. -/
theorem simulationBackward_odd (c T s : ℕ) (hs : s + 1 < T) (a : Fin (c+1)) :
    simulationTouching (a,0) (a,1)
      (pauliLayerEvolution
        ((brickworkGateSchedule c T).drop (s*(2*c+1)+a.val+1)).reverse
        (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) =
      simulationTouching (a.rev,0) (a.rev,1) (simulationBeforeOdd c (T-s-2)) := by
  have hd (p : BrickworkSite c × BrickworkSite c)
      (hp : p ∈ (brickworkGateSchedule c T).drop (s*(2*c+1)+a.val+1)) : p.1 ≠ p.2 :=
    brickworkGateSchedule_distinct (List.mem_of_mem_drop hp)
  change simulationTouching (brickworkOddBond a).1 (brickworkOddBond a).2 _ = _
  rw [simulationBackward_reflect c _ hd (brickworkOddBond a), simulationReflectBond_odd,
    simulationSchedule_drop_odd c T s (by omega) a]
  simp only [simulationReverseBonds_append, simulationReverseBonds_even,
    simulationReverseBonds_drop_odd, pauliLayerEvolution_append]
  change simulationTouching (a.rev,0) (a.rev,1) _ = _
  rw [simulationTouching_layer_misses]
  · rw [show T-s-1 = (T-s-2)+1 by omega, simulationReverseSchedule_initial]
    rfl
  · intro p hp
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hp)
    simp [brickworkOddBond]
  · exact simulationOddPrefix_misses a.rev

/-- In the final odd layer the reversed future reduces exactly to the
initial reflected endpoint Pauli; its virtual forward time is one. -/
theorem simulationBackward_odd_last (c s : ℕ) (a : Fin (c+1)) :
    simulationTouching (a,0) (a,1)
      (pauliLayerEvolution
        ((brickworkGateSchedule c (s+1)).drop (s*(2*c+1)+a.val+1)).reverse
        (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) =
      simulationTouching (a.rev,0) (a.rev,1) (pauliInitialVector (brickworkInitialZ c)) := by
  have hd (p : BrickworkSite c × BrickworkSite c)
      (hp : p ∈ (brickworkGateSchedule c (s+1)).drop (s*(2*c+1)+a.val+1)) : p.1 ≠ p.2 :=
    brickworkGateSchedule_distinct (List.mem_of_mem_drop hp)
  change simulationTouching (brickworkOddBond a).1 (brickworkOddBond a).2 _ = _
  rw [simulationBackward_reflect c _ hd (brickworkOddBond a), simulationReflectBond_odd,
    simulationSchedule_drop_odd c (s+1) s (by omega) a]
  simp only [show s+1-s-1=0 by omega, brickworkGateSchedule, List.append_nil,
    simulationReverseBonds_append, simulationReverseBonds_even,
    simulationReverseBonds_drop_odd, pauliLayerEvolution_append, simulationEven_initial_fixed]
  change simulationTouching (a.rev,0) (a.rev,1) _ = _
  apply simulationTouching_layer_misses
  · intro p hp
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hp)
    simp [brickworkOddBond]
  · exact simulationOddPrefix_misses a.rev


/-- The final even layer has zero backwards active mass on every bond. -/
theorem simulationBackward_even_last (c s : ℕ) (a : Fin c) :
    simulationTouching (a.castSucc,1) (a.succ,0)
      (pauliLayerEvolution
        ((brickworkGateSchedule c (s+1)).drop (s*(2*c+1)+(c+1)+a.val+1)).reverse
        (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) = 0 := by
  have hd (p : BrickworkSite c × BrickworkSite c)
      (hp : p ∈ (brickworkGateSchedule c (s+1)).drop (s*(2*c+1)+(c+1)+a.val+1)) : p.1 ≠ p.2 :=
    brickworkGateSchedule_distinct (List.mem_of_mem_drop hp)
  change simulationTouching (brickworkEvenBond a).1 (brickworkEvenBond a).2 _ = 0
  rw [simulationBackward_reflect c _ hd (brickworkEvenBond a), simulationReflectBond_even,
    brickworkGateSchedule_drop_even c (s+1) s (by omega) a]
  simp only [show s+1-s-1=0 by omega, brickworkGateSchedule, List.append_nil,
    simulationReverseBonds_drop_even]
  change simulationTouching (a.rev.castSucc,1) (a.rev.succ,0) _ = 0
  rw [simulationTouching_layer_misses]
  · simp only [simulationTouching, pauliInitialVector, ite_mul, one_mul, zero_mul]
    simp [brickworkInitialZ]
  · intro p hp
    obtain ⟨b,_,rfl⟩ := brickworkEvenBonds_take_mem a.rev p hp
    simp [brickworkEvenBond]
  · exact brickworkEvenPrefix_misses a.rev

end
end Fluctuations
