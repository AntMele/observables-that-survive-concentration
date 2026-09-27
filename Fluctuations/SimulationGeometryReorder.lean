import Fluctuations.SimulationGeometrySampler
import Fluctuations.SimulationSamplerReorder

/-! Discharge the matching and permutation requirements for the actual
outside-first physical brickwork layers used in the runtime proof. -/
namespace Fluctuations
noncomputable section

lemma simulationBrickworkLayer_matching (c t : ℕ)
    (p q : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ simulationBrickworkLayer c t) (hq : q ∈ simulationBrickworkLayer c t)
    (hne : p ≠ q) : p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
  unfold simulationBrickworkLayer at hp hq
  split_ifs at hp hq with ht
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
    have hab : a ≠ b := by intro h; subst b; exact hne rfl
    simp [brickworkOddBond,hab]
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
    have hab : a ≠ b := by intro h; subst b; exact hne rfl
    simp [brickworkEvenBond,hab]

lemma simulationOutsideRetained_perm {α : Type*} [DecidableEq α]
    (layer retained : Finset α) (hr : retained ⊆ layer) :
    layer.toList.Perm ((layer \ retained).toList ++ retained.toList) := by
  apply (List.perm_ext_iff_of_nodup layer.nodup_toList _).mpr
  · intro p
    simp only [Finset.mem_toList,List.mem_append,Finset.mem_sdiff]
    constructor
    · intro h
      by_cases hp : p ∈ retained
      · exact Or.inr hp
      · exact Or.inl ⟨h,hp⟩
    · rintro (⟨h,_⟩ | h)
      · exact h
      · exact hr h
  · apply List.nodup_append.mpr
    refine ⟨(layer \ retained).nodup_toList,retained.nodup_toList,?_⟩
    intro a ha b hb hab
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2 (Finset.mem_toList.mp hb)

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Total coherent action on a physical pair (invalid self-bonds are identities,
and never occur in a brickwork word). -/
def simulationPairVectorStep (p : Site × Site) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) :=
  if h : p.1 ≠ p.2 then pauliSamplerFixed p.1 p.2 h U ψ else ψ

def simulationPhysicalWordEvolution (gates : Site × Site → TwoQubitUnitary)
    (word : List (Site × Site)) (ψ : PauliString Site → ℝ) :=
  word.foldl (fun ψ p => simulationPairVectorStep p (gates p) ψ) ψ

/-- Actual coefficient action for a physical matching is independent of ordering. -/
theorem simulationPhysicalWord_perm (gates : Site × Site → TwoQubitUnitary)
    (word other : List (Site × Site)) (hp : word.Perm other)
    (hv : ∀ p ∈ word, p.1 ≠ p.2)
    (hm : ∀ p ∈ word, ∀ q ∈ word, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
    (ψ : PauliString Site → ℝ) :
    simulationPhysicalWordEvolution gates word ψ = simulationPhysicalWordEvolution gates other ψ := by
  apply hp.foldl_eq'
  intro p hpp q hqq v
  by_cases he : p=q
  · subst q
    rfl
  · have h1 := hv p hpp
    have h2 := hv q hqq
    obtain ⟨h3,h4,h5,h6⟩ := hm p hpp q hqq he
    simp only [simulationPairVectorStep,dif_pos h1,dif_pos h2]
    exact (pauliSamplerFixed_commute p.1 p.2 q.1 q.2 h1 h2 h3 h4 h5 h6
      (gates p) (gates q) v).symm

/-- The precise two lists traversed by the support/cost implementation have
identical quantum coefficient action for all physical gate realizations. -/
theorem simulationBrickwork_outside_first (c d t : ℕ) (R : ℝ)
    (gates : BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (ψ : PauliString (BrickworkSite c) → ℝ) :
    simulationPhysicalWordEvolution gates (simulationBrickworkLayer c t).toList ψ =
      simulationPhysicalWordEvolution gates
        ((simulationBrickworkLayer c t \ simulationRetainedLayer c d t R).toList ++
          (simulationRetainedLayer c d t R).toList) ψ := by
  apply simulationPhysicalWord_perm gates _ _
    (simulationOutsideRetained_perm _ _ (Finset.filter_subset _ _))
  · intro p hp
    exact simulationBrickworkLayer_distinct c t p (Finset.mem_toList.mp hp)
  · intro p hp q hq he
    exact simulationBrickworkLayer_matching c t p q
      (Finset.mem_toList.mp hp) (Finset.mem_toList.mp hq) he

/-- The physical chronological list in each layer. -/
def simulationChronologicalLayer (c t : ℕ) : List (BrickworkSite c × BrickworkSite c) :=
  if t%2=1 then brickworkOddBonds c else brickworkEvenBonds c

lemma simulationChronologicalLayer_nodup (c t : ℕ) :
    (simulationChronologicalLayer c t).Nodup := by
  unfold simulationChronologicalLayer
  split_ifs
  · apply List.nodup_ofFn.mpr
    intro a b h
    exact congrArg (fun p => p.1.1) h
  · apply List.nodup_ofFn.mpr
    intro a b h
    have he := congrArg (fun p => p.1.1.val) h
    exact Fin.ext he

/-- Reordering starts from the existing chronological odd/even layer itself,
not only from an arbitrary enumeration of its gate set. -/
theorem simulationChronological_outside_first (c d t : ℕ) (R : ℝ)
    (gates : BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (ψ : PauliString (BrickworkSite c) → ℝ) :
    simulationPhysicalWordEvolution gates (simulationChronologicalLayer c t) ψ =
      simulationPhysicalWordEvolution gates
        ((simulationBrickworkLayer c t \ simulationRetainedLayer c d t R).toList ++
          (simulationRetainedLayer c d t R).toList) ψ := by
  have he : (simulationChronologicalLayer c t).toFinset=simulationBrickworkLayer c t := by
    unfold simulationChronologicalLayer simulationBrickworkLayer
    split_ifs <;> rfl
  have hp := (List.toFinset_toList (simulationChronologicalLayer_nodup c t)).symm
  rw [he] at hp
  rw [← simulationBrickwork_outside_first c d t R gates ψ]
  apply simulationPhysicalWord_perm gates _ _ hp
  · intro p hp
    apply simulationBrickworkLayer_distinct c t p
    rw [←he]
    exact List.mem_toFinset.mpr hp
  · intro p hp q hq hne
    apply simulationBrickworkLayer_matching c t p q
    · rw [←he]; exact List.mem_toFinset.mpr hp
    · rw [←he]; exact List.mem_toFinset.mpr hq
    · exact hne

end
end Fluctuations
