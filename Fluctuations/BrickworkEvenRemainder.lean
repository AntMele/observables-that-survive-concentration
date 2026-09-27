import Fluctuations.EndpointLumpability

/-! The concrete even matching with one selected bond removed. -/

namespace Fluctuations

lemma brickworkEvenBond_disjoint {c : ℕ} (a b : Fin c) (hba : b ≠ a) :
    (brickworkEvenBond b).1 ≠ (brickworkEvenBond a).1 ∧
    (brickworkEvenBond b).1 ≠ (brickworkEvenBond a).2 ∧
    (brickworkEvenBond b).2 ≠ (brickworkEvenBond a).1 ∧
    (brickworkEvenBond b).2 ≠ (brickworkEvenBond a).2 := by
  simpa [brickworkEvenBond] using hba

lemma brickworkEvenBonds_take_mem {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).take a.val) :
    ∃ b : Fin c, b ≠ a ∧ brickworkEvenBond b = p := by
  obtain ⟨k,hk,hp⟩ := List.mem_take_iff_getElem.mp hp
  have hka : k < a.val := (lt_min_iff.mp hk).1
  have hkc : k < c := hka.trans a.isLt
  refine ⟨⟨k,hkc⟩, ?_, ?_⟩
  · intro h
    have hh := congrArg Fin.val h
    change k = a.val at hh
    omega
  · simpa [brickworkEvenBonds] using hp

lemma brickworkEvenBonds_drop_mem {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).drop (a.val+1)) :
    ∃ b : Fin c, b ≠ a ∧ brickworkEvenBond b = p := by
  obtain ⟨k,hk,hp⟩ := List.mem_iff_getElem.mp hp
  have hkc : a.val+1+k < c := by
    simp only [List.length_drop, brickworkEvenBonds, List.length_ofFn] at hk
    omega
  refine ⟨⟨a.val+1+k,hkc⟩, ?_, ?_⟩
  · intro h
    have hh := congrArg Fin.val h
    change a.val+1+k = a.val at hh
    omega
  · simpa [List.getElem_drop, brickworkEvenBonds] using hp

/-- Every remaining gate in the selected even matching is a different bond. -/
lemma brickworkEvenRemainder_mem {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).take a.val ++ (brickworkEvenBonds c).drop (a.val+1)) :
    ∃ b : Fin c, b ≠ a ∧ brickworkEvenBond b = p := by
  rcases List.mem_append.mp hp with hp | hp
  · exact brickworkEvenBonds_take_mem a p hp
  · exact brickworkEvenBonds_drop_mem a p hp

theorem brickworkEvenRemainder_adjacent {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).take a.val ++ (brickworkEvenBonds c).drop (a.val+1)) :
    brickworkRank p.2 = brickworkRank p.1 + 1 := by
  obtain ⟨b,_,rfl⟩ := brickworkEvenRemainder_mem a p hp
  simp [brickworkEvenBond, brickworkRank]
  omega

theorem brickworkEvenRemainder_misses {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).take a.val ++ (brickworkEvenBonds c).drop (a.val+1)) :
    p.1 ≠ (a.castSucc,1) ∧ p.1 ≠ (a.succ,0) ∧
      p.2 ≠ (a.castSucc,1) ∧ p.2 ≠ (a.succ,0) := by
  obtain ⟨b,hb,rfl⟩ := brickworkEvenRemainder_mem a p hp
  exact brickworkEvenBond_disjoint a b hb

/-- Prefix disjointness in the orientation used to move the fixed gate first. -/
theorem brickworkEvenPrefix_misses {c : ℕ} (a : Fin c)
    (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ (brickworkEvenBonds c).take a.val) :
    (a.castSucc,1) ≠ p.1 ∧ (a.castSucc,1) ≠ p.2 ∧
      (a.succ,0) ≠ p.1 ∧ (a.succ,0) ≠ p.2 := by
  obtain ⟨b,hb,rfl⟩ := brickworkEvenBonds_take_mem a p hp
  have h := brickworkEvenBond_disjoint a b hb
  exact ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩

end Fluctuations
