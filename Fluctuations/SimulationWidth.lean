import Fluctuations.EndpointEye
import Fluctuations.PauliBrickworkCircuit

/-! The retained eye and the coherent-support bound used by the conditional
sampler. Site sets below are actual supports, not bounds postulated for a
black-box algorithm. Averaging a gate removes its sites; fixing it adds them.
Outside gates are processed first, exactly as in the manuscript. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section

/-- The manuscript's (possibly asymmetric) diffusive radius. -/
def simulationSigma (d t ℓ : ℝ) : ℝ :=
  Real.sqrt (if t ≤ 5*ℓ/3 then t else d-t)

/-- Physical gates retained in a layer; positions are the left sites, one-based.
The parity condition selects the actual brickwork matching. -/
def simulationEyePositions (n d t : ℕ) (R : ℝ) : Finset ℤ :=
  (Finset.Icc 1 (n-1 : ℤ)).filter fun ℓ =>
    ℓ % 2 = (t : ℤ) % 2 ∧ (ℓ : ℝ) ≤ t ∧ (n:ℝ)-ℓ ≤ (d:ℝ)-t ∧
      t < d ∧ |(t:ℝ)-5*ℓ/3| ≤ R*simulationSigma d t ℓ

lemma simulationSigma_le_sqrt {d t ℓ : ℝ} (ht : 0 ≤ t) (htd : t ≤ d) :
    simulationSigma d t ℓ ≤ Real.sqrt d := by
  unfold simulationSigma
  split_ifs <;> exact Real.sqrt_le_sqrt (by linarith)

theorem simulationEyePositions_strip {n d t : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {ℓ : ℤ} (hℓ : ℓ ∈ simulationEyePositions n d t R) :
    |(ℓ:ℝ)-3*t/5| ≤ 3*R*Real.sqrt d/5 := by
  obtain ⟨_,_,_,_,htd,h⟩ := Finset.mem_filter.mp hℓ
  have hs := simulationSigma_le_sqrt (ℓ := (ℓ:ℝ))
    (d := (d:ℝ)) (t := (t:ℝ)) (by positivity) (by exact_mod_cast htd.le)
  have hm := mul_le_mul_of_nonneg_left hs hR
  rw [abs_le] at h ⊢
  constructor <;> linarith

/-- A completely explicit version of `W_R = O(R sqrt d)`. -/
theorem simulationEyePositions_card {n d t : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    ((simulationEyePositions n d t R).card : ℝ) ≤ 6*R*Real.sqrt d/5+1 := by
  let a : ℝ := 3*t/5-3*R*Real.sqrt d/5
  let b : ℝ := 3*t/5+3*R*Real.sqrt d/5
  have hab : a ≤ b := by
    dsimp [a,b]
    have h : 0 ≤ 3*R*Real.sqrt d/5 := by positivity
    linarith
  have hs : simulationEyePositions n d t R ⊆ evenLatticeInterval (2*a) (2*b) := by
    intro ℓ hℓ
    have h := simulationEyePositions_strip hR hℓ
    rw [abs_le] at h
    rw [mem_evenLatticeInterval]
    dsimp [a,b]
    constructor <;> linarith
  have hc : ((simulationEyePositions n d t R).card : ℝ) ≤
      ((evenLatticeInterval (2*a) (2*b)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  have hb := evenLatticeInterval_card_upper (a:=2*a) (b:=2*b) (by linarith)
  dsimp [a,b] at hb
  linarith

section Support
variable {Site : Type*} [DecidableEq Site]

/-- Sites touched by a finite set of physical two-site gates. -/
def simulationGateSites (gates : Finset (Site × Site)) : Finset Site :=
  gates.biUnion fun p => {p.1,p.2}

lemma mem_simulationGateSites {gates : Finset (Site × Site)} {x : Site} :
    x ∈ simulationGateSites gates ↔ ∃ p ∈ gates, x = p.1 ∨ x = p.2 := by
  simp [simulationGateSites]

lemma simulationGateSites_mono {a b : Finset (Site × Site)} (h : a ⊆ b) :
    simulationGateSites a ⊆ simulationGateSites b := by
  intro x hx
  obtain ⟨p,hp,hx⟩ := mem_simulationGateSites.mp hx
  exact mem_simulationGateSites.mpr ⟨p,h hp,hx⟩

theorem simulationGateSites_card (gates : Finset (Site × Site)) :
    (simulationGateSites gates).card ≤ 2*gates.card := by
  unfold simulationGateSites
  calc
    _ ≤ ∑ p ∈ gates, ({p.1,p.2} : Finset Site).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gates, 2 := Finset.sum_le_sum fun _ _ => by
      calc _ ≤ ({_} : Finset Site).card+1 := Finset.card_insert_le _ _
           _ = 2 := by simp
    _ = _ := by simp; omega

/-- The coherent set after outside gates have been measured and removed. -/
def simulationOutsideSupport (C : Finset Site) (outside : Finset (Site × Site)) : Finset Site :=
  C \ simulationGateSites outside

/-- The support after then processing a prefix of retained gates coherently. -/
def simulationRetainedSupport (C : Finset Site) (outside retained : Finset (Site × Site)) : Finset Site :=
  simulationOutsideSupport C outside ∪ simulationGateSites retained

/-- Each outside-gate update really deletes its two coherent sites. -/
theorem simulationOutsideSupport_insert (C : Finset Site) (gates : Finset (Site × Site))
    (p : Site × Site) :
    simulationOutsideSupport C (insert p gates) =
      simulationOutsideSupport C gates \ {p.1,p.2} := by
  ext x
  simp [simulationOutsideSupport, simulationGateSites]
  tauto

/-- Each fixed-gate update really includes its two sites in the coherent vector. -/
theorem simulationRetainedSupport_insert (C : Finset Site)
    (outside gates : Finset (Site × Site)) (p : Site × Site) :
    simulationRetainedSupport C outside (insert p gates) =
      simulationRetainedSupport C outside gates ∪ {p.1,p.2} := by
  ext x
  simp [simulationRetainedSupport,simulationGateSites]


/-- At the end of the outside-first layer, only retained or idle sites are coherent. -/
theorem simulationRetainedSupport_subset (C idle : Finset Site)
    (outside retained : Finset (Site × Site))
    (hcover : ∀ x : Site, x ∈ simulationGateSites outside ∨
      x ∈ simulationGateSites retained ∨ x ∈ idle) :
    simulationRetainedSupport C outside retained ⊆ simulationGateSites retained ∪ idle := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨_,hn⟩ := Finset.mem_sdiff.mp hx
    rcases hcover x with h | h | h
    · exact (hn h).elim
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ hx

/-- Explicit layer-end coherent width. This also applies to every retained prefix. -/
theorem simulationRetainedSupport_card (C idle : Finset Site)
    (outside retained pre : Finset (Site × Site)) (hp : pre ⊆ retained)
    (hcover : ∀ x : Site, x ∈ simulationGateSites outside ∨
      x ∈ simulationGateSites retained ∨ x ∈ idle) (hi : idle.card ≤ 2) :
    (simulationRetainedSupport C outside pre).card ≤ 2*retained.card+2 := by
  have hs : simulationRetainedSupport C outside pre ⊆
      simulationRetainedSupport C outside retained :=
    Finset.union_subset_union (by rfl) (simulationGateSites_mono hp)
  calc
    _ ≤ (simulationRetainedSupport C outside retained).card := Finset.card_le_card hs
    _ ≤ (simulationGateSites retained ∪ idle).card :=
      Finset.card_le_card (simulationRetainedSupport_subset C idle outside retained hcover)
    _ ≤ (simulationGateSites retained).card+idle.card := Finset.card_union_le _ _
    _ ≤ 2*retained.card+2 := Nat.add_le_add (simulationGateSites_card _) hi

/-- Temporarily adjoining the measured gate costs at most two more sites. -/
theorem simulationOutsideSupport_temporary_card (C : Finset Site)
    (outside : Finset (Site × Site)) (p : Site × Site) (W : ℕ)
    (hC : C.card ≤ 2*W+2) :
    (simulationOutsideSupport C outside ∪ {p.1,p.2}).card ≤ 2*W+4 := by
  have hs := Finset.card_le_card (Finset.sdiff_subset : C \ simulationGateSites outside ⊆ C)
  have hu := Finset.card_union_le (simulationOutsideSupport C outside) {p.1,p.2}
  have hp := (show ({p.1,p.2} : Finset Site).card ≤ 2 from by
    calc _ ≤ ({p.2} : Finset Site).card+1 := Finset.card_insert_le _ _
         _ = 2 := by simp)
  change (simulationOutsideSupport C outside).card ≤ C.card at hs
  omega

end Support

/-- Physical layer matching, indexed in exactly the existing quantum circuit. -/
def simulationBrickworkLayer (c t : ℕ) : Finset (BrickworkSite c × BrickworkSite c) :=
  if t % 2 = 1 then (brickworkOddBonds c).toFinset else (brickworkEvenBonds c).toFinset

def simulationIdleBoundary (c : ℕ) : Finset (BrickworkSite c) := {(0,0),(Fin.last c,1)}

/-- Every actual layer covers all sites except at most the two boundary sites. -/
theorem simulationBrickworkLayer_cover (c t : ℕ) (x : BrickworkSite c) :
    x ∈ simulationGateSites (simulationBrickworkLayer c t) ∨ x ∈ simulationIdleBoundary c := by
  unfold simulationBrickworkLayer
  split_ifs with ht
  · left
    apply mem_simulationGateSites.mpr
    refine ⟨brickworkOddBond x.1, ?_, ?_⟩
    · exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨x.1,rfl⟩)
    · rcases x with ⟨a,b⟩
      fin_cases b <;> simp [brickworkOddBond]
  · rcases x with ⟨a,b⟩
    fin_cases b
    · by_cases ha : a.val=0
      · right
        have he : a=0 := Fin.ext ha
        simp [simulationIdleBoundary,he]
      · left
        let j : Fin c := ⟨a.val-1,by have hh:=a.isLt; omega⟩
        refine mem_simulationGateSites.mpr ⟨brickworkEvenBond j,?_,Or.inr ?_⟩
        · simp [brickworkEvenBonds]
        · apply Prod.ext
          · apply Fin.ext
            dsimp [brickworkEvenBond,j]
            omega
          · rfl
    · by_cases ha : a.val=c
      · right
        have he : a=Fin.last c := Fin.ext ha
        simp [simulationIdleBoundary,he]
      · left
        let j : Fin c := ⟨a.val,by have hh:=a.isLt; omega⟩
        refine mem_simulationGateSites.mpr ⟨brickworkEvenBond j,?_,Or.inl ?_⟩
        · simp [brickworkEvenBonds]
        · rfl

theorem simulationBrickworkLayer_coherent_card (c t : ℕ) (C : Finset (BrickworkSite c))
    (retained : Finset (BrickworkSite c × BrickworkSite c))
    :
    (simulationRetainedSupport C (simulationBrickworkLayer c t \ retained) retained).card
      ≤ 2*retained.card+2 := by
  apply simulationRetainedSupport_card C (simulationIdleBoundary c) _ retained retained
    (by rfl) _ (by
      calc _ ≤ ({(Fin.last c,1)} : Finset (BrickworkSite c)).card+1 := Finset.card_insert_le _ _
           _ = 2 := by simp)
  intro x
  rcases simulationBrickworkLayer_cover c t x with h | h
  · obtain ⟨p,hp,hx⟩ := mem_simulationGateSites.mp h
    by_cases hpr : p ∈ retained
    · exact Or.inr (Or.inl (mem_simulationGateSites.mpr ⟨p,hpr,hx⟩))
    · exact Or.inl (mem_simulationGateSites.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpr⟩,hx⟩)
  · exact Or.inr (Or.inr h)

/-- One-based physical bond coordinate of the existing brickwork schedule. -/
def simulationBondPosition {c : ℕ} (p : BrickworkSite c × BrickworkSite c) : ℤ :=
  brickworkRank p.1 + 1

lemma simulationBrickworkLayer_position_injective (c t : ℕ) :
    Set.InjOn (simulationBondPosition (c:=c)) (simulationBrickworkLayer c t) := by
  intro p hp q hq he
  unfold simulationBrickworkLayer at hp hq
  split_ifs at hp hq with ht
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
    have hab : a=b := by
      apply Fin.ext
      simp only [simulationBondPosition,brickworkOddBond,brickworkRank,Fin.val_zero,
        add_zero] at he
      omega
    rw [hab]
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    obtain ⟨b,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hq)
    have hab : a=b := by
      apply Fin.ext
      simp only [simulationBondPosition,brickworkEvenBond,brickworkRank,
        Fin.coe_castSucc,Fin.val_one] at he
      omega
    rw [hab]

/-- Retained eye gates as actual physical pairs in the quantum circuit. -/
def simulationRetainedLayer (c d t : ℕ) (R : ℝ) :
    Finset (BrickworkSite c × BrickworkSite c) :=
  (simulationBrickworkLayer c t).filter fun p =>
    simulationBondPosition p ∈ simulationEyePositions (2*(c+1)) d t R

theorem simulationRetainedLayer_card {c d t : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    ((simulationRetainedLayer c d t R).card : ℝ) ≤ 6*R*Real.sqrt d/5+1 := by
  have hinj : Set.InjOn (simulationBondPosition (c:=c))
      (↑(simulationRetainedLayer c d t R)) := by
    intro p hp q hq he
    apply simulationBrickworkLayer_position_injective c t
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have hc : (simulationRetainedLayer c d t R).card ≤
      (simulationEyePositions (2*(c+1)) d t R).card := by
    rw [← Finset.card_image_iff.mpr hinj]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hp).2
  have hcr : ((simulationRetainedLayer c d t R).card : ℝ) ≤
      ((simulationEyePositions (2*(c+1)) d t R).card : ℝ) := by exact_mod_cast hc
  exact hcr.trans (simulationEyePositions_card hR)

/-- Critical depth gives the advertised `O(R sqrt n)` coherent width. -/
theorem simulationRetainedLayer_critical_card {c d t : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hd : (d:ℝ) = 5*(2*(c+1):ℕ)/3) :
    ((simulationRetainedLayer c d t R).card : ℝ) ≤
      2*R*Real.sqrt (2*(c+1):ℕ)+1 := by
  have hs : Real.sqrt (d:ℝ) ≤ (5/3)*Real.sqrt (2*(c+1):ℕ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hsq := Real.sq_sqrt (show 0 ≤ ((2*(c+1):ℕ):ℝ) by positivity)
      rw [hd]
      nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*R/5 by positivity)
  have hb := simulationRetainedLayer_card (c:=c) (d:=d) (t:=t) hR
  nlinarith

end
end Fluctuations
