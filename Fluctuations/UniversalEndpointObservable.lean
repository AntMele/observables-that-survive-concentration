import Fluctuations.EndpointLumpability
import Fluctuations.PauliEndpointObservable

/-! Universal endpoint Pauli-sign observable after the final odd Haar layer. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section

section General
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

omit [DecidableEq Site] in
/-- The product endpoint observable is the usual rightmost-nonzero indicator. -/
theorem pauliEndpointIndicator_eq_ite (rank : Site → ℕ) (hrank : Function.Injective rank)
    (s : Site) (P : Site → Fin 4) :
    pauliEndpointIndicator rank (rank s) P =
      if P s ≠ 0 ∧ ∀ t, rank s < rank t → P t = 0 then 1 else 0 := by
  unfold pauliEndpointIndicator pauliProductWeight
  split_ifs with h
  · apply Finset.prod_eq_one
    intro t _
    by_cases ht : rank t < rank s
    · simp [pauliEndpointMarginal, ht]
    · by_cases he : rank t = rank s
      · have hts : t = s := hrank he
        subst t
        simp [pauliEndpointMarginal, h.1]
      · have hz : P t = 0 := h.2 t (by omega)
        simp [pauliEndpointMarginal, ht, he, pauliIdentityWeight, hz]
  · by_cases hs : P s = 0
    · exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [pauliEndpointMarginal, hs])
    · have hex : ∃ t, rank s < rank t ∧ P t ≠ 0 := by
        by_contra hn
        apply h
        refine ⟨hs, ?_⟩
        intro t ht
        by_contra hp
        exact hn ⟨t,ht,hp⟩
      obtain ⟨t,ht,hp⟩ := hex
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      simp [pauliEndpointMarginal, not_lt_of_ge ht.le, ne_of_gt ht,
        pauliIdentityWeight, hp]

omit [Fintype Site] in
lemma pauliPairEvolution_one (i j : Site) :
    pauliPairEvolution i j localPauliHaarKernel (fun _ => 1) = fun _ => 1 := by
  funext P
  simpa [pauliPairEvolution] using pauliHaar_one_product (P i,P j)

/-- The actual finite Pauli Haar update preserves the sum of arbitrary weights. -/
theorem pauliPairEvolution_totalMass (i j : Site) (hij : i ≠ j)
    (w : (Site → Fin 4) → ℝ) :
    (∑ P, pauliPairEvolution i j localPauliHaarKernel w P) = ∑ P, w P := by
  have h := pauliPairEvolution_selfAdjoint i j hij (fun _ => 1) w
  simpa only [one_mul, pauliPairEvolution_one] using h

lemma pauliLayerEvolution_totalMass (bs : List (Site × Site))
    (hb : ∀ p ∈ bs, p.1 ≠ p.2) (w : (Site → Fin 4) → ℝ) :
    (∑ P, pauliLayerEvolution bs w P) = ∑ P, w P := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    rw [pauliLayerEvolution, ih (fun p hp => hb p (by simp [hp])),
      pauliPairEvolution_totalMass i j (hb (i,j) (by simp))]


end General

section Brickwork

lemma brickworkRank_last_le (c : ℕ) (s : BrickworkSite c) :
    brickworkRank s ≤ brickworkRank (Fin.last c, (1 : Fin 2)) := by
  have ha := s.1.isLt
  have hb := s.2.isLt
  simp only [brickworkRank, Fin.val_last, Fin.val_one]
  omega

lemma brickworkRank_above_last_left (c : ℕ) (s : BrickworkSite c) :
    brickworkRank (Fin.last c, (0 : Fin 2)) < brickworkRank s ↔
      s = (Fin.last c,1) := by
  constructor
  · intro h
    have ha := s.1.isLt
    have hb := s.2.isLt
    simp only [brickworkRank, Fin.val_last, Fin.val_zero] at h
    apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_last, Fin.val_one] <;> omega
  · rintro rfl
    simp [brickworkRank]

lemma pauliEndpointIndicator_last_right (c : ℕ) (P : BrickworkSite c → Fin 4) :
    pauliEndpointIndicator brickworkRank (2*c+1) P =
      if P (Fin.last c,1) = 0 then 0 else 1 := by
  change pauliEndpointIndicator brickworkRank (brickworkRank (Fin.last c,1)) P = _
  rw [pauliEndpointIndicator_eq_ite brickworkRank (brickworkRank_injective c)]
  have he : (∀ t : BrickworkSite c, brickworkRank (Fin.last c,1) < brickworkRank t → P t = 0) := by
    intro t ht
    exact False.elim (not_lt_of_ge (brickworkRank_last_le c t) ht)
  by_cases hp : P (Fin.last c,1) = 0
  · rw [if_neg (by intro h; exact h.1 hp), if_pos hp]
  · rw [if_pos ⟨hp,he⟩, if_neg hp]

lemma pauliEndpointIndicator_last_left (c : ℕ) (P : BrickworkSite c → Fin 4) :
    pauliEndpointIndicator brickworkRank (2*c) P =
      (if P (Fin.last c,0) = 0 then 0 else 1) * pauliIdentityWeight (P (Fin.last c,1)) := by
  have h := pauliEndpointIndicator_eq_ite brickworkRank (brickworkRank_injective c)
    (Fin.last c,0) P
  have he : (∀ t : BrickworkSite c, brickworkRank (Fin.last c,0) < brickworkRank t → P t = 0) ↔
      P (Fin.last c,1) = 0 := by
    constructor
    · intro hh
      exact hh _ ((brickworkRank_above_last_left c _).mpr rfl)
    · intro hh t ht
      simpa only [(brickworkRank_above_last_left c t).mp ht] using hh
  simp only [he] at h
  by_cases h₀ : P (Fin.last c,0) = 0 <;> by_cases h₁ : P (Fin.last c,1) = 0 <;>
    simpa [brickworkRank, pauliIdentityWeight, h₀, h₁] using h

set_option maxRecDepth 2048 in
lemma pauliHaar_endpoint_sign (p : TwoQubitPauliLabel) :
    (∑ q : TwoQubitPauliLabel, localPauliHaarKernel p q * pauliEndpointSign q.2) =
      1 - (16/15 : ℝ) *
        ((if p.1 = 0 then 0 else 1) * pauliIdentityWeight p.2 +
          (if p.2 = 0 then 0 else 1)) := by
  have hsign : pauliEndpointSign = ![(1 : ℝ),-1,-1,1] := by
    funext q
    fin_cases q <;> norm_num [pauliEndpointSign, Fin.ext_iff]
  rw [hsign]
  rcases p with ⟨p₁,p₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight]

/-- One final Haar gate gives the exact last-site sign observable for every
incoming Pauli-string weight. -/
theorem brickworkLastPair_sign (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      pauliPairEvolution (Fin.last c,0) (Fin.last c,1) localPauliHaarKernel w P) =
      (∑ P, w P) - (16/15 : ℝ) * brickworkEndpointCellMass w (Fin.last c) := by
  have hij : (Fin.last c, (0 : Fin 2)) ≠ (Fin.last c,1) := by simp
  rw [pauliPairEvolution_selfAdjoint _ _ hij]
  have he (P : BrickworkSite c → Fin 4) :
      pauliPairEvolution (Fin.last c,0) (Fin.last c,1) localPauliHaarKernel
        (fun Q => pauliEndpointSign (Q (Fin.last c,1))) P =
      1 - (16/15 : ℝ) * (pauliEndpointIndicator brickworkRank (2*c) P +
        pauliEndpointIndicator brickworkRank (2*c+1) P) := by
    simp only [pauliPairEvolution, pauliPairReplace, Function.update_self]
    rw [pauliEndpointIndicator_last_left, pauliEndpointIndicator_last_right]
    exact pauliHaar_endpoint_sign (P (Fin.last c,0),P (Fin.last c,1))
  simp only [he]
  simp [brickworkEndpointCellMass, pauliEndpointMass, sub_mul, mul_add, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma brickworkLastPair_cellMass (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    brickworkEndpointCellMass
      (pauliPairEvolution (Fin.last c,0) (Fin.last c,1) localPauliHaarKernel w)
      (Fin.last c) = brickworkEndpointCellMass w (Fin.last c) := by
  change pauliEndpointMass brickworkRank _ (brickworkRank (Fin.last c,0)) +
    pauliEndpointMass brickworkRank _ (brickworkRank (Fin.last c,1)) = _
  rw [pauliEndpointMass_haar_pair brickworkRank (brickworkRank_injective c) _ _ (by simp [brickworkRank]),
    pauliEndpointMass_haar_pair brickworkRank (brickworkRank_injective c) _ _ (by simp [brickworkRank])]
  have hn : brickworkRank (Fin.last c, (1 : Fin 2)) ≠ brickworkRank (Fin.last c,0) := by
    simp [brickworkRank]
  simp only [if_neg hn]
  change (1/5 : ℝ)*_+(4/5 : ℝ)*_ = _
  unfold brickworkEndpointCellMass
  simp only [brickworkRank, Fin.val_last, Fin.val_zero, Fin.val_one, add_zero]
  ring

/-- A full odd layer makes the final-site Pauli sign depend only on endpoint-cell
mass, even for correlated or signed incoming distributions. -/
theorem brickworkOdd_sign (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      pauliLayerEvolution (brickworkOddBonds c) w P) =
      (∑ P, w P) - (16/15 : ℝ) * brickworkEndpointCellMass w (Fin.last c) := by
  let bs : List (BrickworkSite c × BrickworkSite c) :=
    List.ofFn (fun a : Fin c => brickworkOddBond a.castSucc)
  have hs : brickworkOddBonds c = bs ++ [( (Fin.last c,0),(Fin.last c,1))] := by
    simpa only [bs, List.concat_eq_append, brickworkOddBond] using
      List.ofFn_succ' (brickworkOddBond (c := c))
  have hf : pauliLayerEvolution (brickworkOddBonds c) w =
      pauliPairEvolution (Fin.last c,0) (Fin.last c,1) localPauliHaarKernel
        (pauliLayerEvolution bs w) := by
    rw [hs, pauliLayerEvolution_append]
    rfl
  have hm : (∑ P, pauliLayerEvolution bs w P) = ∑ P, w P := by
    apply pauliLayerEvolution_totalMass
    intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkOddBond]
  have hc : brickworkEndpointCellMass (pauliLayerEvolution bs w) (Fin.last c) =
      brickworkEndpointCellMass w (Fin.last c) := by
    rw [← brickworkLastPair_cellMass c, ← hf, brickworkEndpointCellMass_odd]
  rw [hf, brickworkLastPair_sign, hm, hc]

lemma brickworkOdd_totalMass (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliLayerEvolution (brickworkOddBonds c) w P) = ∑ P, w P := by
  apply pauliLayerEvolution_totalMass
  intro p hp
  have h := brickworkOddBonds_adjacent c p hp
  intro he
  rw [he] at h
  omega

lemma brickworkEven_totalMass (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliLayerEvolution (brickworkEvenBonds c) w P) = ∑ P, w P := by
  apply pauliLayerEvolution_totalMass
  intro p hp
  have h := brickworkEvenBonds_adjacent c p hp
  intro he
  rw [he] at h
  omega

lemma brickworkPeriod_totalMass (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, brickworkPeriod c w P) = ∑ P, w P := by
  rw [brickworkPeriod, brickworkOdd_totalMass, brickworkEven_totalMass]

lemma brickworkPeriod_iterate_totalMass (c n : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, (brickworkPeriod c)^[n] w P) = ∑ P, w P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', brickworkPeriod_totalMass, ih]

lemma brickworkPeriod_sign (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) * brickworkPeriod c w P) =
      (∑ P, w P) - (16/15 : ℝ) * brickworkEndpointCellMass (brickworkPeriod c w) (Fin.last c) := by
  rw [brickworkPeriod, brickworkOdd_sign, brickworkEndpointCellMass_odd,
    brickworkEven_totalMass]

/-- The actual final Pauli-sign expectation is the reflecting endpoint-chain
observable, universally over the incoming full Pauli-string distribution. -/
theorem brickworkIterateOdd_sign (c n : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      (brickworkPeriod c)^[n] (pauliLayerEvolution (brickworkOddBonds c) w) P) =
      (∑ P, w P) - (16/15 : ℝ) *
        (endpointMarkov c ^ n).mulVec (brickworkEndpointCellMass w) (Fin.last c) := by
  cases n with
  | zero => simpa using brickworkOdd_sign c w
  | succ n =>
    rw [Function.iterate_succ_apply', brickworkPeriod_sign,
      brickworkPeriod_iterate_totalMass, brickworkOdd_totalMass]
    rw [← Function.iterate_succ_apply' (brickworkPeriod c) n,
      brickworkEndpointCellMass_iterate_odd]

end Brickwork

end
end Fluctuations
