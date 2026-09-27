import Fluctuations.PauliFixedGate
import Fluctuations.UniversalEndpointObservable
import Fluctuations.EndpointPerturbation

open scoped BigOperators Matrix
namespace Fluctuations
noncomputable section

section TotalMass
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- A local column-stochastic transfer preserves the full Pauli-string mass. -/
lemma pauliPairEvolution_totalMass_of_columns (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (hK : ∀ p, (∑ q, K q p) = 1) (w : (Site → Fin 4) → ℝ) :
    (∑ Q, pauliPairEvolution i j K w Q) = ∑ P, w P := by
  have he : (∑ z : (Site → Fin 4) × TwoQubitPauliLabel,
      K (z.1 i,z.1 j) z.2 * w (pauliPairReplace i j z.1 z.2)) =
      ∑ z : (Site → Fin 4) × TwoQubitPauliLabel, K z.2 (z.1 i,z.1 j) * w z.1 := by
    apply Fintype.sum_equiv (pauliPairSwapEquiv i j hij)
    rintro ⟨P,p⟩
    simp [pauliPairSwapEquiv,pauliPairReplace,hij]
  conv_lhs at he => rw [Fintype.sum_prod_type]
  conv_rhs at he => rw [Fintype.sum_prod_type]
  simp only [pauliPairEvolution]
  rw [he]
  simp_rw [← Finset.sum_mul,hK,one_mul]

lemma pauliPairEvolution_fixed_totalMass (i j : Site) (hij : i ≠ j)
    (U : TwoQubitUnitary) (w : (Site → Fin 4) → ℝ) :
    (∑ Q, pauliPairEvolution i j (localPauliSquaredKernel U) w Q) = ∑ P, w P :=
  pauliPairEvolution_totalMass_of_columns i j hij _
    (fun p => twoQubitPauliTransfer_column_sq p U) w

end TotalMass

/-- Universal propagation of a proved adjacent-cell perturbation through the
remaining full Haar periods. This applies even to correlated Pauli weights. -/
theorem brickworkFuture_cell_delta (c r : ℕ) (a : Fin c)
    (w v : (BrickworkSite c → Fin 4) → ℝ) (η : ℝ)
    (hδ : ∀ b, brickworkEndpointCellMass w b - brickworkEndpointCellMass v b =
      η * ((if b = a.succ then 1 else 0) - (if b = a.castSucc then 1 else 0)))
    (b : Fin (c+1)) :
    brickworkEndpointCellMass
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c) w)) b -
      brickworkEndpointCellMass
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c) v)) b =
      η * ((endpointMarkov c ^ r) b a.succ - (endpointMarkov c ^ r) b a.castSucc) := by
  rw [brickworkEndpointCellMass_iterate_odd,brickworkEndpointCellMass_iterate_odd]
  simp only [Matrix.mulVec,dotProduct]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub,hδ,mul_sub,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

/-- The exact classical fixed-gate response, with its actual past and future
Q-power factors, before converting endpoint weight to the OTOC readout. -/
theorem brickworkFixedPair_future_gap (c s r : ℕ) (a : Fin c) (U : TwoQubitUnitary) :
    brickworkEndpointCellMass
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
          (pauliPairEvolution (a.castSucc,1) (a.succ,0) (localPauliSquaredKernel U)
            (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))))) (Fin.last c) -
      brickworkEndpointCellMass
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
          (pauliPairEvolution (a.castSucc,1) (a.succ,0) localPauliHaarKernel
            (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))))) (Fin.last c) =
      endpointPastFactor c s a * endpointFutureFactor c r a * (localPauliA U - 4/5) := by
  rw [brickworkFuture_cell_delta c r a _ _
    (endpointPastFactor c s a * (localPauliA U - 4/5))
    (by intro b; exact brickworkFixedPair_cell_delta c a _ U b)]
  rw [endpointFutureFactor]
  ring

/-- The last-site endpoint probability has the additional universal 4/5
factor restored by the final odd Haar layer. -/
theorem brickworkFixedPair_future_site_gap (c s r : ℕ) (a : Fin c) (U : TwoQubitUnitary) :
    pauliEndpointMass brickworkRank
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
          (pauliPairEvolution (a.castSucc,1) (a.succ,0) (localPauliSquaredKernel U)
            (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0)))))
        (brickworkRank (Fin.last c,(1 : Fin 2))) -
      pauliEndpointMass brickworkRank
        ((brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
          (pauliPairEvolution (a.castSucc,1) (a.succ,0) localPauliHaarKernel
            (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0)))))
        (brickworkRank (Fin.last c,(1 : Fin 2))) =
      (4/5) * endpointPastFactor c s a * endpointFutureFactor c r a * (localPauliA U - 4/5) := by
  have h := brickworkFixedPair_future_gap c s r a U
  rw [brickworkEndpointCellMass_iterate_odd,brickworkEndpointCellMass_iterate_odd] at h
  rw [pauliEndpointMass_iterate_odd,pauliEndpointMass_iterate_odd]
  norm_num
  nlinarith [h]

lemma brickworkFixedPair_site_delta (c s : ℕ) (a : Fin c) (U : TwoQubitUnitary)
    (v : BrickworkSite c) :
    pauliEndpointMass brickworkRank
        (pauliPairEvolution (a.castSucc,1) (a.succ,0) (localPauliSquaredKernel U)
          (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))) (brickworkRank v) -
      pauliEndpointMass brickworkRank
        (pauliPairEvolution (a.castSucc,1) (a.succ,0) localPauliHaarKernel
          (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))) (brickworkRank v) =
      (endpointPastFactor c s a * (localPauliA U - 4/5)) *
        ((if v = (a.succ,0) then 1 else 0) - (if v = (a.castSucc,1) then 1 else 0)) := by
  have hadj : brickworkRank (a.succ,(0 : Fin 2)) = brickworkRank (a.castSucc,(1 : Fin 2)) + 1 := by
    simp [brickworkRank]
    omega
  have h := pauliEndpointMass_fixed_mixture_delta brickworkRank (brickworkRank_injective c)
    (a.castSucc,1) (a.succ,0) hadj U
    (fun u : BrickworkSite c => (if u.2 = 0 then (1/5 : ℝ) else 4/5) *
      (endpointMarkov c ^ s) u.1 0) v
  rw [← brickworkCellProjection_siteMixture c (fun b => (endpointMarkov c ^ s) b 0)] at h
  dsimp only at h
  simp only [show (1 : Fin 2) ≠ 0 by decide,if_false,if_true] at h
  have hcoef : (4/5 : ℝ) * (endpointMarkov c ^ s) a.castSucc 0 -
      ((1/5 : ℝ) * (endpointMarkov c ^ s) a.succ 0) / 4 = endpointPastFactor c s a := by
    rw [endpointPastFactor]
    ring
  simpa only [hcoef] using h

/-- Actual final Pauli-sign response for a fixed even-layer gate, including
all the other gates of that matching and the complete remaining Haar future. -/
theorem brickworkFixedMatching_future_sign_gap (c s r : ℕ) (a : Fin c)
    (U : TwoQubitUnitary) (bs : List (BrickworkSite c × BrickworkSite c))
    (hadj : ∀ p ∈ bs, brickworkRank p.2 = brickworkRank p.1 + 1)
    (hmiss : ∀ p ∈ bs, p.1 ≠ (a.castSucc,1) ∧ p.1 ≠ (a.succ,0) ∧
      p.2 ≠ (a.castSucc,1) ∧ p.2 ≠ (a.succ,0)) :
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      (brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
        (pauliLayerEvolution bs (pauliPairEvolution (a.castSucc,1) (a.succ,0)
          (localPauliSquaredKernel U) (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))))) P) -
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      (brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c)
        (pauliLayerEvolution bs (pauliPairEvolution (a.castSucc,1) (a.succ,0)
          localPauliHaarKernel (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))))) P) =
      -(16/15 : ℝ) * endpointPastFactor c s a * endpointFutureFactor c r a * (localPauliA U - 4/5) := by
  let w := pauliPairEvolution (a.castSucc,1) (a.succ,0) (localPauliSquaredKernel U)
    (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))
  let v := pauliPairEvolution (a.castSucc,1) (a.succ,0) localPauliHaarKernel
    (brickworkCellProjection (fun b => (endpointMarkov c ^ s) b 0))
  have hij : (a.castSucc,(1 : Fin 2)) ≠ (a.succ,0) := by simp
  have hb : ∀ p ∈ bs, p.1 ≠ p.2 := by
    intro p hp he
    have hh := hadj p hp
    rw [he] at hh
    omega
  have htotal : (∑ P, pauliLayerEvolution bs w P) = ∑ P, pauliLayerEvolution bs v P := by
    rw [pauliLayerEvolution_totalMass bs hb,pauliLayerEvolution_totalMass bs hb]
    dsimp [w,v]
    rw [pauliPairEvolution_fixed_totalMass _ _ hij,pauliPairEvolution_totalMass _ _ hij]
  have hsite := pauliEndpointMass_layer_twoSite_difference brickworkRank (brickworkRank_injective c)
    bs hadj (a.castSucc,1) (a.succ,0) (endpointPastFactor c s a * (localPauliA U - 4/5)) w v
    (brickworkFixedPair_site_delta c s a U) hmiss
  have hcell (b : Fin (c+1)) :
      brickworkEndpointCellMass (pauliLayerEvolution bs w) b -
        brickworkEndpointCellMass (pauliLayerEvolution bs v) b =
      (endpointPastFactor c s a * (localPauliA U - 4/5)) *
        ((if b = a.succ then 1 else 0) - (if b = a.castSucc then 1 else 0)) := by
    have h0 := hsite (b,0)
    have h1 := hsite (b,1)
    simp only [Prod.mk.injEq,show (1 : Fin 2) ≠ 0 by decide,Fin.zero_ne_one,
      if_false,and_true,and_false] at h0 h1
    change _ + _ - (_ + _) = _
    simpa only [brickworkEndpointCellMass,brickworkRank,Fin.val_zero,Fin.val_one,add_zero]
      using (show (pauliEndpointMass brickworkRank (pauliLayerEvolution bs w) (brickworkRank (b,0)) +
        pauliEndpointMass brickworkRank (pauliLayerEvolution bs w) (brickworkRank (b,1))) -
        (pauliEndpointMass brickworkRank (pauliLayerEvolution bs v) (brickworkRank (b,0)) +
        pauliEndpointMass brickworkRank (pauliLayerEvolution bs v) (brickworkRank (b,1))) = _ by
        nlinarith [h0,h1])
  have hf := brickworkFuture_cell_delta c r a (pauliLayerEvolution bs w)
    (pauliLayerEvolution bs v) (endpointPastFactor c s a * (localPauliA U - 4/5)) hcell (Fin.last c)
  rw [brickworkEndpointCellMass_iterate_odd,brickworkEndpointCellMass_iterate_odd] at hf
  change (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      (brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c) (pauliLayerEvolution bs w)) P) -
    (∑ P, pauliEndpointSign (P (Fin.last c,1)) *
      (brickworkPeriod c)^[r] (pauliLayerEvolution (brickworkOddBonds c) (pauliLayerEvolution bs v)) P) = _
  rw [brickworkIterateOdd_sign,brickworkIterateOdd_sign,htotal]
  rw [endpointFutureFactor]
  nlinarith [hf]

end
end Fluctuations
