import Fluctuations.PauliString
import Fluctuations.EndpointLumpability
import Fluctuations.PauliFixedLocal
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace Fluctuations
noncomputable section

section ProductPairing
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma pauliSpectatorProduct (w : Site → Fin 4 → ℝ) (i j : Site) (P : Site → Fin 4) :
    (∏ s ∈ (Finset.univ.erase i).erase j, w s (P s)) =
      ∏ s : PairSpectator i j, w s (P s) := by
  exact Finset.prod_subtype _ (by intro s; simp [and_comm]) _

/-- Exact finite input/output factorization for a local kernel acting on a
product Pauli law, tested against a product observable. -/
theorem pauliPairEvolution_product_pairing (f w : Site → Fin 4 → ℝ)
    (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ) :
    (∑ Q, pauliProductWeight f Q * pauliPairEvolution i j K (pauliProductWeight w) Q) =
      (∑ q : TwoQubitPauliLabel, (f i q.1 * f j q.2) *
        ∑ p : TwoQubitPauliLabel, K q p * (w i p.1 * w j p.2)) *
      ∏ s : PairSpectator i j, ∑ p : Fin 4, f s p * w s p := by
  simp_rw [pauliProductWeight_split f i j hij, pauliPairEvolution_product w i j hij,
    pauliSpectatorProduct]
  rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm, Fintype.sum_prod_type]
  have he (q : TwoQubitPauliLabel) (P : PairSpectator i j → Fin 4) :
      (pairSplitEquiv i j hij (Fin 4)).symm (q,P) i = q.1 := by
    simp [pairSplitEquiv]
  have he' (q : TwoQubitPauliLabel) (P : PairSpectator i j → Fin 4) :
      (pairSplitEquiv i j hij (Fin 4)).symm (q,P) j = q.2 := by
    simp [pairSplitEquiv, hij.symm]
  have hs (q : TwoQubitPauliLabel) (P : PairSpectator i j → Fin 4) (s : PairSpectator i j) :
      (pairSplitEquiv i j hij (Fin 4)).symm (q,P) s = P s := by
    simp [pairSplitEquiv, s.prop.1, s.prop.2]
  simp only [he,he',hs]
  simp_rw [mul_assoc, mul_left_comm (∏ s : PairSpectator i j, _)]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (s : PairSpectator i j) (p : Fin 4) => f s p * w s p)]
  simp only [Prod.mk.eta]
  ring

/-- Endpoint projection after an arbitrary local kernel at a product-law front.
Only the local identity-output exclusion and the explicit spectator marginals
are required; no restoration of the full shock distribution is asserted. -/
theorem pauliEndpointMass_pair_front (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1)
    (w : Site → Fin 4 → ℝ) (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (hout : ∀ s, s ≠ i → s ≠ j → w s = pauliShockMarginal rank (rank i) s)
    (hzero : (∑ p, K (0,0) p * (w i p.1 * w j p.2)) = 0) (v : Site) :
    pauliEndpointMass rank (pauliPairEvolution i j K (pauliProductWeight w)) (rank v) =
      if v = i then
        ∑ α : Fin 3, ∑ p, K (α.succ,0) p * (w i p.1 * w j p.2)
      else if v = j then
        ∑ γ : Fin 4, ∑ δ : Fin 3, ∑ p, K (γ,δ.succ) p * (w i p.1 * w j p.2)
      else 0 := by
  have hij : i ≠ j := by intro he; subst j; omega
  have hlt : rank i < rank j := by omega
  have hne : rank i ≠ rank j := ne_of_lt hlt
  change (∑ Q, pauliProductWeight (pauliEndpointMarginal rank (rank v)) Q *
    pauliPairEvolution i j K (pauliProductWeight w) Q) = _
  rw [pauliPairEvolution_product_pairing _ _ i j hij]
  have hp : ∏ s : PairSpectator i j, ∑ p : Fin 4,
      pauliEndpointMarginal rank (rank i) s p * w s p = 1 := by
    apply Finset.prod_eq_one
    intro s _
    rw [hout s s.prop.1 s.prop.2]
    have hsi : rank s ≠ rank i := fun he => s.prop.1 (hrank he)
    by_cases hs : rank s < rank i
    · norm_num [pauliEndpointMarginal, pauliShockMarginal, hs,
        pauliUniformWeight, Fin.sum_univ_succ]
    · norm_num [pauliEndpointMarginal, pauliShockMarginal, hs, hsi,
        pauliIdentityWeight, Fin.sum_univ_succ]
  by_cases hvi : v = i
  · subst v
    rw [if_pos rfl,hp,mul_one]
    simp [pauliEndpointMarginal, hne.symm, not_lt_of_ge hlt.le,
      pauliIdentityWeight, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · rw [if_neg hvi]
    by_cases hvj : v = j
    · subst v
      rw [if_pos rfl]
      have hp' : ∏ s : PairSpectator i j, ∑ p : Fin 4,
          pauliEndpointMarginal rank (rank j) s p * w s p = 1 := by
        convert hp using 1
        apply Finset.prod_congr rfl
        intro s _
        rw [← pauliEndpointMarginal_adjacent_away rank hrank i j hadj s s.prop.1 s.prop.2]
      rw [hp',mul_one]
      simp [pauliEndpointMarginal, hlt, Fintype.sum_prod_type, Fin.sum_univ_succ]
    · rw [if_neg hvj]
      have hvi' : rank v ≠ rank i := fun he => hvi (hrank he)
      have hvj' : rank v ≠ rank j := fun he => hvj (hrank he)
      by_cases hvlt : rank v < rank i
      · have hl : (∑ q : TwoQubitPauliLabel,
            (pauliEndpointMarginal rank (rank v) i q.1 *
              pauliEndpointMarginal rank (rank v) j q.2) *
            ∑ p, K q p * (w i p.1 * w j p.2)) = 0 := by
          simpa [pauliEndpointMarginal, show ¬rank i < rank v by omega,
            show ¬rank j < rank v by omega, hvi'.symm, hvj'.symm,
            pauliIdentityWeight, Fintype.sum_prod_type] using hzero
        rw [hl,zero_mul]
      · have hvgt : rank i < rank v := by omega
        have hz : ∏ s : PairSpectator i j, ∑ p : Fin 4,
            pauliEndpointMarginal rank (rank v) s p * w s p = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ (⟨v,hvi,hvj⟩ : PairSpectator i j))
          rw [hout v hvi hvj]
          norm_num [pauliEndpointMarginal, pauliShockMarginal,
            show ¬rank v < rank i by omega, hvi', pauliIdentityWeight,
            Fin.sum_univ_succ]
        rw [hz,mul_zero]

/-- The actual fixed-unitary transfer sends a left-front shock to endpoint
masses 1-A and A, although its full output need not be a shock law. -/
theorem pauliEndpointMass_fixed_left (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (U : TwoQubitUnitary) (v : Site) :
    pauliEndpointMass rank
      (pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank i)))
      (rank v) = if v = i then 1 - localPauliA U else if v = j then localPauliA U else 0 := by
  have hlt : rank i < rank j := by omega
  have hwi : pauliShockMarginal rank (rank i) i = pauliNonzeroWeight := by
    simp [pauliShockMarginal]
  have hwj : pauliShockMarginal rank (rank i) j = pauliIdentityWeight := by
    simp [pauliShockMarginal, not_lt_of_ge hlt.le, ne_of_gt hlt]
  have h := pauliEndpointMass_pair_front rank hrank i j hadj
    (pauliShockMarginal rank (rank i)) (localPauliSquaredKernel U)
    (by intros; rfl) (by rw [hwi,hwj]; exact localPauliLeftLaw_zero U) v
  simp only [hwi,hwj] at h
  change pauliEndpointMass rank
      (pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank i)))
      (rank v) = if v = i then ∑ α : Fin 3, localPauliLeftLaw U (α.succ,0)
        else if v = j then ∑ γ : Fin 4, ∑ δ : Fin 3, localPauliLeftLaw U (γ,δ.succ)
        else 0 at h
  simpa only [localPauliLeftLaw_left,localPauliLeftLaw_right] using h

/-- The actual right-front input sector has endpoint weights 1-B and B. -/
theorem pauliEndpointMass_fixed_right (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (U : TwoQubitUnitary) (v : Site) :
    pauliEndpointMass rank
      (pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank j)))
      (rank v) = if v = i then 1 - localPauliB U else if v = j then localPauliB U else 0 := by
  have hlt : rank i < rank j := by omega
  have hwi : pauliShockMarginal rank (rank j) i = pauliUniformWeight := by
    simp [pauliShockMarginal, hlt]
  have hwj : pauliShockMarginal rank (rank j) j = pauliNonzeroWeight := by
    simp [pauliShockMarginal]
  have h := pauliEndpointMass_pair_front rank hrank i j hadj
    (pauliShockMarginal rank (rank j)) (localPauliSquaredKernel U)
    (by intro s hsi hsj; exact (pauliShockMarginal_adjacent_away rank hrank i j hadj s hsi hsj).symm)
    (by rw [hwi,hwj]; exact localPauliRightLaw_zero U) v
  simp only [hwi,hwj] at h
  change pauliEndpointMass rank
      (pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank j)))
      (rank v) = if v = i then ∑ α : Fin 3, localPauliRightLaw U (α.succ,0)
        else if v = j then ∑ γ : Fin 4, ∑ δ : Fin 3, localPauliRightLaw U (γ,δ.succ)
        else 0 at h
  simpa only [localPauliRightLaw_left,localPauliRightLaw_right] using h

/-- Away from the front, a fixed unitary preserves the full shock law:
its local input is either all identity or fully uniform. -/
theorem pauliShock_fixed_away (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (U : TwoQubitUnitary)
    (u : Site) (hui : u ≠ i) (huj : u ≠ j) :
    pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank u)) =
      pauliShock rank (rank u) := by
  have hij : i ≠ j := by intro he; subst j; omega
  have hui' : rank u ≠ rank i := fun he => hui (hrank he)
  have huj' : rank u ≠ rank j := fun he => huj (hrank he)
  funext Q
  apply pauliPairEvolution_product_fixed _ i j hij
  intro q
  by_cases hu : rank u < rank i
  · simpa [pauliShockMarginal, show ¬rank i < rank u by omega,
      show ¬rank j < rank u by omega, hui'.symm, huj'.symm] using
      localPauliSquared_identity U q
  · simpa [pauliShockMarginal, show rank i < rank u by omega,
      show rank j < rank u by omega] using localPauliSquared_uniform U q

omit [Fintype Site] in
lemma pauliPairEvolution_weighted_sum {A : Type*} [Fintype A]
    (i j : Site) (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (a : A → ℝ) (w : A → (Site → Fin 4) → ℝ) :
    pauliPairEvolution i j K (fun P => ∑ u, a u * w u P) =
      fun Q => ∑ u, a u * pauliPairEvolution i j K (w u) Q := by
  funext Q
  simp only [pauliPairEvolution, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem pauliEndpointMass_fixed_delta (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (U : TwoQubitUnitary) (u v : Site) :
    pauliEndpointMass rank
        (pauliPairEvolution i j (localPauliSquaredKernel U) (pauliShock rank (rank u))) (rank v) -
      pauliEndpointMass rank
        (pauliPairEvolution i j localPauliHaarKernel (pauliShock rank (rank u))) (rank v) =
      (if u = i then localPauliA U - 4/5 else if u = j then localPauliB U - 4/5 else 0) *
        ((if v = j then 1 else 0) - (if v = i then 1 else 0)) := by
  have hij : i ≠ j := by intro he; subst j; omega
  rw [pauliEndpointMass_haar_pair rank hrank i j hadj]
  simp only [pauliEndpointMass_shock rank hrank, hrank.eq_iff]
  by_cases hui : u = i
  · subst u
    rw [pauliEndpointMass_fixed_left rank hrank i j hadj]
    by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp [hvi,hvj,hij,hij.symm] <;> ring
  · by_cases huj : u = j
    · subst u
      rw [pauliEndpointMass_fixed_right rank hrank i j hadj]
      by_cases hvi : v = i <;> by_cases hvj : v = j <;> simp [hvi,hvj,hij,hij.symm] <;> ring
    · rw [pauliShock_fixed_away rank hrank i j hadj U u hui huj,
        pauliEndpointMass_shock rank hrank]
      by_cases hvi : v = i <;> by_cases hvj : v = j <;>
        simp_all [Ne.symm hui,Ne.symm huj]

/-- Exact fixed-gate endpoint perturbation for an arbitrary full shock mixture.
The factor 1/4 is proved from the local orthogonal-transfer balance identity. -/
theorem pauliEndpointMass_fixed_mixture_delta (rank : Site → ℕ)
    (hrank : Function.Injective rank) (i j : Site) (hadj : rank j = rank i + 1)
    (U : TwoQubitUnitary) (a : Site → ℝ) (v : Site) :
    pauliEndpointMass rank
        (pauliPairEvolution i j (localPauliSquaredKernel U)
          (fun P => ∑ u, a u * pauliShock rank (rank u) P)) (rank v) -
      pauliEndpointMass rank
        (pauliPairEvolution i j localPauliHaarKernel
          (fun P => ∑ u, a u * pauliShock rank (rank u) P)) (rank v) =
      (a i - a j / 4) * (localPauliA U - 4/5) *
        ((if v = j then 1 else 0) - (if v = i then 1 else 0)) := by
  have hij : i ≠ j := by intro he; subst j; omega
  rw [pauliPairEvolution_weighted_sum,pauliPairEvolution_weighted_sum,
    pauliEndpointMass_sum,pauliEndpointMass_sum,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub,pauliEndpointMass_fixed_delta rank hrank i j hadj]
  have he (u : Site) :
      a u * ((if u = i then localPauliA U - 4/5 else if u = j then localPauliB U - 4/5 else 0) *
        ((if v = j then 1 else 0) - (if v = i then 1 else 0))) =
      (if u = i then a i * (localPauliA U - 4/5) else 0) *
        ((if v = j then 1 else 0) - (if v = i then 1 else 0)) +
      (if u = j then a j * (localPauliB U - 4/5) else 0) *
        ((if v = j then 1 else 0) - (if v = i then 1 else 0)) := by
    by_cases hui : u = i <;> by_cases huj : u = j <;> simp_all <;> ring
  simp_rw [he,Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [localPauliB_eq_one_sub_quarter_A]
  ring

end ProductPairing
lemma brickworkCellProjection_siteMixture (c : ℕ) (m : Fin (c+1) → ℝ) :
    brickworkCellProjection m = fun P => ∑ u : BrickworkSite c,
      ((if u.2 = 0 then (1/5 : ℝ) else 4/5) * m u.1) *
        pauliShock brickworkRank (brickworkRank u) P := by
  funext P
  simp only [brickworkCellProjection,Fintype.sum_prod_type,Fin.sum_univ_two,
    brickworkCellShock,brickworkRank,Fin.val_zero,Fin.val_one,add_zero,
    if_true,show (1 : Fin 2) ≠ 0 by decide,if_false]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Actual fixed-gate cell-mass perturbation on the incoming full cell-shock
mixture. The scalar is exactly the past gradient from the manuscript. -/
theorem brickworkFixedPair_cell_delta (c : ℕ) (a : Fin c) (m : Fin (c+1) → ℝ)
    (U : TwoQubitUnitary) (b : Fin (c+1)) :
    brickworkEndpointCellMass
        (pauliPairEvolution (a.castSucc,1) (a.succ,0) (localPauliSquaredKernel U)
          (brickworkCellProjection m)) b -
      brickworkEndpointCellMass
        (pauliPairEvolution (a.castSucc,1) (a.succ,0) localPauliHaarKernel
          (brickworkCellProjection m)) b =
      ((4/5 : ℝ) * m a.castSucc - (1/20 : ℝ) * m a.succ) *
        (localPauliA U - 4/5) * ((if b = a.succ then 1 else 0) - (if b = a.castSucc then 1 else 0)) := by
  have hadj : brickworkRank (a.succ,(0 : Fin 2)) = brickworkRank (a.castSucc,(1 : Fin 2)) + 1 := by
    simp [brickworkRank]
    omega
  have h (v : BrickworkSite c) := pauliEndpointMass_fixed_mixture_delta brickworkRank
    (brickworkRank_injective c) (a.castSucc,1) (a.succ,0) hadj U
    (fun u : BrickworkSite c => (if u.2 = 0 then (1/5 : ℝ) else 4/5) * m u.1) v
  rw [← brickworkCellProjection_siteMixture] at h
  have h0 := h (b,0)
  have h1 := h (b,1)
  simp only [Prod.mk.injEq,show (1 : Fin 2) ≠ 0 by decide,Fin.zero_ne_one,if_false,if_true,
    and_true,and_false] at h0 h1
  simp only [brickworkEndpointCellMass]
  change _ + _ - (_ + _) = _
  have he0 : brickworkRank (b,(0 : Fin 2)) = 2*b.val := by simp [brickworkRank]
  have he1 : brickworkRank (b,(1 : Fin 2)) = 2*b.val+1 := by simp [brickworkRank]
  rw [he0] at h0
  rw [he1] at h1
  nlinarith [h0,h1]

end
end Fluctuations
