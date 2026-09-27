import Fluctuations.PauliBrickwork

/-! Endpoint projection of arbitrary Pauli-string weights intertwines the actual
local Haar kernel with the two-site endpoint walk. No product-law hypothesis is used. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section

section PairAdjoint
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

omit [Fintype Site] in
lemma pauliPairReplace_replace (i j : Site) (hij : i ≠ j)
    (P : Site → Fin 4) (p q : TwoQubitPauliLabel) :
    pauliPairReplace i j (pauliPairReplace i j P p) q = pauliPairReplace i j P q := by
  funext s
  by_cases hsi : s = i
  · subst s; simp [pauliPairReplace, hij]
  by_cases hsj : s = j
  · subst s; simp [pauliPairReplace]
  simp [pauliPairReplace, Function.update_of_ne hsi, Function.update_of_ne hsj]

omit [Fintype Site] in
lemma pauliPairReplace_self (i j : Site) (P : Site → Fin 4) :
    pauliPairReplace i j P (P i,P j) = P := by
  simp [pauliPairReplace]

omit [Fintype Site] in
def pauliPairSwapEquiv (i j : Site) (hij : i ≠ j) :
    ((Site → Fin 4) × TwoQubitPauliLabel) ≃ ((Site → Fin 4) × TwoQubitPauliLabel) where
  toFun z := (pauliPairReplace i j z.1 z.2, (z.1 i,z.1 j))
  invFun z := (pauliPairReplace i j z.1 z.2, (z.1 i,z.1 j))
  left_inv z := by
    rcases z with ⟨P,p⟩
    apply Prod.ext
    · exact (pauliPairReplace_replace i j hij P p (P i,P j)).trans
        (pauliPairReplace_self i j P)
    · simp [pauliPairReplace, hij]
  right_inv z := by
    rcases z with ⟨P,p⟩
    apply Prod.ext
    · exact (pauliPairReplace_replace i j hij P p (P i,P j)).trans
        (pauliPairReplace_self i j P)
    · simp [pauliPairReplace, hij]

lemma localPauliHaarKernel_symm (p q : TwoQubitPauliLabel) :
    localPauliHaarKernel p q = localPauliHaarKernel q p := by
  unfold localPauliHaarKernel
  split_ifs <;> simp_all

/-- Reindexing actual input/output Pauli strings proves the Haar pair update is
self-adjoint for the finite counting pairing. -/
theorem pauliPairEvolution_selfAdjoint (i j : Site) (hij : i ≠ j)
    (f w : (Site → Fin 4) → ℝ) :
    (∑ Q, f Q * pauliPairEvolution i j localPauliHaarKernel w Q) =
      ∑ P, pauliPairEvolution i j localPauliHaarKernel f P * w P := by
  simp only [pauliPairEvolution, Finset.mul_sum, Finset.sum_mul]
  let F : ((Site → Fin 4) × TwoQubitPauliLabel) → ℝ := fun z =>
    f z.1 * (localPauliHaarKernel (z.1 i,z.1 j) z.2 * w (pauliPairReplace i j z.1 z.2))
  let H : ((Site → Fin 4) × TwoQubitPauliLabel) → ℝ := fun z =>
    localPauliHaarKernel (z.1 i,z.1 j) z.2 * f (pauliPairReplace i j z.1 z.2) * w z.1
  change (∑ P, ∑ p, F (P,p)) = ∑ P, ∑ p, H (P,p)
  rw [← Fintype.sum_prod_type F, ← Fintype.sum_prod_type H]
  apply Fintype.sum_equiv (pauliPairSwapEquiv i j hij)
  rintro ⟨P,p⟩
  simp only [F, H, pauliPairSwapEquiv, Equiv.coe_fn_mk, pauliPairReplace_replace i j hij,
    pauliPairReplace_self]
  simp only [pauliPairReplace, Function.update_self, Function.update_of_ne hij]
  rw [localPauliHaarKernel_symm]
  ring

end PairAdjoint

section Endpoint
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

def pauliEndpointMarginal (rank : Site → ℕ) (x : ℕ) (s : Site) (p : Fin 4) : ℝ :=
  if rank s < x then 1 else if rank s = x then (if p = 0 then 0 else 1)
  else pauliIdentityWeight p

/-- Indicator of a nonidentity Pauli string whose rightmost occupied site has rank x. -/
def pauliEndpointIndicator (rank : Site → ℕ) (x : ℕ) : (Site → Fin 4) → ℝ :=
  pauliProductWeight (pauliEndpointMarginal rank x)

/-- Endpoint masses of an arbitrary (possibly signed) Pauli-string weight. -/
def pauliEndpointMass (rank : Site → ℕ) (w : (Site → Fin 4) → ℝ) (x : ℕ) : ℝ :=
  ∑ P, pauliEndpointIndicator rank x P * w P

omit [Fintype Site] [DecidableEq Site] in
lemma pauliEndpointMarginal_adjacent_away (rank : Site → ℕ)
    (hrank : Function.Injective rank) (i j : Site) (hadj : rank j = rank i + 1)
    (s : Site) (hsi : s ≠ i) (hsj : s ≠ j) :
    pauliEndpointMarginal rank (rank i) s = pauliEndpointMarginal rank (rank j) s := by
  have hi : rank s ≠ rank i := fun h => hsi (hrank h)
  have hj : rank s ≠ rank j := fun h => hsj (hrank h)
  funext p
  by_cases hs : rank s < rank i
  · simp [pauliEndpointMarginal, hs, show rank s < rank j by omega]
  · simp [pauliEndpointMarginal, hs, hi, hj, show ¬rank s < rank j by omega]

lemma pauliHaar_endpoint_left (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      ((if p.1 = 0 then 0 else 1) * pauliIdentityWeight p.2)) =
      (1/5 : ℝ) * ((if q.1 = 0 then 0 else 1) * pauliIdentityWeight q.2) +
        (1/5 : ℝ) * (1 * (if q.2 = 0 then 0 else 1)) := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight]

lemma pauliHaar_endpoint_right (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      (1 * (if p.2 = 0 then 0 else 1))) =
      (4/5 : ℝ) * ((if q.1 = 0 then 0 else 1) * pauliIdentityWeight q.2) +
        (4/5 : ℝ) * (1 * (if q.2 = 0 then 0 else 1)) := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight]

lemma pauliHaar_one_product (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p * (1 * 1)) = 1 * 1 := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel]

/-- The dual local Haar update on endpoint indicators is computed directly. -/
theorem pauliEndpointIndicator_haar_pair (rank : Site → ℕ)
    (hrank : Function.Injective rank) (i j : Site) (hadj : rank j = rank i + 1)
    (x : ℕ) (Q : Site → Fin 4) :
    pauliPairEvolution i j localPauliHaarKernel (pauliEndpointIndicator rank x) Q =
      if x = rank i then (1/5 : ℝ) *
        (pauliEndpointIndicator rank (rank i) Q + pauliEndpointIndicator rank (rank j) Q)
      else if x = rank j then (4/5 : ℝ) *
        (pauliEndpointIndicator rank (rank i) Q + pauliEndpointIndicator rank (rank j) Q)
      else pauliEndpointIndicator rank x Q := by
  have hij : i ≠ j := by intro h; subst j; omega
  have hlt : rank i < rank j := by omega
  have hne : rank i ≠ rank j := Nat.ne_of_lt hlt
  by_cases hi : x = rank i
  · subst x
    rw [if_pos rfl, mul_add]
    apply pauliPairEvolution_product_mix _ _ _ i j hij
    · intro s _ _; rfl
    · intro s hsi hsj
      exact (pauliEndpointMarginal_adjacent_away rank hrank i j hadj s hsi hsj).symm
    · intro q
      simpa [pauliEndpointMarginal, hlt, hne, hne.symm, not_lt_of_ge hlt.le] using
        pauliHaar_endpoint_left q
  · rw [if_neg hi]
    by_cases hj : x = rank j
    · subst x
      rw [if_pos rfl, mul_add]
      apply pauliPairEvolution_product_mix _ _ _ i j hij
      · intro s hsi hsj
        exact pauliEndpointMarginal_adjacent_away rank hrank i j hadj s hsi hsj
      · intro s _ _; rfl
      · intro q
        simpa [pauliEndpointMarginal, hlt, hne, hne.symm, not_lt_of_ge hlt.le] using
          pauliHaar_endpoint_right q
    · rw [if_neg hj]
      apply pauliPairEvolution_product_fixed _ i j hij
      intro q
      by_cases hx : x < rank i
      · simpa [pauliEndpointMarginal, show ¬rank i < x by omega,
          show ¬rank j < x by omega, Ne.symm hi, Ne.symm hj] using pauliHaar_identity_product q
      · simpa [pauliEndpointMarginal, show rank i < x by omega,
          show rank j < x by omega] using pauliHaar_one_product q

/-- Every arbitrary Pauli-string distribution has the same closed local endpoint rule. -/
theorem pauliEndpointMass_haar_pair (rank : Site → ℕ)
    (hrank : Function.Injective rank) (i j : Site) (hadj : rank j = rank i + 1)
    (w : (Site → Fin 4) → ℝ) (x : ℕ) :
    pauliEndpointMass rank (pauliPairEvolution i j localPauliHaarKernel w) x =
      if x = rank i then (1/5 : ℝ) *
        (pauliEndpointMass rank w (rank i) + pauliEndpointMass rank w (rank j))
      else if x = rank j then (4/5 : ℝ) *
        (pauliEndpointMass rank w (rank i) + pauliEndpointMass rank w (rank j))
      else pauliEndpointMass rank w x := by
  have hij : i ≠ j := by intro h; subst j; omega
  unfold pauliEndpointMass
  rw [pauliPairEvolution_selfAdjoint i j hij]
  simp_rw [pauliEndpointIndicator_haar_pair rank hrank i j hadj]
  split_ifs <;> simp [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc]

/-- Equality of endpoint projections is preserved by every sequence of adjacent Haar gates. -/
theorem pauliEndpointMass_layer_congr (rank : Site → ℕ)
    (hrank : Function.Injective rank) (bs : List (Site × Site))
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (w v : (Site → Fin 4) → ℝ)
    (he : ∀ s, pauliEndpointMass rank w (rank s) = pauliEndpointMass rank v (rank s))
    (s : Site) :
    pauliEndpointMass rank (pauliLayerEvolution bs w) (rank s) =
      pauliEndpointMass rank (pauliLayerEvolution bs v) (rank s) := by
  induction bs generalizing w v with
  | nil => exact he s
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    apply ih (fun p hp => hadj p (by simp [hp]))
    intro t
    rw [pauliEndpointMass_haar_pair rank hrank i j (hadj (i,j) (by simp)),
      pauliEndpointMass_haar_pair rank hrank i j (hadj (i,j) (by simp))]
    simp only [he]

lemma pauliEndpointMass_sum {A : Type*} [Fintype A]
    (rank : Site → ℕ) (w : A → (Site → Fin 4) → ℝ) (a : A → ℝ) (x : ℕ) :
    pauliEndpointMass rank (fun P => ∑ k, a k * w k P) x =
      ∑ k, a k * pauliEndpointMass rank (w k) x := by
  simp only [pauliEndpointMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro P _
  ring

lemma pauliEndpointMass_add (rank : Site → ℕ) (w v : (Site → Fin 4) → ℝ)
    (a b : ℝ) (x : ℕ) :
    pauliEndpointMass rank (fun P => a * w P + b * v P) x =
      a * pauliEndpointMass rank w x + b * pauliEndpointMass rank v x := by
  simp [pauliEndpointMass, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]

/-- A normalized shock really has a deterministic endpoint. -/
theorem pauliEndpointMass_shock (rank : Site → ℕ) (hrank : Function.Injective rank)
    (s t : Site) :
    pauliEndpointMass rank (pauliShock rank (rank t)) (rank s) = if s = t then 1 else 0 := by
  unfold pauliEndpointMass pauliEndpointIndicator pauliShock pauliProductWeight
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun u p => pauliEndpointMarginal rank (rank s) u p *
    pauliShockMarginal rank (rank t) u p)]
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro u _
    by_cases hu : rank u < rank s
    · norm_num [pauliEndpointMarginal, pauliShockMarginal, hu, pauliUniformWeight,
        Fin.sum_univ_succ]
    · by_cases he : rank u = rank s
      · norm_num [pauliEndpointMarginal, pauliShockMarginal, hu, he,
          pauliNonzeroWeight, Fin.sum_univ_succ]
      · norm_num [pauliEndpointMarginal, pauliShockMarginal, hu, he,
          pauliIdentityWeight, Fin.sum_univ_succ]
  · rw [if_neg hst]
    have hr : rank s ≠ rank t := fun h => hst (hrank h)
    rcases lt_or_gt_of_ne hr with hlt | hlt
    · apply Finset.prod_eq_zero (Finset.mem_univ t)
      norm_num [pauliEndpointMarginal, pauliShockMarginal, not_lt_of_ge hlt.le,
        ne_of_gt hlt, pauliIdentityWeight, pauliNonzeroWeight, Fin.sum_univ_succ]
    · apply Finset.prod_eq_zero (Finset.mem_univ s)
      norm_num [pauliEndpointMarginal, pauliShockMarginal, not_lt_of_ge hlt.le,
        ne_of_gt hlt, pauliIdentityWeight, pauliNonzeroWeight, Fin.sum_univ_succ]

/-- Canonical shock mixture with exactly the endpoint masses of an arbitrary weight. -/
def pauliShockProjection (rank : Site → ℕ) (w : (Site → Fin 4) → ℝ)
    (P : Site → Fin 4) : ℝ :=
  ∑ s, pauliEndpointMass rank w (rank s) * pauliShock rank (rank s) P

theorem pauliEndpointMass_shockProjection (rank : Site → ℕ)
    (hrank : Function.Injective rank) (w : (Site → Fin 4) → ℝ) (s : Site) :
    pauliEndpointMass rank (pauliShockProjection rank w) (rank s) =
      pauliEndpointMass rank w (rank s) := by
  unfold pauliShockProjection
  rw [pauliEndpointMass_sum]
  simp [pauliEndpointMass_shock rank hrank]

/-- Haar endpoint observables can be evaluated on the shock representative even
when the physical distribution itself is not a shock mixture. -/
theorem pauliEndpointMass_layer_shockProjection (rank : Site → ℕ)
    (hrank : Function.Injective rank) (bs : List (Site × Site))
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (w : (Site → Fin 4) → ℝ) (s : Site) :
    pauliEndpointMass rank (pauliLayerEvolution bs w) (rank s) =
      pauliEndpointMass rank (pauliLayerEvolution bs (pauliShockProjection rank w)) (rank s) := by
  apply pauliEndpointMass_layer_congr rank hrank bs hadj
  intro t
  exact (pauliEndpointMass_shockProjection rank hrank w t).symm

omit [Fintype Site] in
lemma pauliLayerEvolution_fintype_sum {A : Type*} [Fintype A]
    (bs : List (Site × Site)) (w : A → (Site → Fin 4) → ℝ) (a : A → ℝ) :
    pauliLayerEvolution bs (fun P => ∑ k, a k * w k P) =
      fun Q => ∑ k, a k * pauliLayerEvolution bs (w k) Q := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    have hpair : pauliPairEvolution i j localPauliHaarKernel (fun P => ∑ k, a k * w k P) =
        fun Q => ∑ k, a k * pauliPairEvolution i j localPauliHaarKernel (w k) Q := by
      funext Q
      simp only [pauliPairEvolution, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro p _
      ring
    simp only [pauliLayerEvolution, hpair]
    exact ih _

end Endpoint

section BrickworkEndpoint

/-- Endpoint-cell mass, with the all-identity string excluded automatically. -/
def brickworkEndpointCellMass {c : ℕ} (w : (BrickworkSite c → Fin 4) → ℝ)
    (a : Fin (c+1)) : ℝ :=
  pauliEndpointMass brickworkRank w (2*a.val) +
    pauliEndpointMass brickworkRank w (2*a.val+1)

lemma brickworkOddBonds_adjacent (c : ℕ) (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ brickworkOddBonds c) : brickworkRank p.2 = brickworkRank p.1 + 1 := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
  simp [brickworkOddBond, brickworkRank]

lemma brickworkEvenBonds_adjacent (c : ℕ) (p : BrickworkSite c × BrickworkSite c)
    (hp : p ∈ brickworkEvenBonds c) : brickworkRank p.2 = brickworkRank p.1 + 1 := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
  simp [brickworkEvenBond, brickworkRank]
  omega

lemma pauliEndpointMass_cellShock (c : ℕ) (a t : Fin (c+1)) (b : Fin 2) :
    pauliEndpointMass brickworkRank (brickworkCellShock a) (brickworkRank (t,b)) =
      if t = a then (if b = 0 then 1/5 else 4/5) else 0 := by
  change pauliEndpointMass brickworkRank
    (fun P => (1/5 : ℝ)*pauliShock brickworkRank (brickworkRank (a,0)) P +
      (4/5 : ℝ)*pauliShock brickworkRank (brickworkRank (a,1)) P) _ = _
  rw [pauliEndpointMass_add]
  simp only [pauliEndpointMass_shock brickworkRank (brickworkRank_injective c), Prod.mk.injEq]
  fin_cases b <;> by_cases ht : t = a <;> simp [ht]

/-- A cell-shock mixture is a convenient representative of the endpoint projection. -/
def brickworkCellProjection {c : ℕ} (m : Fin (c+1) → ℝ)
    (P : BrickworkSite c → Fin 4) : ℝ :=
  ∑ a, m a * brickworkCellShock a P

lemma pauliEndpointMass_cellProjection (c : ℕ) (m : Fin (c+1) → ℝ)
    (a : Fin (c+1)) (b : Fin 2) :
    pauliEndpointMass brickworkRank (brickworkCellProjection m) (brickworkRank (a,b)) =
      (if b = 0 then 1/5 else 4/5) * m a := by
  unfold brickworkCellProjection
  rw [pauliEndpointMass_sum]
  simp [pauliEndpointMass_cellShock, mul_ite, mul_comm]

lemma brickworkOdd_shockProjection (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    pauliLayerEvolution (brickworkOddBonds c) (pauliShockProjection brickworkRank w) =
      brickworkCellProjection (brickworkEndpointCellMass w) := by
  unfold pauliShockProjection
  rw [pauliLayerEvolution_fintype_sum]
  funext Q
  simp only [Fintype.sum_prod_type, brickworkOdd_shock]
  simp only [brickworkCellProjection, brickworkEndpointCellMass,
    Fin.sum_univ_two, brickworkRank, Fin.val_zero, Fin.val_one, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A full odd Haar layer establishes the universal 1/5–4/5 endpoint profile.
The input weight is completely arbitrary and need not have a product form. -/
theorem pauliEndpointMass_odd (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ)
    (a : Fin (c+1)) (b : Fin 2) :
    pauliEndpointMass brickworkRank (pauliLayerEvolution (brickworkOddBonds c) w)
      (brickworkRank (a,b)) =
      (if b = 0 then 1/5 else 4/5) * brickworkEndpointCellMass w a := by
  rw [pauliEndpointMass_layer_shockProjection brickworkRank (brickworkRank_injective c)
    (brickworkOddBonds c) (brickworkOddBonds_adjacent c), brickworkOdd_shockProjection,
    pauliEndpointMass_cellProjection]

theorem brickworkEndpointCellMass_odd (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :
    brickworkEndpointCellMass (pauliLayerEvolution (brickworkOddBonds c) w) =
      brickworkEndpointCellMass w := by
  funext a
  change pauliEndpointMass brickworkRank _ (brickworkRank (a,0)) +
    pauliEndpointMass brickworkRank _ (brickworkRank (a,1)) = _
  rw [pauliEndpointMass_odd, pauliEndpointMass_odd]
  norm_num
  ring

lemma brickworkEndpointMass_period_congr (c : ℕ)
    (w v : (BrickworkSite c → Fin 4) → ℝ)
    (he : ∀ s : BrickworkSite c, pauliEndpointMass brickworkRank w (brickworkRank s) =
      pauliEndpointMass brickworkRank v (brickworkRank s)) (s : BrickworkSite c) :
    pauliEndpointMass brickworkRank (brickworkPeriod c w) (brickworkRank s) =
      pauliEndpointMass brickworkRank (brickworkPeriod c v) (brickworkRank s) := by
  apply pauliEndpointMass_layer_congr brickworkRank (brickworkRank_injective c)
    (brickworkOddBonds c) (brickworkOddBonds_adjacent c)
  intro t
  exact pauliEndpointMass_layer_congr brickworkRank (brickworkRank_injective c)
    (brickworkEvenBonds c) (brickworkEvenBonds_adjacent c) w v he t

lemma brickworkPeriod_cellProjection (c : ℕ) (m : Fin (c+1) → ℝ) :
    brickworkPeriod c (brickworkCellProjection m) =
      brickworkCellProjection ((endpointMarkov c).mulVec m) := by
  unfold brickworkCellProjection
  rw [brickworkPeriod_sum]
  simp_rw [brickworkPeriod_smul, brickworkPeriod_cellShock]
  funext Q
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma brickworkEndpointMass_iterate_congr (c n : ℕ)
    (w v : (BrickworkSite c → Fin 4) → ℝ)
    (he : ∀ s : BrickworkSite c, pauliEndpointMass brickworkRank w (brickworkRank s) =
      pauliEndpointMass brickworkRank v (brickworkRank s)) (s : BrickworkSite c) :
    pauliEndpointMass brickworkRank ((brickworkPeriod c)^[n] w) (brickworkRank s) =
      pauliEndpointMass brickworkRank ((brickworkPeriod c)^[n] v) (brickworkRank s) := by
  induction n generalizing s with
  | zero => exact he s
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply brickworkEndpointMass_period_congr
    intro t
    exact ih t

lemma brickworkPeriod_iterate_cellProjection (c n : ℕ) (m : Fin (c+1) → ℝ) :
    (brickworkPeriod c)^[n] (brickworkCellProjection m) =
      brickworkCellProjection ((endpointMarkov c ^ n).mulVec m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, brickworkPeriod_cellProjection,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- Exact universal endpoint profile after an initial odd layer and any number
of even–odd periods. This holds for every Pauli-string weight, including the
correlated distribution produced by a fixed gate. -/
theorem pauliEndpointMass_iterate_odd (c n : ℕ)
    (w : (BrickworkSite c → Fin 4) → ℝ) (a : Fin (c+1)) (b : Fin 2) :
    pauliEndpointMass brickworkRank
      ((brickworkPeriod c)^[n] (pauliLayerEvolution (brickworkOddBonds c) w))
      (brickworkRank (a,b)) =
      (if b = 0 then 1/5 else 4/5) *
        (endpointMarkov c ^ n).mulVec (brickworkEndpointCellMass w) a := by
  have he (s : BrickworkSite c) :
      pauliEndpointMass brickworkRank (pauliLayerEvolution (brickworkOddBonds c) w)
        (brickworkRank s) =
      pauliEndpointMass brickworkRank
        (brickworkCellProjection (brickworkEndpointCellMass w)) (brickworkRank s) := by
    rcases s with ⟨t,b⟩
    rw [pauliEndpointMass_odd, pauliEndpointMass_cellProjection]
  rw [brickworkEndpointMass_iterate_congr c n _ _ he,
    brickworkPeriod_iterate_cellProjection, pauliEndpointMass_cellProjection]

/-- The endpoint-cell distribution obeys the actual reflecting Markov matrix,
without any independence assumption on the incoming Pauli labels. -/
theorem brickworkEndpointCellMass_iterate_odd (c n : ℕ)
    (w : (BrickworkSite c → Fin 4) → ℝ) :
    brickworkEndpointCellMass
      ((brickworkPeriod c)^[n] (pauliLayerEvolution (brickworkOddBonds c) w)) =
      (endpointMarkov c ^ n).mulVec (brickworkEndpointCellMass w) := by
  funext a
  change pauliEndpointMass brickworkRank _ (brickworkRank (a,0)) +
    pauliEndpointMass brickworkRank _ (brickworkRank (a,1)) = _
  rw [pauliEndpointMass_iterate_odd, pauliEndpointMass_iterate_odd]
  norm_num
  ring

end BrickworkEndpoint

end
end Fluctuations
