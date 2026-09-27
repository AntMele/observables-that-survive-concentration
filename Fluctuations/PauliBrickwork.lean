import Fluctuations.PauliShock
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-! Full matching layers acting on actual Pauli-string distributions. -/

open scoped BigOperators

namespace Fluctuations
noncomputable section

section Layers
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

def pauliLayerEvolution : List (Site × Site) → ((Site → Fin 4) → ℝ) → (Site → Fin 4) → ℝ
  | [], w => w
  | (i,j) :: bs, w => pauliLayerEvolution bs (pauliPairEvolution i j localPauliHaarKernel w)

omit [Fintype Site] in
lemma pauliPairEvolution_linear (i j : Site) (w v : (Site → Fin 4) → ℝ) (a b : ℝ) :
    pauliPairEvolution i j localPauliHaarKernel (fun P => a * w P + b * v P) =
      fun Q => a * pauliPairEvolution i j localPauliHaarKernel w Q +
        b * pauliPairEvolution i j localPauliHaarKernel v Q := by
  funext Q
  simp only [pauliPairEvolution, mul_add, Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_comm (localPauliHaarKernel _ _) a,
    mul_comm (localPauliHaarKernel _ _) b, mul_assoc, ← Finset.mul_sum]

omit [Fintype Site] in
lemma pauliLayerEvolution_linear (bs : List (Site × Site))
    (w v : (Site → Fin 4) → ℝ) (a b : ℝ) :
    pauliLayerEvolution bs (fun P => a * w P + b * v P) =
      fun Q => a * pauliLayerEvolution bs w Q + b * pauliLayerEvolution bs v Q := by
  induction bs generalizing w v with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    simp only [pauliLayerEvolution, pauliPairEvolution_linear]
    exact ih _ _

lemma pauliLayerEvolution_shock_fixed (rank : Site → ℕ) (hrank : Function.Injective rank)
    (bs : List (Site × Site)) (x : ℕ)
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (hmiss : ∀ p ∈ bs, x ≠ rank p.1 ∧ x ≠ rank p.2) :
    pauliLayerEvolution bs (pauliShock rank x) = pauliShock rank x := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    have hpair : pauliPairEvolution i j localPauliHaarKernel (pauliShock rank x) =
        pauliShock rank x := by
      funext Q
      rw [pauliShock_haar_pair rank hrank i j (hadj (i,j) (by simp)),
        if_neg (not_or.mpr (hmiss (i,j) (by simp)))]
    simp only [pauliLayerEvolution, hpair]
    exact ih (fun p hp => hadj p (by simp [hp])) (fun p hp => hmiss p (by simp [hp]))

/-- A matching acts on a shock only through the unique bond containing its
endpoint. Every other local Haar gate is proved to preserve the full law. -/
theorem pauliLayerEvolution_shock_hit (rank : Site → ℕ) (hrank : Function.Injective rank)
    (bs : List (Site × Site)) (i j : Site) (x : ℕ)
    (hmem : (i,j) ∈ bs) (hx : x = rank i ∨ x = rank j)
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (hunique : ∀ p ∈ bs, p ≠ (i,j) →
      (rank i ≠ rank p.1 ∧ rank i ≠ rank p.2) ∧
      (rank j ≠ rank p.1 ∧ rank j ≠ rank p.2))
    (hnodup : bs.Nodup) :
    pauliLayerEvolution bs (pauliShock rank x) =
      fun Q => (1/5 : ℝ) * pauliShock rank (rank i) Q +
        (4/5 : ℝ) * pauliShock rank (rank j) Q := by
  induction bs with
  | nil => simp at hmem
  | cons p bs ih =>
    rcases p with ⟨u,v⟩
    by_cases hp : (u,v) = (i,j)
    · obtain ⟨hu,hv⟩ := Prod.mk.inj hp
      subst u
      subst v
      have hpair : pauliPairEvolution i j localPauliHaarKernel (pauliShock rank x) =
          fun Q => (1/5 : ℝ) * pauliShock rank (rank i) Q +
            (4/5 : ℝ) * pauliShock rank (rank j) Q := by
        funext Q
        rw [pauliShock_haar_pair rank hrank i j (hadj (i,j) (by simp)), if_pos hx]
      simp only [pauliLayerEvolution, hpair, pauliLayerEvolution_linear]
      have hn : (i,j) ∉ bs := (List.nodup_cons.mp hnodup).1
      have hd : ∀ p ∈ bs, p ≠ (i,j) := by intro p hp he; subst p; exact hn hp
      rw [pauliLayerEvolution_shock_fixed rank hrank bs (rank i)
          (fun p hp => hadj p (by simp [hp]))
          (fun p hp => (hunique p (by simp [hp]) (hd p hp)).1),
        pauliLayerEvolution_shock_fixed rank hrank bs (rank j)
          (fun p hp => hadj p (by simp [hp]))
          (fun p hp => (hunique p (by simp [hp]) (hd p hp)).2)]
    · have hm : (i,j) ∈ bs := by
        rcases List.mem_cons.mp hmem with he | he
        · exact False.elim (hp he.symm)
        · exact he
      have hu := hunique (u,v) (by simp) hp
      have hmiss : x ≠ rank u ∧ x ≠ rank v := by rcases hx with rfl | rfl; exact hu.1; exact hu.2
      have hpair : pauliPairEvolution u v localPauliHaarKernel (pauliShock rank x) =
          pauliShock rank x := by
        funext Q
        rw [pauliShock_haar_pair rank hrank u v (hadj (u,v) (by simp)), if_neg (not_or.mpr hmiss)]
      simp only [pauliLayerEvolution, hpair]
      exact ih hm (fun p hp => hadj p (by simp [hp]))
        (fun p hp he => hunique p (by simp [hp]) he) (List.nodup_cons.mp hnodup).2

omit [Fintype Site] in
lemma pauliLayerEvolution_append (bs cs : List (Site × Site))
    (w : (Site → Fin 4) → ℝ) :
    pauliLayerEvolution (bs ++ cs) w = pauliLayerEvolution cs (pauliLayerEvolution bs w) := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    simpa only [List.cons_append, pauliLayerEvolution] using
      ih (pauliPairEvolution i j localPauliHaarKernel w)

end Layers

/-- Qubits indexed by their cell and their left/right position. -/
abbrev BrickworkSite (c : ℕ) := Fin (c + 1) × Fin 2

def brickworkRank {c : ℕ} (s : BrickworkSite c) : ℕ := 2 * s.1.val + s.2.val

theorem brickworkRank_injective (c : ℕ) : Function.Injective (brickworkRank (c := c)) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ h
  simp only [brickworkRank] at h
  have hb := b.isLt
  have hb' := b'.isLt
  have ha : a = a' := Fin.ext (by omega)
  have he : b = b' := Fin.ext (by omega)
  simp [ha,he]

def brickworkOddBond {c : ℕ} (a : Fin (c + 1)) : BrickworkSite c × BrickworkSite c :=
  ((a,0),(a,1))

def brickworkEvenBond {c : ℕ} (a : Fin c) : BrickworkSite c × BrickworkSite c :=
  ((a.castSucc,1),(a.succ,0))

def brickworkOddBonds (c : ℕ) : List (BrickworkSite c × BrickworkSite c) :=
  List.ofFn (brickworkOddBond (c := c))

def brickworkEvenBonds (c : ℕ) : List (BrickworkSite c × BrickworkSite c) :=
  List.ofFn (brickworkEvenBond (c := c))

def brickworkCellShock {c : ℕ} (a : Fin (c + 1)) (P : BrickworkSite c → Fin 4) : ℝ :=
  (1/5 : ℝ) * pauliShock brickworkRank (2 * a.val) P +
  (4/5 : ℝ) * pauliShock brickworkRank (2 * a.val + 1) P

theorem brickworkOdd_shock (c : ℕ) (a : Fin (c + 1)) (b : Fin 2) :
    pauliLayerEvolution (brickworkOddBonds c)
      (pauliShock brickworkRank (brickworkRank (a,b))) = brickworkCellShock a := by
  have h := pauliLayerEvolution_shock_hit brickworkRank (brickworkRank_injective c)
    (brickworkOddBonds c) (a,0) (a,1) (brickworkRank (a,b))
  apply h
  · simp only [brickworkOddBonds, List.mem_ofFn]
    exact ⟨a,rfl⟩
  · fin_cases b <;> simp [brickworkRank]
  · intro p hp
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkOddBond, brickworkRank]
  · intro p hp hpne
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hp
    have hne : u ≠ a := by intro he; subst u; exact hpne rfl
    have hv : u.val ≠ a.val := fun he => hne (Fin.ext he)
    simp only [brickworkOddBond, brickworkRank, Fin.val_zero, Fin.val_one]
    omega
  · apply List.nodup_ofFn.mpr
    intro u v huv
    exact congrArg (fun p => p.1.1) huv

theorem brickworkEven_shock_hit {c : ℕ} (a : Fin c) (x : ℕ)
    (hx : x = 2 * a.val + 1 ∨ x = 2 * a.val + 2) :
    pauliLayerEvolution (brickworkEvenBonds c) (pauliShock brickworkRank x) =
      fun Q => (1/5 : ℝ) * pauliShock brickworkRank (2 * a.val + 1) Q +
        (4/5 : ℝ) * pauliShock brickworkRank (2 * a.val + 2) Q := by
  have h := pauliLayerEvolution_shock_hit brickworkRank (brickworkRank_injective c)
    (brickworkEvenBonds c) (a.castSucc,1) (a.succ,0) x
  have hv : brickworkRank (a.succ, (0 : Fin 2)) = 2 * a.val + 2 := by
    simp [brickworkRank]; omega
  rw [hv] at h
  apply h
  · simp only [brickworkEvenBonds, List.mem_ofFn]
    exact ⟨a,rfl⟩
  · simpa [brickworkRank] using hx
  · intro p hp
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond, brickworkRank]; omega
  · intro p hp hpne
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hp
    have hne : u ≠ a := by intro he; subst u; exact hpne rfl
    have huv : u.val ≠ a.val := fun he => hne (Fin.ext he)
    simp only [brickworkEvenBond, brickworkRank, Fin.val_zero, Fin.val_one,
      Fin.coe_castSucc, Fin.val_succ]
    omega
  · apply List.nodup_ofFn.mpr
    intro u v huv
    apply Fin.ext
    exact congrArg (fun p => p.1.1.val) huv

theorem brickworkEven_shock_first (c : ℕ) :
    pauliLayerEvolution (brickworkEvenBonds c) (pauliShock brickworkRank 0) =
      pauliShock brickworkRank 0 := by
  apply pauliLayerEvolution_shock_fixed brickworkRank (brickworkRank_injective c)
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond, brickworkRank]; omega
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond, brickworkRank]

theorem brickworkEven_shock_last (c : ℕ) :
    pauliLayerEvolution (brickworkEvenBonds c) (pauliShock brickworkRank (2*c+1)) =
      pauliShock brickworkRank (2*c+1) := by
  apply pauliLayerEvolution_shock_fixed brickworkRank (brickworkRank_injective c)
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    simp [brickworkEvenBond, brickworkRank]; omega
  · intro p hp
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    have ha := a.isLt
    simp only [brickworkEvenBond, brickworkRank, Fin.val_zero, Fin.val_one,
      Fin.coe_castSucc, Fin.val_succ]
    omega

lemma brickworkOdd_shock_left {c : ℕ} (a : Fin (c + 1)) :
    pauliLayerEvolution (brickworkOddBonds c) (pauliShock brickworkRank (2*a.val)) =
      brickworkCellShock a := by
  simpa [brickworkRank] using brickworkOdd_shock c a 0

lemma brickworkOdd_shock_right {c : ℕ} (a : Fin (c + 1)) :
    pauliLayerEvolution (brickworkOddBonds c) (pauliShock brickworkRank (2*a.val+1)) =
      brickworkCellShock a := by
  simpa [brickworkRank] using brickworkOdd_shock c a 1

/-- One effective endpoint step: an even layer followed by an odd layer. -/
def brickworkPeriod (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) :=
  pauliLayerEvolution (brickworkOddBonds c) (pauliLayerEvolution (brickworkEvenBonds c) w)

theorem brickworkPeriod_linear (c : ℕ) (w v : (BrickworkSite c → Fin 4) → ℝ) (a b : ℝ) :
    brickworkPeriod c (fun P => a*w P+b*v P) =
      fun Q => a*brickworkPeriod c w Q+b*brickworkPeriod c v Q := by
  simp only [brickworkPeriod, pauliLayerEvolution_linear]

lemma brickworkPeriod_shock_hit {c : ℕ} (a : Fin c) (x : ℕ)
    (hx : x = 2 * a.val + 1 ∨ x = 2 * a.val + 2) :
    brickworkPeriod c (pauliShock brickworkRank x) =
      fun Q => (1/5 : ℝ) * brickworkCellShock a.castSucc Q +
        (4/5 : ℝ) * brickworkCellShock a.succ Q := by
  rw [brickworkPeriod, brickworkEven_shock_hit a x hx, pauliLayerEvolution_linear]
  have hs : 2 * a.val + 2 = 2 * a.succ.val := by simp; omega
  rw [hs, brickworkOdd_shock_left]
  change (fun Q => (1/5 : ℝ) *
    pauliLayerEvolution (brickworkOddBonds c) (pauliShock brickworkRank (2*a.castSucc.val+1)) Q + _) = _
  rw [brickworkOdd_shock_right]

lemma brickworkPeriod_shock_first (c : ℕ) :
    brickworkPeriod c (pauliShock brickworkRank 0) = brickworkCellShock (0 : Fin (c+1)) := by
  rw [brickworkPeriod, brickworkEven_shock_first]
  simpa using brickworkOdd_shock_left (0 : Fin (c+1))

lemma brickworkPeriod_shock_last (c : ℕ) :
    brickworkPeriod c (pauliShock brickworkRank (2*c+1)) = brickworkCellShock (Fin.last c) := by
  rw [brickworkPeriod, brickworkEven_shock_last]
  exact brickworkOdd_shock_right (Fin.last c)

lemma endpointMarkov_sum_column (c : ℕ) (a : Fin (c+1)) (f : Fin (c+1) → ℝ) :
    (∑ b, endpointMarkov c b a * f b) =
      ((8/25 : ℝ) + (if a.val = 0 then 1/25 else 0) +
        (if a.val = c then 16/25 else 0)) * f a +
      (if h : a.val < c then (16/25 : ℝ) * f ⟨a.val+1,by omega⟩ else 0) +
      (if h : 0 < a.val then (1/25 : ℝ) * f ⟨a.val-1,by omega⟩ else 0) := by
  simp only [endpointMarkov_apply, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  have hdiag : (∑ b : Fin (c+1),
      (if b = a then ((8/25 : ℝ)+(if b.val=0 then 1/25 else 0)+
        (if b.val=c then 16/25 else 0))*f b else 0)) =
      ((8/25 : ℝ)+(if a.val=0 then 1/25 else 0)+(if a.val=c then 16/25 else 0))*f a := by simp
  simp only [add_mul, ite_mul, zero_mul] at hdiag
  rw [hdiag]
  congr 1
  · congr 1
    rw [sum_fin_value]
    split_ifs <;> first | rfl | omega
  · have he (b : Fin (c+1)) : a.val = b.val + 1 ↔ 0 < a.val ∧ b.val = a.val-1 := by omega
    simp_rw [he]
    by_cases ha : 0 < a.val
    · simp only [ha, true_and, dif_pos]
      rw [sum_fin_value]
      simp [show a.val-1<c+1 by omega]
    · simp [ha]

/-- The full Pauli-string law, averaged over an even and an odd Haar layer,
closes exactly under the reflecting cell matrix from the paper. -/
theorem brickworkPeriod_cellShock (c : ℕ) (a : Fin (c+1)) :
    brickworkPeriod c (brickworkCellShock a) =
      fun Q => ∑ b : Fin (c+1), endpointMarkov c b a * brickworkCellShock b Q := by
  change brickworkPeriod c (fun P => (1/5 : ℝ)*pauliShock brickworkRank (2*a.val) P +
    (4/5 : ℝ)*pauliShock brickworkRank (2*a.val+1) P) = _
  rw [brickworkPeriod_linear]
  have hleft : brickworkPeriod c (pauliShock brickworkRank (2*a.val)) =
      if h : 0 < a.val then
        (fun Q => (1/5 : ℝ)*brickworkCellShock ⟨a.val-1,by omega⟩ Q +
          (4/5 : ℝ)*brickworkCellShock a Q)
      else brickworkCellShock a := by
    split_ifs with ha
    · let b : Fin c := ⟨a.val-1,by omega⟩
      have he : b.succ = a := Fin.ext (by dsimp [b]; omega)
      have hx : 2*a.val=2*b.val+2 := by dsimp [b]; omega
      rw [brickworkPeriod_shock_hit b _ (Or.inr hx),he]
      rfl
    · have he : a = 0 := Fin.ext (by change a.val = 0; omega)
      subst a
      exact brickworkPeriod_shock_first c
  have hright : brickworkPeriod c (pauliShock brickworkRank (2*a.val+1)) =
      if h : a.val < c then
        (fun Q => (1/5 : ℝ)*brickworkCellShock a Q +
          (4/5 : ℝ)*brickworkCellShock ⟨a.val+1,by omega⟩ Q)
      else brickworkCellShock a := by
    split_ifs with ha
    · let b : Fin c := ⟨a.val,ha⟩
      have he : b.castSucc = a := Fin.ext rfl
      rw [brickworkPeriod_shock_hit b _ (Or.inl rfl),he]
      rfl
    · have he : a = Fin.last c := Fin.ext (by simp; omega)
      subst a
      exact brickworkPeriod_shock_last c
  rw [hleft,hright]
  funext Q
  rw [endpointMarkov_sum_column]
  have ha := a.isLt
  split_ifs <;> first | omega | ring

lemma brickworkPeriod_zero (c : ℕ) : brickworkPeriod c (fun _ => 0) = fun _ => 0 := by
  have h := brickworkPeriod_linear c (fun _ => 0) (fun _ => 0) 0 0
  simpa using h

lemma brickworkPeriod_smul (c : ℕ) (w : (BrickworkSite c → Fin 4) → ℝ) (a : ℝ) :
    brickworkPeriod c (fun P => a*w P) = fun Q => a*brickworkPeriod c w Q := by
  simpa using brickworkPeriod_linear c w (fun _ => 0) a 0

lemma brickworkPeriod_sum {ι : Type*} (c : ℕ) (s : Finset ι)
    (w : ι → (BrickworkSite c → Fin 4) → ℝ) :
    brickworkPeriod c (fun P => ∑ a ∈ s, w a P) =
      fun Q => ∑ a ∈ s, brickworkPeriod c (w a) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using brickworkPeriod_zero c
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h := brickworkPeriod_linear c (w a) (fun P => ∑ a ∈ s, w a P) 1 1
    simpa [ih] using h

/-- The exact arbitrary-depth forward Pauli law, not merely its endpoint marginal. -/
theorem brickworkPeriod_iterate_cellShock (c s : ℕ) (a : Fin (c+1)) :
    (brickworkPeriod c)^[s] (brickworkCellShock a) =
      fun Q => ∑ b : Fin (c+1), (endpointMarkov c ^ s) b a * brickworkCellShock b Q := by
  induction s with
  | zero =>
    funext Q
    simp [Matrix.one_apply]
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, brickworkPeriod_sum]
    simp_rw [brickworkPeriod_smul, brickworkPeriod_cellShock]
    funext Q
    rw [pow_succ']
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring

end
end Fluctuations
