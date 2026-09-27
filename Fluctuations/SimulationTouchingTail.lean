import Fluctuations.SimulationEndpointTail
import Fluctuations.PauliBrickworkInitial
import Fluctuations.UniversalEndpointObservable

open scoped BigOperators

namespace Fluctuations
noncomputable section

section General
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Total Pauli weight touching at least one of the two specified sites. -/
def simulationTouching (i j : Site) (w : (Site → Fin 4) → ℝ) : ℝ :=
  ∑ P, w P * (if P i = 0 ∧ P j = 0 then 0 else 1)

lemma simulationTouching_linear (i j : Site) (w v : (Site → Fin 4) → ℝ) (a b : ℝ) :
    simulationTouching i j (fun P => a * w P + b * v P) =
      a * simulationTouching i j w + b * simulationTouching i j v := by
  simp only [simulationTouching, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_assoc]

lemma simulationTouching_sum {A : Type*} [Fintype A] (i j : Site)
    (w : A → (Site → Fin 4) → ℝ) :
    simulationTouching i j (fun P => ∑ a, w a P) = ∑ a, simulationTouching i j (w a) := by
  simp only [simulationTouching, Finset.sum_mul]
  exact Finset.sum_comm

lemma simulationTouching_smul (i j : Site) (w : (Site → Fin 4) → ℝ) (a : ℝ) :
    simulationTouching i j (fun P => a * w P) = a * simulationTouching i j w := by
  simp only [simulationTouching, Finset.mul_sum, mul_assoc]

lemma simulationTouching_nonneg (i j : Site) (w : (Site → Fin 4) → ℝ)
    (hw : ∀ P, 0 ≤ w P) : 0 ≤ simulationTouching i j w := by
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (hw P) (by split_ifs <;> norm_num))

lemma simulationTouching_le_mass (i j : Site) (w : (Site → Fin 4) → ℝ)
    (hw : ∀ P, 0 ≤ w P) : simulationTouching i j w ≤ ∑ P, w P := by
  apply Finset.sum_le_sum
  intro P _
  split_ifs
  · simpa using hw P
  · simp

omit [DecidableEq Site] in
lemma simulationShock_nonneg (rank : Site → ℕ) (x : ℕ) (P : Site → Fin 4) :
    0 ≤ pauliShock rank x P := by
  apply Finset.prod_nonneg
  intro s _
  unfold pauliShockMarginal
  split_ifs <;> dsimp [pauliUniformWeight, pauliNonzeroWeight, pauliIdentityWeight]
  all_goals positivity

lemma simulationShock_mass (rank : Site → ℕ) (x : ℕ) :
    (∑ P : Site → Fin 4, pauliShock rank x P) = 1 := by
  unfold pauliShock pauliProductWeight
  rw [← Fintype.prod_sum]
  apply Finset.prod_eq_one
  intro s _
  unfold pauliShockMarginal
  split_ifs <;> norm_num [pauliUniformWeight, pauliNonzeroWeight,
    pauliIdentityWeight, Fin.sum_univ_succ]

omit [DecidableEq Site] in
lemma simulationShock_support (rank : Site → ℕ) (x : ℕ) (P : Site → Fin 4)
    (s : Site) (hs : x < rank s) (hP : P s ≠ 0) : pauliShock rank x P = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  simp [pauliShockMarginal, show ¬rank s < x by omega, ne_of_gt hs,
    pauliIdentityWeight, hP]

lemma simulationTouching_shock_zero (rank : Site → ℕ) (x : ℕ) (i j : Site)
    (hi : x < rank i) (hj : x < rank j) :
    simulationTouching i j (pauliShock rank x) = 0 := by
  apply Finset.sum_eq_zero
  intro P _
  by_cases hPi : P i = 0
  · by_cases hPj : P j = 0
    · simp [hPi, hPj]
    · rw [simulationShock_support rank x P j hj hPj]
      simp
  · rw [simulationShock_support rank x P i hi hPi]
    simp

omit [Fintype Site] in
lemma simulationLayer_nonneg (bs : List (Site × Site)) (w : (Site → Fin 4) → ℝ)
    (hw : ∀ P, 0 ≤ w P) : ∀ P, 0 ≤ pauliLayerEvolution bs w P := by
  induction bs generalizing w with
  | nil => exact hw
  | cons p bs ih =>
    apply ih
    intro P
    apply Finset.sum_nonneg
    intro q _
    apply mul_nonneg _ (hw _)
    unfold localPauliHaarKernel
    split_ifs <;> norm_num

end General

/-- Actual Pauli law just before physical even layer `2s+2`: the first odd
Haar layer and then `s` complete even/odd periods have been processed. -/
def simulationBeforeEven (c s : ℕ) : (BrickworkSite c → Fin 4) → ℝ :=
  (brickworkPeriod c)^[s]
    (pauliLayerEvolution (brickworkOddBonds c) (pauliInitialVector (brickworkInitialZ c)))

/-- Actual law just before physical odd layer `2s+3`. -/
def simulationBeforeOdd (c s : ℕ) : (BrickworkSite c → Fin 4) → ℝ :=
  pauliLayerEvolution (brickworkEvenBonds c) (simulationBeforeEven c s)

theorem simulationBeforeEven_eq (c s : ℕ) :
    simulationBeforeEven c s = fun P => ∑ b : Fin (c + 1),
      (endpointMarkov c ^ s) b 0 * brickworkCellShock b P := by
  rw [simulationBeforeEven, brickworkInitialZ_odd_layer, brickworkPeriod_iterate_cellShock]

lemma simulationCellShock_nonneg {c : ℕ} (b : Fin (c + 1)) (P : BrickworkSite c → Fin 4) :
    0 ≤ brickworkCellShock b P := by
  unfold brickworkCellShock
  exact add_nonneg (mul_nonneg (by norm_num) (simulationShock_nonneg _ _ _))
    (mul_nonneg (by norm_num) (simulationShock_nonneg _ _ _))

lemma simulationCellShock_mass {c : ℕ} (b : Fin (c + 1)) :
    (∑ P : BrickworkSite c → Fin 4, brickworkCellShock b P) = 1 := by
  simp only [brickworkCellShock, Finset.sum_add_distrib, ← Finset.mul_sum,
    simulationShock_mass]
  norm_num

lemma simulationCellShock_touching_zero {c : ℕ} (b : Fin (c + 1)) (i j : BrickworkSite c)
    (hi : 2 * b.val + 1 < brickworkRank i) (hj : 2 * b.val + 1 < brickworkRank j) :
    simulationTouching i j (brickworkCellShock b) = 0 := by
  change simulationTouching i j (fun P => (1/5 : ℝ) * pauliShock brickworkRank (2*b.val) P +
    (4/5 : ℝ) * pauliShock brickworkRank (2*b.val+1) P) = 0
  rw [simulationTouching_linear,
    simulationTouching_shock_zero _ _ _ _ (by omega) (by omega),
    simulationTouching_shock_zero _ _ _ _ hi hj]
  ring

/-- A physical even gate can be touched only after reaching its left cell. -/
theorem simulationTouching_even_le (c s : ℕ) (a : Fin c) :
    simulationTouching (a.castSucc, 1) (a.succ, 0) (simulationBeforeEven c s) ≤
      simulationEndpointTail c s a.val := by
  rw [simulationBeforeEven_eq, simulationTouching_sum]
  simp_rw [simulationTouching_smul]
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (simulationEndpointPower_nonneg c s b 0)
  by_cases hb : a.val ≤ b.val
  · rw [if_pos hb]
    exact (simulationTouching_le_mass _ _ _ (simulationCellShock_nonneg b)).trans_eq
      (simulationCellShock_mass b)
  · have hi : 2 * b.val + 1 < brickworkRank (a.castSucc, (1 : Fin 2)) := by
      simp only [brickworkRank, Fin.coe_castSucc, Fin.val_one]; omega
    have hj : 2 * b.val + 1 < brickworkRank (a.succ, (0 : Fin 2)) := by
      simp only [brickworkRank, Fin.val_succ, Fin.val_zero]; omega
    rw [if_neg hb, simulationCellShock_touching_zero b _ _ hi hj]

/-- An even layer moves the endpoint of a shock by at most one physical site. -/
lemma simulationEven_shock_touching_zero (c x : ℕ) (hx : x ≤ 2 * c + 1)
    (i j : BrickworkSite c) (hi : x + 1 < brickworkRank i) (hj : x + 1 < brickworkRank j) :
    simulationTouching i j
      (pauliLayerEvolution (brickworkEvenBonds c) (pauliShock brickworkRank x)) = 0 := by
  by_cases h0 : x = 0
  · subst x
    rw [brickworkEven_shock_first]
    exact simulationTouching_shock_zero _ _ _ _ (by omega) (by omega)
  by_cases hlast : x = 2 * c + 1
  · subst x
    rw [brickworkEven_shock_last]
    exact simulationTouching_shock_zero _ _ _ _ (by omega) (by omega)
  let a : Fin c := ⟨(x - 1) / 2, by omega⟩
  have hhit : x = 2 * a.val + 1 ∨ x = 2 * a.val + 2 := by dsimp [a]; omega
  rw [brickworkEven_shock_hit a x hhit, simulationTouching_linear,
    simulationTouching_shock_zero _ _ _ _ (by rcases hhit with h | h <;> omega)
      (by rcases hhit with h | h <;> omega),
    simulationTouching_shock_zero _ _ _ _ (by rcases hhit with h | h <;> omega)
      (by rcases hhit with h | h <;> omega)]
  ring

lemma simulationEven_cell_touching_zero {c : ℕ} (b : Fin (c + 1)) (i j : BrickworkSite c)
    (hi : 2 * b.val + 2 < brickworkRank i) (hj : 2 * b.val + 2 < brickworkRank j) :
    simulationTouching i j
      (pauliLayerEvolution (brickworkEvenBonds c) (brickworkCellShock b)) = 0 := by
  change simulationTouching i j (pauliLayerEvolution (brickworkEvenBonds c)
    (fun P => (1/5 : ℝ) * pauliShock brickworkRank (2*b.val) P +
      (4/5 : ℝ) * pauliShock brickworkRank (2*b.val+1) P)) = 0
  rw [pauliLayerEvolution_linear, simulationTouching_linear,
    simulationEven_shock_touching_zero c _ (by omega) _ _ (by omega) (by omega),
    simulationEven_shock_touching_zero c _ (by omega) _ _ hi hj]
  ring

/-- The preceding even layer can advance at most one cell. This bound
includes the leftmost odd bond via its truncated threshold zero. -/
theorem simulationTouching_odd_le (c s : ℕ) (a : Fin (c + 1)) :
    simulationTouching (a, 0) (a, 1) (simulationBeforeOdd c s) ≤
      simulationEndpointTail c s (a.val - 1) := by
  rw [simulationBeforeOdd, simulationBeforeEven_eq,
    pauliLayerEvolution_fintype_sum, simulationTouching_sum]
  simp_rw [simulationTouching_smul]
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (simulationEndpointPower_nonneg c s b 0)
  by_cases hb : a.val - 1 ≤ b.val
  · rw [if_pos hb]
    apply (simulationTouching_le_mass _ _ _
      (simulationLayer_nonneg _ _ (simulationCellShock_nonneg b))).trans_eq
    rw [brickworkEven_totalMass, simulationCellShock_mass]
  · have hi : 2 * b.val + 2 < brickworkRank (a, (0 : Fin 2)) := by
      simp only [brickworkRank, Fin.val_zero]; omega
    have hj : 2 * b.val + 2 < brickworkRank (a, (1 : Fin 2)) := by
      simp only [brickworkRank, Fin.val_one]; omega
    rw [if_neg hb, simulationEven_cell_touching_zero b _ _ hi hj]


/-- Touching a physical even bond has the paper's uniform Gaussian tail. -/
theorem simulationTouching_even_gaussian (c s : ℕ) (a : Fin c) :
    simulationTouching (a.castSucc, 1) (a.succ, 0) (simulationBeforeEven c s) ≤
      (5 / 2) * Real.exp
        (-(max (5 * (2 * (a.val : ℝ) + 2) - 3 * (2 * (s : ℝ) + 2)) 0) ^ 2 /
          (200 * (2 * (s : ℝ) + 2))) := by
  have hg : (5 * (2 * (a.val : ℝ) + 2) - 3 * (2 * s + 2 : ℕ) - 4) / 10 ≤
      ((2 * s + 1 : ℕ) : ℝ) / 5 - (((s : ℤ) - a.val : ℤ) : ℝ) := by
    push_cast
    linarith
  have hb := simulationBinomialCDF_touching (2 * s + 1) (2 * s + 2)
    (by omega) (by omega) (by omega) ((s : ℤ) - a.val) (2 * (a.val : ℝ) + 2) hg
  have h := (simulationTouching_even_le c s a).trans
    ((simulationEndpointTail_binomial c s a.val).trans hb)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

/-- Touching a physical odd bond after the first layer has the same tail. -/
theorem simulationTouching_odd_gaussian (c s : ℕ) (a : Fin (c + 1)) :
    simulationTouching (a, 0) (a, 1) (simulationBeforeOdd c s) ≤
      (5 / 2) * Real.exp
        (-(max (5 * (2 * (a.val : ℝ) + 1) - 3 * (2 * (s : ℝ) + 3)) 0) ^ 2 /
          (200 * (2 * (s : ℝ) + 3))) := by
  have hg : (5 * (2 * (a.val : ℝ) + 1) - 3 * (2 * s + 3 : ℕ) - 4) / 10 ≤
      ((2 * s + 1 : ℕ) : ℝ) / 5 - (((s : ℤ) - (a.val - 1 : ℕ) : ℤ) : ℝ) := by
    by_cases ha : a.val = 0
    · simp only [ha, Nat.zero_sub, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Int.cast_natCast]
      linarith
    · have he : ((a.val - 1 : ℕ) : ℝ) = (a.val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      push_cast
      rw [he]
      linarith
  have hb := simulationBinomialCDF_touching (2 * s + 1) (2 * s + 3)
    (by omega) (by omega) (by omega) ((s : ℤ) - (a.val - 1 : ℕ))
    (2 * (a.val : ℝ) + 1) hg
  have h := (simulationTouching_odd_le c s a).trans
    ((simulationEndpointTail_binomial c s (a.val - 1)).trans hb)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

lemma simulationTouching_initial (c : ℕ) (a : Fin (c + 1)) :
    simulationTouching (a, 0) (a, 1) (pauliInitialVector (brickworkInitialZ c)) =
      if a = 0 then 1 else 0 := by
  simp only [simulationTouching, pauliInitialVector, ite_mul, one_mul, zero_mul]
  simp [brickworkInitialZ]

/-- The initial odd layer is included, with no positive-time exception. -/
theorem simulationTouching_initial_gaussian (c : ℕ) (a : Fin (c + 1)) :
    simulationTouching (a, 0) (a, 1) (pauliInitialVector (brickworkInitialZ c)) ≤
      (5 / 2) * Real.exp (-(max (5 * (2 * (a.val : ℝ) + 1) - 3) 0) ^ 2 / 200) := by
  rw [simulationTouching_initial]
  by_cases ha : a = 0
  · subst a
    norm_num
    have he := Real.add_one_le_exp (-(1 / 50 : ℝ))
    norm_num at he
    linarith
  · rw [if_neg ha]
    positivity

end
end Fluctuations
