import Fluctuations.EndpointBinomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open scoped BigOperators

namespace Fluctuations

/-- The lower CDF of a sum of `m` independent Bernoulli(1/5) variables,
defined by its exact convolution recursion. Integer thresholds include the
zero convention below the support. -/
noncomputable def simulationBinomialCDF : ℕ → ℤ → ℝ
  | 0, r => if 0 ≤ r then 1 else 0
  | m + 1, r => (4 / 5) * simulationBinomialCDF m r +
      (1 / 5) * simulationBinomialCDF m (r - 1)

lemma simulationBinomialCDF_nonneg (m : ℕ) (r : ℤ) :
    0 ≤ simulationBinomialCDF m r := by
  induction m generalizing r with
  | zero => simp only [simulationBinomialCDF]; split_ifs <;> norm_num
  | succ m ih =>
    simp only [simulationBinomialCDF]
    exact add_nonneg (mul_nonneg (by norm_num) (ih r))
      (mul_nonneg (by norm_num) (ih (r - 1)))

lemma simulationBinomialCDF_le_one (m : ℕ) (r : ℤ) :
    simulationBinomialCDF m r ≤ 1 := by
  induction m generalizing r with
  | zero => simp only [simulationBinomialCDF]; split_ifs <;> norm_num
  | succ m ih =>
    simp only [simulationBinomialCDF]
    linarith [ih r, ih (r - 1)]

lemma simulationBinomialCDF_neg (m : ℕ) {r : ℤ} (hr : r < 0) :
    simulationBinomialCDF m r = 0 := by
  induction m generalizing r with
  | zero => simp [simulationBinomialCDF, not_le.mpr hr]
  | succ m ih => simp [simulationBinomialCDF, ih hr, ih (show r - 1 < 0 by omega)]

lemma simulationBinomialCDF_mono (m : ℕ) : Monotone (simulationBinomialCDF m) := by
  induction m with
  | zero =>
    intro a b hab
    simp only [simulationBinomialCDF]
    split_ifs <;> norm_num
    omega
  | succ m ih =>
    intro a b hab
    simp only [simulationBinomialCDF]
    linarith [ih hab, ih (show a - 1 ≤ b - 1 by omega)]

lemma simulationBinomialCDF_add_two (m : ℕ) (r : ℤ) :
    simulationBinomialCDF (m + 2) r =
      (16 / 25) * simulationBinomialCDF m r +
      (8 / 25) * simulationBinomialCDF m (r - 1) +
      (1 / 25) * simulationBinomialCDF m (r - 2) := by
  simp only [simulationBinomialCDF]
  rw [show r - 1 - 1 = r - 2 by omega]
  ring

/-- Zero-extended point probabilities, in an integer-index form convenient
for exact convolution and reflection identities. -/
noncomputable def simulationBinomialMass (m : ℕ) (r : ℤ) : ℝ :=
  (4 : ℝ) ^ ((m : ℤ) - r) / (5 : ℝ) ^ m * endpointChoose m r

lemma simulationBinomialMass_nonneg (m : ℕ) (r : ℤ) :
    0 ≤ simulationBinomialMass m r := by
  unfold simulationBinomialMass endpointChoose
  positivity

lemma simulationBinomialMass_succ (m : ℕ) (r : ℤ) :
    simulationBinomialMass (m + 1) r =
      (4 / 5) * simulationBinomialMass m r +
      (1 / 5) * simulationBinomialMass m (r - 1) := by
  have h1 : (4 : ℝ) ^ (((m + 1 : ℕ) : ℤ) - r) =
      (4 : ℝ) ^ ((m : ℤ) - r) * 4 := by
    rw [show (((m + 1 : ℕ) : ℤ) - r) = (m : ℤ) - r + 1 by omega,
      zpow_add₀ (by norm_num)]
    norm_num
  have h2 : (4 : ℝ) ^ ((m : ℤ) - (r - 1)) =
      (4 : ℝ) ^ ((m : ℤ) - r) * 4 := by
    rw [show (m : ℤ) - (r - 1) = (m : ℤ) - r + 1 by omega,
      zpow_add₀ (by norm_num)]
    norm_num
  simp only [simulationBinomialMass, h1, h2, endpointChoose_succ, pow_succ]
  ring

lemma simulationBinomialCDF_sub (m : ℕ) (r : ℤ) :
    simulationBinomialCDF m r - simulationBinomialCDF m (r - 1) =
      simulationBinomialMass m r := by
  induction m generalizing r with
  | zero =>
    by_cases h0 : r = 0
    · subst r; norm_num [simulationBinomialCDF, simulationBinomialMass, endpointChoose]
    · by_cases hn : r < 0
      · rw [simulationBinomialCDF_neg _ hn,
          simulationBinomialCDF_neg _ (show r - 1 < 0 by omega)]
        simp [simulationBinomialMass, endpointChoose_neg _ hn]
      · have hp : 0 < r := by omega
        simp [simulationBinomialCDF, show 0 ≤ r by omega, show 1 ≤ r by omega,
          simulationBinomialMass, endpointChoose_gt _ hp]
  | succ m ih =>
    rw [simulationBinomialCDF, simulationBinomialCDF, simulationBinomialMass_succ,
      ← ih r, ← ih (r - 1)]
    ring


/-- Identification with the usual binomial point-probability formula. -/
theorem simulationBinomialMass_nat (m r : ℕ) :
    simulationBinomialMass m r =
      (m.choose r : ℝ) * (1 / 5 : ℝ) ^ r * (4 / 5 : ℝ) ^ (m - r) := by
  by_cases hr : r ≤ m
  · have hpow : (5 : ℝ) ^ m = (5 : ℝ) ^ r * (5 : ℝ) ^ (m - r) := by
      rw [← pow_add, Nat.add_sub_of_le hr]
    rw [simulationBinomialMass, endpointChoose_nat,
      ← Nat.cast_sub hr, zpow_natCast]
    rw [div_pow, div_pow, one_pow, hpow]
    ring
  · simp [simulationBinomialMass, endpointChoose_nat, Nat.choose_eq_zero_of_lt (by omega : m < r)]

/-- Explicit finite-CDF identification. Thus the convolution used in the
comparison theorem is the standard binomial distribution, not a surrogate. -/
theorem simulationBinomialCDF_sum (m r : ℕ) :
    simulationBinomialCDF m r =
      ∑ k ∈ Finset.range (r + 1),
        (m.choose k : ℝ) * (1 / 5 : ℝ) ^ k * (4 / 5 : ℝ) ^ (m - k) := by
  induction r with
  | zero =>
    have h := simulationBinomialCDF_sub m 0
    rw [show (0 : ℤ) - 1 = -1 by omega, simulationBinomialCDF_neg m (r := -1) (by omega),
      sub_zero, show (0 : ℤ) = (0 : ℕ) by rfl, simulationBinomialMass_nat] at h
    simpa using h
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h := simulationBinomialCDF_sub m ((r + 1 : ℕ) : ℤ)
    rw [show ((r + 1 : ℕ) : ℤ) - 1 = r by omega,
      simulationBinomialMass_nat] at h
    linarith

/-- The adjacent central masses of an odd binomial differ by exactly 1/4. -/
lemma simulationBinomialMass_odd_center (s : ℕ) :
    simulationBinomialMass (2 * s + 1) ((s : ℤ) + 1) =
      (1 / 4) * simulationBinomialMass (2 * s + 1) s := by
  have hc : endpointChoose (2 * s + 1) ((s : ℤ) + 1) =
      endpointChoose (2 * s + 1) s := by
    rw [endpointChoose_symm]
    congr 1
    omega
  have he : (4 : ℝ) ^ (((2 * s + 1 : ℕ) : ℤ) - ((s : ℤ) + 1)) =
      (4 : ℝ) ^ (((2 * s + 1 : ℕ) : ℤ) - (s : ℤ)) / 4 := by
    rw [show (((2 * s + 1 : ℕ) : ℤ) - ((s : ℤ) + 1)) =
        (((2 * s + 1 : ℕ) : ℤ) - (s : ℤ)) - 1 by omega,
      zpow_sub₀ (by norm_num)]
    norm_num
  simp only [simulationBinomialMass, hc, he]
  ring

/-- The reflecting left boundary is controlled uniformly in time. -/
theorem simulationBinomialCDF_odd_center (s : ℕ) :
    (4 / 5 : ℝ) ≤ simulationBinomialCDF (2 * s + 1) s := by
  induction s with
  | zero => norm_num [simulationBinomialCDF]
  | succ s ih =>
    rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by omega,
      simulationBinomialCDF_add_two]
    have hplus := simulationBinomialCDF_sub (2 * s + 1) ((s : ℤ) + 1)
    have hminus := simulationBinomialCDF_sub (2 * s + 1) (s : ℤ)
    rw [show (s : ℤ) + 1 - 1 = s by omega, simulationBinomialMass_odd_center] at hplus
    have hn := simulationBinomialMass_nonneg (2 * s + 1) s
    have he1 : ((s + 1 : ℕ) : ℤ) - 1 = s := by omega
    have he2 : ((s + 1 : ℕ) : ℤ) - 2 = (s : ℤ) - 1 := by omega
    rw [he1, he2]
    push_cast
    linarith

lemma simulation_exp_neg_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hd (y : ℝ) : HasDerivAt f (-1 + y + Real.exp (-y)) y := by
    convert (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).neg).exp) using 1
    dsimp [f]
    ring
  have hm : Monotone f := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    (fun y => by rw [(hd y).deriv]; linarith [Real.add_one_le_exp (-y)])
  have h := hm hx
  dsimp [f] at h
  norm_num at h
  linarith

/-- Elementary Chernoff bound, before choosing the exponential parameter. -/
theorem simulationBinomialCDF_chernoff (m : ℕ) (r : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    simulationBinomialCDF m r ≤ Real.exp (t * r) *
      ((4 / 5 : ℝ) + (1 / 5) * Real.exp (-t)) ^ m := by
  induction m generalizing r with
  | zero =>
    simp only [simulationBinomialCDF, pow_zero, mul_one]
    split_ifs with hr
    · exact Real.one_le_exp (mul_nonneg ht (by exact_mod_cast hr))
    · exact (Real.exp_pos _).le
  | succ m ih =>
    rw [simulationBinomialCDF, pow_succ]
    have hr := ih r
    have hr' := ih (r - 1)
    have he : Real.exp (t * ((r - 1 : ℤ) : ℝ)) = Real.exp (t * r) * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [he] at hr'
    nlinarith

/-- Hoeffding's lower-tail estimate derived from the binomial convolution,
with no tail inequality assumed as an input. -/
theorem simulationBinomialCDF_hoeffding (m : ℕ) (hm : 0 < m) (r : ℤ)
    (hr : (r : ℝ) ≤ (m : ℝ) / 5) :
    simulationBinomialCDF m r ≤
      Real.exp (-2 * ((m : ℝ) / 5 - r) ^ 2 / m) := by
  let a : ℝ := (m : ℝ) / 5 - r
  let t : ℝ := 4 * a / m
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 ≤ a := sub_nonneg.mpr hr
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbase : (4 / 5 : ℝ) + (1 / 5) * Real.exp (-t) ≤
      Real.exp (-t / 5 + t ^ 2 / 8) := by
    have hq := simulation_exp_neg_quadratic ht
    have he := Real.add_one_le_exp (-t / 5 + t ^ 2 / 8)
    nlinarith [sq_nonneg t]
  calc
    simulationBinomialCDF m r ≤ Real.exp (t * r) *
        ((4 / 5 : ℝ) + (1 / 5) * Real.exp (-t)) ^ m :=
      simulationBinomialCDF_chernoff m r ht
    _ ≤ Real.exp (t * r) * Real.exp (-t / 5 + t ^ 2 / 8) ^ m := by
      gcongr
    _ = Real.exp (t * r + (m : ℝ) * (-t / 5 + t ^ 2 / 8)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ = Real.exp (-2 * ((m : ℝ) / 5 - r) ^ 2 / m) := by
      congr 1
      dsimp [t, a]
      field_simp
      ring


/-- The constants used for physical touching tails. A possible loss of at
most four in the front coordinate absorbs the odd/even layer conventions. -/
theorem simulationBinomialCDF_touching (m u : ℕ) (hm : 0 < m) (hu : 0 < u)
    (hmu : m ≤ u) (r : ℤ) (v : ℝ)
    (hgap : (5 * v - 3 * u - 4) / 10 ≤ (m : ℝ) / 5 - r) :
    (5 / 4 : ℝ) * simulationBinomialCDF m r ≤
      (5 / 2) * Real.exp (-(max (5 * v - 3 * u) 0) ^ 2 / (200 * u)) := by
  let A : ℝ := 5 * v - 3 * u
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hmu' : (m : ℝ) ≤ u := by exact_mod_cast hmu
  by_cases hA : 8 ≤ A
  · have hd : A / 20 ≤ (m : ℝ) / 5 - r := by dsimp [A] at *; linarith
    have hr : (r : ℝ) ≤ (m : ℝ) / 5 := by linarith
    have hs : A ^ 2 ≤ 400 * ((m : ℝ) / 5 - r) ^ 2 := by nlinarith
    have he : -2 * ((m : ℝ) / 5 - r) ^ 2 / m ≤ -A ^ 2 / (200 * u) := by
      apply (div_le_div_iff₀ hmp (by positivity : (0 : ℝ) < 200 * u)).2
      nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hmu'),
        mul_nonneg (show 0 ≤ 400 * ((m : ℝ) / 5 - r) ^ 2 - A ^ 2 by linarith) hup.le]
    calc
      (5 / 4 : ℝ) * simulationBinomialCDF m r ≤
          (5 / 4) * Real.exp (-2 * ((m : ℝ) / 5 - r) ^ 2 / m) := by
        gcongr
        exact simulationBinomialCDF_hoeffding m hm r hr
      _ ≤ (5 / 4) * Real.exp (-A ^ 2 / (200 * u)) := by gcongr
      _ ≤ (5 / 2) * Real.exp (-A ^ 2 / (200 * u)) := by
        nlinarith [Real.exp_pos (-A ^ 2 / (200 * u))]
      _ = _ := by rw [max_eq_left (by dsimp [A] at hA; linarith)]
  · have hA' : max A 0 < 8 := max_lt (lt_of_not_ge hA) (by norm_num)
    have hA0 : 0 ≤ max A 0 := le_max_right _ _
    have hsq : (max A 0) ^ 2 ≤ 64 := by nlinarith
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hdiv : -(max A 0) ^ 2 / (200 * u) ≥ -(1 / 2 : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 200 * u)).2
      nlinarith
    have hex := Real.add_one_le_exp (-(max A 0) ^ 2 / (200 * u))
    have hc := simulationBinomialCDF_le_one m r
    change (5 / 4 : ℝ) * simulationBinomialCDF m r ≤
      (5 / 2) * Real.exp (-(max A 0) ^ 2 / (200 * u))
    nlinarith

end Fluctuations
