import Fluctuations.PauliEndpointObservable

/-! Quantitative stability of the real Pauli-amplitude representation. -/

open scoped BigOperators

namespace Fluctuations

variable {Q : Type*} [Fintype Q]

/-- Squared Euclidean mass, in the orthonormal Pauli coefficient convention. -/
def amplitudeMass (v : Q → ℝ) : ℝ := ∑ q, v q ^ 2

lemma amplitudeMass_nonneg (v : Q → ℝ) : 0 ≤ amplitudeMass v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The final commutation-sign readout of a coherent Pauli vector. -/
def amplitudeSignReadout (f v : Q → ℝ) : ℝ := ∑ q, f q * v q ^ 2

theorem amplitudeSignReadout_abs_le (f v : Q → ℝ) (hf : ∀ q, |f q| ≤ 1) :
    |amplitudeSignReadout f v| ≤ amplitudeMass v := by
  calc
    _ ≤ ∑ q, |f q * v q ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, v q ^ 2 := Finset.sum_le_sum fun q _ => by
      rw [abs_mul, abs_pow, sq_abs]
      exact mul_le_of_le_one_left (sq_nonneg _) (hf q)

theorem amplitudeMass_add_le (v w : Q → ℝ) :
    amplitudeMass (fun q => v q + w q) ≤ 2 * amplitudeMass v + 2 * amplitudeMass w := by
  simp only [amplitudeMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => by nlinarith [sq_nonneg (v q - w q)]

theorem amplitudeMass_sub_le (v w : Q → ℝ) :
    amplitudeMass (fun q => v q - w q) ≤ 2 * amplitudeMass v + 2 * amplitudeMass w := by
  simp only [amplitudeMass, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => by nlinarith [sq_nonneg (v q + w q)]

/-- A bounded diagonal readout is 2-Lipschitz on normalized real vectors. -/
theorem amplitudeSignReadout_sub_sq_le (f v w : Q → ℝ)
    (hf : ∀ q, |f q| ≤ 1) (hv : amplitudeMass v = 1) (hw : amplitudeMass w = 1) :
    (amplitudeSignReadout f v - amplitudeSignReadout f w) ^ 2 ≤
      4 * amplitudeMass (fun q => v q - w q) := by
  have he : amplitudeSignReadout f v - amplitudeSignReadout f w =
      ∑ q, (v q - w q) * (f q * (v q + w q)) := by
    simp only [amplitudeSignReadout, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun q => v q - w q) (g := fun q => f q * (v q + w q))
  have hb : (∑ q, (f q * (v q + w q)) ^ 2) ≤ 4 := by
    calc
      _ ≤ amplitudeMass (fun q => v q + w q) := Finset.sum_le_sum fun q _ => by
        have hq := hf q
        have hs : f q ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 hq
        dsimp
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) hs
      _ ≤ 4 := by linarith [amplitudeMass_add_le v w]
  change _ ≤ 4 * (∑ q, (v q - w q) ^ 2)
  exact hc.trans ((mul_le_mul_of_nonneg_left hb
    (Finset.sum_nonneg fun q _ => sq_nonneg (v q - w q))).trans_eq (mul_comm _ _))

/-- The familiar factor four follows from the mass of the active gate sector. -/
theorem amplitudeSignReadout_sub_le_four_sqrt (f v w : Q → ℝ)
    (hf : ∀ q, |f q| ≤ 1) (hv : amplitudeMass v = 1) (hw : amplitudeMass w = 1)
    (p : ℝ) (hp : 0 ≤ p)
    (hd : amplitudeMass (fun q => v q - w q) ≤ 4 * p) :
    |amplitudeSignReadout f v - amplitudeSignReadout f w| ≤ 4 * Real.sqrt p := by
  have h := amplitudeSignReadout_sub_sq_le f v w hf hv hw
  have hs := Real.sq_sqrt hp
  have ha := sq_abs (amplitudeSignReadout f v - amplitudeSignReadout f w)
  nlinarith [Real.sqrt_nonneg p, abs_nonneg (amplitudeSignReadout f v - amplitudeSignReadout f w)]

/-- Orthogonal column identities imply preservation of the full squared mass. -/
theorem amplitudeMass_mulVec [DecidableEq Q] (K : Matrix Q Q ℝ)
    (hK : ∀ a b, ∑ q, K q a * K q b = if a = b then 1 else 0)
    (v : Q → ℝ) : amplitudeMass (K.mulVec v) = amplitudeMass v := by
  classical
  unfold amplitudeMass
  simp only [Matrix.mulVec, dotProduct, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have he (b : Q) : (∑ q, K q a * v a * (K q b * v b)) =
      (∑ q, K q a * K q b) * (v a * v b) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  simp_rw [he, hK]
  simp

end Fluctuations
