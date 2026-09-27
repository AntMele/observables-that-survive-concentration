import Fluctuations.BinomialLocalBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.Interval

/-! The actual lattice of even gates in the diffusive endpoint eye.  Coordinates
in `endpointEye` are half-coordinates: `(a,s)` represents the gate `(2a,2s)`.
The bounds count this explicitly defined finite set, rather than assuming a
number of influential gates. -/

open scoped BigOperators

namespace Fluctuations

/-- Half-coordinates of the even integers in a closed real interval. -/
noncomputable def evenLatticeInterval (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈a / 2⌉ ⌊b / 2⌋

lemma mem_evenLatticeInterval {a b : ℝ} {j : ℤ} :
    j ∈ evenLatticeInterval a b ↔ a ≤ 2 * (j : ℝ) ∧ 2 * (j : ℝ) ≤ b := by
  simp only [evenLatticeInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma evenLatticeInterval_card_lower (a b : ℝ) :
    (b - a) / 2 - 1 ≤ ((evenLatticeInterval a b).card : ℝ) := by
  have hf := Int.lt_floor_add_one (b / 2)
  have hc := Int.ceil_lt_add_one (a / 2)
  have hn : (⌊b / 2⌋ + 1 - ⌈a / 2⌉ : ℤ) ≤
      ((⌊b / 2⌋ + 1 - ⌈a / 2⌉).toNat : ℤ) := by omega
  have hn' := (Int.cast_le (R := ℝ)).mpr hn
  simp only [evenLatticeInterval, Int.card_Icc]
  push_cast at hn'
  linarith

lemma evenLatticeInterval_card_upper {a b : ℝ} (hab : a ≤ b) :
    ((evenLatticeInterval a b).card : ℝ) ≤ (b - a) / 2 + 1 := by
  have hf := Int.floor_le (b / 2)
  have hc := Int.le_ceil (a / 2)
  simp only [evenLatticeInterval, Int.card_Icc]
  by_cases h : 0 ≤ ⌊b / 2⌋ + 1 - ⌈a / 2⌉
  · have he := Int.toNat_of_nonneg h
    have he' := congrArg (fun z : ℤ => (z : ℝ)) he
    push_cast at he'
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    push_cast
    linarith

/-- Center line after sharing the total front displacement equally between
the past and future segments. -/
noncomputable def endpointEyeCenter (n d ℓ : ℝ) : ℝ :=
  5 * ℓ / 3 + (d - 5 * n / 3) / 2

/-- The manuscript's central eye, with even spatial and temporal coordinates. -/
noncomputable def endpointEye (n d : ℕ) : Finset (Σ _ : ℤ, ℤ) :=
  (evenLatticeInterval ((n : ℝ) / 3) (2 * n / 3)).sigma fun a =>
    evenLatticeInterval
      (endpointEyeCenter n d (2 * a) - Real.sqrt n)
      (endpointEyeCenter n d (2 * a) + Real.sqrt n)

lemma mem_endpointEye {n d : ℕ} {z : Σ _ : ℤ, ℤ} :
    z ∈ endpointEye n d ↔
      (n : ℝ) / 3 ≤ 2 * (z.1 : ℝ) ∧ 2 * (z.1 : ℝ) ≤ 2 * n / 3 ∧
      |2 * (z.2 : ℝ) - endpointEyeCenter n d (2 * z.1)| ≤ Real.sqrt n := by
  simp only [endpointEye, Finset.mem_sigma, mem_evenLatticeInterval, abs_le]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨h₁,h₂,by linarith,by linarith⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨⟨h₁,h₂⟩,by linarith,by linarith⟩

/-- There are at least `n * sqrt n / 24` even gates in the eye. -/
theorem endpointEye_card_lower {n d : ℕ} (hn : 12 ≤ n) :
    (n : ℝ) * Real.sqrt n / 24 ≤ ((endpointEye n d).card : ℝ) := by
  have hnr : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 2 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hc := evenLatticeInterval_card_lower ((n : ℝ)/3) (2*n/3)
  have hcl : (n : ℝ)/12 ≤ ((evenLatticeInterval ((n:ℝ)/3) (2*n/3)).card : ℝ) := by
    linarith
  have ht (a : ℤ) : Real.sqrt n / 2 ≤
      ((evenLatticeInterval
        (endpointEyeCenter n d (2*a) - Real.sqrt n)
        (endpointEyeCenter n d (2*a) + Real.sqrt n)).card : ℝ) := by
    have h := evenLatticeInterval_card_lower
      (endpointEyeCenter n d (2*a) - Real.sqrt n)
      (endpointEyeCenter n d (2*a) + Real.sqrt n)
    linarith
  have hsum := Finset.sum_le_sum (s := evenLatticeInterval ((n:ℝ)/3) (2*n/3))
    (fun a _ => ht a)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [endpointEye, Finset.card_sigma, Nat.cast_sum]
  have hm := mul_le_mul_of_nonneg_right hcl (show 0 ≤ Real.sqrt n / 2 by positivity)
  nlinarith

/-- The same concrete set has at most `2*n*sqrt n/3` gates. -/
theorem endpointEye_card_upper {n d : ℕ} (hn : 12 ≤ n) :
    ((endpointEye n d).card : ℝ) ≤ 2 * (n : ℝ) * Real.sqrt n / 3 := by
  have hnr : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith)
  have hc := evenLatticeInterval_card_upper
    (a := (n : ℝ)/3) (b := 2*n/3) (by linarith)
  have hcu : ((evenLatticeInterval ((n:ℝ)/3) (2*n/3)).card : ℝ) ≤ (n : ℝ)/3 := by
    linarith
  have ht (a : ℤ) :
      ((evenLatticeInterval
        (endpointEyeCenter n d (2*a) - Real.sqrt n)
        (endpointEyeCenter n d (2*a) + Real.sqrt n)).card : ℝ) ≤ 2 * Real.sqrt n := by
    have h := evenLatticeInterval_card_upper
      (a := endpointEyeCenter n d (2*a) - Real.sqrt n)
      (b := endpointEyeCenter n d (2*a) + Real.sqrt n) (by linarith [Real.sqrt_nonneg (n:ℝ)])
    linarith
  have hsum := Finset.sum_le_sum (s := evenLatticeInterval ((n:ℝ)/3) (2*n/3))
    (fun a _ => ht a)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [endpointEye, Finset.card_sigma, Nat.cast_sum]
  have hm := mul_le_mul_of_nonneg_right hcu (show 0 ≤ 2 * Real.sqrt n by positivity)
  nlinarith

/-- Quantitative geometry needed by both propagation factors. -/
structure EndpointSegmentBounds (n c ℓ t : ℝ) : Prop where
  space_lower : n / 3 ≤ ℓ
  space_upper : ℓ ≤ 2 * n / 3
  time_lower : n / 2 ≤ t
  time_upper : t ≤ 7 * n / 6
  size_lower : n / 3 ≤ t - 1
  size_upper : t - 1 ≤ 4 * n / 3
  index_pos : 0 < (t - ℓ) / 2
  index_lt : (t - ℓ) / 2 < t - 1
  no_reflection : t + ℓ < 2 * n
  deviation : |(t - ℓ) / 2 - (t - 1) / 5| ≤ (c + 2) * Real.sqrt n
  prefactor : 1 / 3 ≤ 2 * ℓ / (t + ℓ)

lemma endpointSegmentBounds_of_near {n c ℓ t : ℝ}
    (hc : 0 ≤ c) (hlarge : 12 * (c + 2) ≤ Real.sqrt n)
    (hℓ₁ : n / 3 ≤ ℓ) (hℓ₂ : ℓ ≤ 2 * n / 3)
    (ht : |t - 5 * ℓ / 3| ≤ (c / 2 + 1) * Real.sqrt n) :
    EndpointSegmentBounds n c ℓ t := by
  have hs : 24 ≤ Real.sqrt n := by linarith
  have hn : 0 < n := Real.sqrt_pos.mp (by linarith : 0 < Real.sqrt n)
  have hs₂ := Real.sq_sqrt hn.le
  have hnlarge : 576 ≤ n := by nlinarith
  have herr : (c / 2 + 1) * Real.sqrt n ≤ n / 24 := by
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.sqrt_nonneg n)
    nlinarith
  have hta := (abs_le.mp ht).1
  have htb := (abs_le.mp ht).2
  have htlo : n / 2 ≤ t := by linarith
  have hthi : t ≤ 7 * n / 6 := by linarith
  have hdev : |(t - ℓ) / 2 - (t - 1) / 5| ≤ (c + 2) * Real.sqrt n := by
    rw [abs_le]
    have hcsp : 0 ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg n)
    constructor <;> nlinarith
  have hden : 0 < t + ℓ := by linarith
  refine ⟨hℓ₁,hℓ₂,htlo,hthi,by linarith,by linarith,by linarith,
    by linarith,by linarith,hdev,?_⟩
  apply (le_div_iff₀ hden).mpr
  linarith

/-- Both halves of a gate in the eye are interior, diffusive, and too short
to encounter a reflection at the opposite boundary.  The constant `c`
allows any fixed-width front window from the main theorem. -/
theorem endpointEye_segmentBounds {n d : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hlarge : 12 * (c + 2) ≤ Real.sqrt n)
    (hfront : |(d : ℝ) - 5 * n / 3| ≤ c * Real.sqrt n)
    {z : Σ _ : ℤ, ℤ} (hz : z ∈ endpointEye n d) :
    EndpointSegmentBounds n c (2 * z.1) (2 * z.2) ∧
    EndpointSegmentBounds n c ((n : ℝ) - 2 * z.1) ((d : ℝ) - 2 * z.2) := by
  obtain ⟨hℓ₁,hℓ₂,ht⟩ := mem_endpointEye.mp hz
  have hδ₁ := (abs_le.mp hfront).1
  have hδ₂ := (abs_le.mp hfront).2
  have ht₁ := (abs_le.mp ht).1
  have ht₂ := (abs_le.mp ht).2
  unfold endpointEyeCenter at ht₁ ht₂
  constructor
  · apply endpointSegmentBounds_of_near hc hlarge hℓ₁ hℓ₂
    rw [abs_le]
    constructor <;> linarith
  · apply endpointSegmentBounds_of_near hc hlarge (by linarith) (by linarith)
    rw [abs_le]
    constructor <;> linarith

/-- A positive uniform front constant; no effort is made to optimize it. -/
noncomputable def endpointFrontConstant (c : ℝ) : ℝ :=
  Real.exp (-2 - 25 * (c + 2) ^ 2) / 6

theorem endpointFrontConstant_pos (c : ℝ) : 0 < endpointFrontConstant c := by
  unfold endpointFrontConstant
  positivity

/-- The local binomial lower estimate applied to an actual eye segment. -/
theorem EndpointSegmentBounds.binomial_lower {n c ℓ t : ℝ} {M r : ℕ}
    (h : EndpointSegmentBounds n c ℓ t) (hn : 0 < n) (hc : 0 ≤ c)
    (hM : (M : ℝ) = t - 1) (hr : (r : ℝ) = (t - ℓ) / 2) :
    Real.exp (-2 - 25 * (c + 2) ^ 2) / (2 * Real.sqrt n) ≤
      endpointBinomialMass M r := by
  have hr₀ : 0 < r := by exact_mod_cast (hr ▸ h.index_pos)
  have hrM : r < M := by
    apply Nat.cast_lt (α := ℝ) |>.mp
    rw [hr,hM]
    exact h.index_lt
  have hMp : (0 : ℝ) < M := by rw [hM]; linarith [h.size_lower]
  have hs₁ : Real.sqrt n ≤ 2 * Real.sqrt M := by
    have hsq₁ := Real.sq_sqrt hn.le
    have hsq₂ := Real.sq_sqrt hMp.le
    have hl := h.size_lower
    rw [← hM] at hl
    nlinarith [Real.sqrt_nonneg n, Real.sqrt_nonneg (M : ℝ)]
  have hs₂ : Real.sqrt M ≤ 2 * Real.sqrt n := by
    have hsq₁ := Real.sq_sqrt hn.le
    have hsq₂ := Real.sq_sqrt hMp.le
    have hu := h.size_upper
    rw [← hM] at hu
    nlinarith [Real.sqrt_nonneg n, Real.sqrt_nonneg (M : ℝ)]
  have hd : |(r : ℝ) - M / 5| ≤ (2 * (c + 2)) * Real.sqrt M := by
    have hh := mul_le_mul_of_nonneg_left hs₁ (show 0 ≤ c + 2 by linarith)
    rw [hr,hM]
    calc
      _ ≤ (c + 2) * Real.sqrt n := h.deviation
      _ ≤ _ := by simpa [hM, mul_assoc, mul_left_comm] using hh
  have hb := endpointBinomialMass_diffusive_lower hr₀ hrM
    (H := 2 * (c + 2)) (by linarith) hd
  have he : -2 - (25/4 : ℝ) * (2 * (c + 2)) ^ 2 = -2 - 25 * (c + 2) ^ 2 := by ring
  rw [he] at hb
  exact le_trans (div_le_div_of_nonneg_left (Real.exp_pos _).le
    (Real.sqrt_pos.mpr hMp) hs₂) hb

/-- The ballot prefactor is uniformly bounded below inside the eye. -/
theorem EndpointSegmentBounds.front_lower {n c ℓ t : ℝ} {M r : ℕ}
    (h : EndpointSegmentBounds n c ℓ t) (hn : 0 < n) (hc : 0 ≤ c)
    (hM : (M : ℝ) = t - 1) (hr : (r : ℝ) = (t - ℓ) / 2) :
    endpointFrontConstant c / Real.sqrt n ≤
      endpointBinomialMass M r * (2 * ℓ / (t + ℓ)) := by
  have hb := h.binomial_lower hn hc hM hr
  have hp := h.prefactor
  have hm := mul_le_mul hb hp (by norm_num : (0 : ℝ) ≤ 1/3)
    (by unfold endpointBinomialMass; positivity : 0 ≤ endpointBinomialMass M r)
  calc
    _ = (Real.exp (-2 - 25 * (c + 2)^2) / (2 * Real.sqrt n)) * (1/3) := by
      unfold endpointFrontConstant
      ring
    _ ≤ _ := hm

end Fluctuations
