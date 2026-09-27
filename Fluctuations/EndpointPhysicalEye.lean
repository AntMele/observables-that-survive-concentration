import Fluctuations.EndpointFrontLower

/-! The diffusive eye as a subset of the actual finite even-gate coordinates. -/

namespace Fluctuations
noncomputable section

def endpointPhysicalEyeLabel {c T : ℕ} (z : Fin T × Fin (c+1)) : Σ _ : ℤ, ℤ :=
  ⟨(z.2.val : ℤ)+1, (z.1.val : ℤ)+1⟩

theorem endpointPhysicalEyeLabel_injective (c T : ℕ) :
    Function.Injective (endpointPhysicalEyeLabel (c := c) (T := T)) := by
  intro z w h
  have h₁ := congrArg Sigma.fst h
  have h₂ : (endpointPhysicalEyeLabel z).2 = (endpointPhysicalEyeLabel w).2 :=
    congrArg (fun p : Σ _ : ℤ, ℤ => p.2) h
  simp only [endpointPhysicalEyeLabel] at h₁ h₂
  apply Prod.ext <;> apply Fin.ext <;> omega

def endpointPhysicalEye (c T : ℕ) : Finset (Fin T × Fin (c+1)) :=
  Finset.univ.filter fun z => endpointPhysicalEyeLabel z ∈ endpointEye (2*(c+2)) (2*T)

@[simp] theorem mem_endpointPhysicalEye {c T : ℕ} {z : Fin T × Fin (c+1)} :
    z ∈ endpointPhysicalEye c T ↔
      endpointPhysicalEyeLabel z ∈ endpointEye (2*(c+2)) (2*T) := by
  simp [endpointPhysicalEye]

theorem endpointPhysicalEye_image {c T : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hlarge : 12 * (C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2))) :
    (endpointPhysicalEye c T).image endpointPhysicalEyeLabel = endpointEye (2*(c+2)) (2*T) := by
  classical
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact mem_endpointPhysicalEye.mp hw
  · intro hz
    have hb := endpointEye_segmentBounds (n := 2*(c+2)) (d := 2*T)
      hC (by simpa using hlarge) (by simpa using hfront) hz
    obtain ⟨hp,hf⟩ := hb
    have hxlo := hp.space_lower
    have hxhi := hp.space_upper
    have htlo := hp.time_lower
    have hthi := hf.time_lower
    push_cast at hxlo hxhi htlo hthi
    have hz₁p : (0 : ℝ) < (z.1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) c]
    have hz₂p : (0 : ℝ) < (z.2 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) c]
    have hz₁ : 1 ≤ z.1 := by
      have : (0 : ℤ) < z.1 := by exact_mod_cast hz₁p
      omega
    have hz₂ : 1 ≤ z.2 := by
      have : (0 : ℤ) < z.2 := by exact_mod_cast hz₂p
      omega
    have hz₁lt : z.1 < (c : ℤ)+2 := by
      have : (z.1 : ℝ) < (c : ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) c]
      exact_mod_cast this
    have hz₂lt : z.2 < (T : ℤ) := by
      have : (z.2 : ℝ) < (T : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) c]
      exact_mod_cast this
    let w : Fin T × Fin (c+1) :=
      (⟨z.2.toNat-1,by omega⟩,⟨z.1.toNat-1,by omega⟩)
    have he : endpointPhysicalEyeLabel w = z := by
      apply Sigma.ext
      · dsimp [endpointPhysicalEyeLabel,w]
        omega
      · apply heq_of_eq
        dsimp [endpointPhysicalEyeLabel,w]
        omega
    apply Finset.mem_image.mpr
    exact ⟨w,mem_endpointPhysicalEye.mpr (he ▸ hz),he⟩

/-- The actual available even-gate coordinates contain the counted eye. -/
theorem endpointPhysicalEye_card_bounds {c T : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hlarge : 12 * (C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2))) :
    (2*(c+2) : ℝ)*Real.sqrt (2*(c+2))/24 ≤ ((endpointPhysicalEye c T).card : ℝ) ∧
      ((endpointPhysicalEye c T).card : ℝ) ≤
        2*(2*(c+2) : ℝ)*Real.sqrt (2*(c+2))/3 := by
  have he := congrArg Finset.card (endpointPhysicalEye_image hC hlarge hfront)
  rw [Finset.card_image_of_injective _ (endpointPhysicalEyeLabel_injective c T)] at he
  rw [he]
  have hs : 24 ≤ Real.sqrt (2*(c+2)) := by linarith
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2*(c+2) by positivity)
  have hn : 12 ≤ 2*(c+2) := by
    have : (12 : ℝ) ≤ 2*(c+2) := by nlinarith
    exact_mod_cast this
  exact ⟨by simpa using endpointEye_card_lower (d := 2*T) hn,
    by simpa using endpointEye_card_upper (d := 2*T) hn⟩

/-- Every counted eye gate has a complete later odd layer. -/
theorem endpointPhysicalEye_interior {c T : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hlarge : 12*(C+2) ≤ Real.sqrt (2*(c+2)))
    (hfront : |(2*T : ℝ)-5*(2*(c+2))/3| ≤ C*Real.sqrt (2*(c+2)))
    {z : Fin T × Fin (c+1)} (hz : z ∈ endpointPhysicalEye c T) : z.1.val+1 < T := by
  have hf := (endpointEye_segmentBounds (n := 2*(c+2)) (d := 2*T)
    hC (by simpa using hlarge) (by simpa using hfront)
    (mem_endpointPhysicalEye.mp hz)).2.time_lower
  simp only [endpointPhysicalEyeLabel] at hf
  push_cast at hf
  have hh : (z.1.val : ℝ)+1 < T := by linarith [Nat.cast_nonneg (α := ℝ) c]
  exact_mod_cast hh

end
end Fluctuations
