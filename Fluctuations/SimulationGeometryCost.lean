import Fluctuations.SimulationCost

/-! Construct the actual outside-first support and arithmetic-call schedule.
The size bounds of `SimulationCost` are discharged here from the physical eye,
not assumed as an unverified width certificate. -/
namespace Fluctuations
noncomputable section
variable {Site : Type*} [DecidableEq Site]

def simulationLayerOutsideCalls (C : Finset Site) (outside : Finset (Site × Site)) :
    List SimulationLocalCall :=
  List.ofFn fun k : Fin outside.card =>
    let p := outside.toList[k.val]'(by simp)
    SimulationLocalCall.averaged
      (simulationOutsideSupport C (outside.toList.take k.val).toFinset ∪ {p.1,p.2}).card

def simulationLayerRetainedCalls (C : Finset Site)
    (outside retained : Finset (Site × Site)) : List SimulationLocalCall :=
  List.ofFn fun k : Fin retained.card =>
    SimulationLocalCall.fixed
      (simulationRetainedSupport C outside (retained.toList.take (k.val+1)).toFinset).card

def simulationLayerCalls (C : Finset Site) (layer retained : Finset (Site × Site)) :
    List SimulationLocalCall :=
  simulationLayerOutsideCalls C (layer \ retained) ++
    simulationLayerRetainedCalls C (layer \ retained) retained

lemma simulationLayerCalls_length (C : Finset Site)
    (layer retained : Finset (Site × Site)) (hr : retained ⊆ layer) :
    (simulationLayerCalls C layer retained).length = layer.card := by
  simp only [simulationLayerCalls,List.length_append,simulationLayerOutsideCalls,
    simulationLayerRetainedCalls,List.length_ofFn]
  exact Finset.card_sdiff_add_card_eq_card hr

lemma simulationLayerOutsideCalls_bound (C : Finset Site)
    (outside : Finset (Site × Site)) (W : ℕ) (hC : C.card ≤ 2*W+2) :
    ∀ call ∈ simulationLayerOutsideCalls C outside, call.coherent ≤ 2*W+4 := by
  intro call hc
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
  exact simulationOutsideSupport_temporary_card C _ _ W hC

lemma simulationLayerRetainedCalls_bound (C idle : Finset Site)
    (outside retained : Finset (Site × Site)) (W : ℕ)
    (hcover : ∀ x : Site, x ∈ simulationGateSites outside ∨
      x ∈ simulationGateSites retained ∨ x ∈ idle) (hi : idle.card ≤ 2)
    (hW : retained.card ≤ W) :
    ∀ call ∈ simulationLayerRetainedCalls C outside retained, call.coherent ≤ 2*W+4 := by
  intro call hc
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
  change (simulationRetainedSupport C outside (retained.toList.take (k.val+1)).toFinset).card ≤ _
  have hp : (retained.toList.take (k.val+1)).toFinset ⊆ retained := by
    intro p hp
    exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hp))
  have h := simulationRetainedSupport_card C idle outside retained _ hp hcover hi
  omega

lemma simulationBrickworkLayer_split_cover (c t : ℕ)
    (retained : Finset (BrickworkSite c × BrickworkSite c)) (x : BrickworkSite c) :
    x ∈ simulationGateSites (simulationBrickworkLayer c t \ retained) ∨
      x ∈ simulationGateSites retained ∨ x ∈ simulationIdleBoundary c := by
  rcases simulationBrickworkLayer_cover c t x with h | h
  · obtain ⟨p,hp,hx⟩ := mem_simulationGateSites.mp h
    by_cases hpr : p ∈ retained
    · exact Or.inr (Or.inl (mem_simulationGateSites.mpr ⟨p,hpr,hx⟩))
    · exact Or.inl (mem_simulationGateSites.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpr⟩,hx⟩)
  · exact Or.inr (Or.inr h)

/-- Coherent sites after successive physical layers, starting with no coherent
sites (all initial Pauli labels are classical). -/
def simulationCoherentAfter (c d : ℕ) (R : ℝ) : ℕ → Finset (BrickworkSite c)
  | 0 => ∅
  | t+1 => simulationRetainedSupport (simulationCoherentAfter c d R t)
      (simulationBrickworkLayer c (t+1) \ simulationRetainedLayer c d (t+1) R)
      (simulationRetainedLayer c d (t+1) R)

/-- Actual local arithmetic calls, with each coherent size computed from the
support evolution, in outside-first order within every layer. -/
def simulationCircuitCalls (c d : ℕ) (R : ℝ) : ℕ → List SimulationLocalCall
  | 0 => []
  | t+1 => simulationCircuitCalls c d R t ++
      simulationLayerCalls (simulationCoherentAfter c d R t)
        (simulationBrickworkLayer c (t+1)) (simulationRetainedLayer c d (t+1) R)

theorem simulationCoherentAfter_bound {c d : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hd : (d:ℝ)=5*(2*(c+1):ℕ)/3) (t : ℕ) :
    (simulationCoherentAfter c d R t).card ≤ 2*simulationWidthBudget (2*(c+1)) R+2 := by
  cases t with
  | zero => simp [simulationCoherentAfter]
  | succ t =>
    have h := simulationBrickworkLayer_coherent_card c (t+1)
      (simulationCoherentAfter c d R t) (simulationRetainedLayer c d (t+1) R)
    have hw := simulationRetainedLayer_le_budget (t:=t+1) hR hd
    change (simulationRetainedSupport _ _ _).card ≤ _
    omega

/-- Every generated call fits in the promised `2W+4` coherent sites. -/
theorem simulationCircuitCalls_bound {c d : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hd : (d:ℝ)=5*(2*(c+1):ℕ)/3) (t : ℕ) :
    ∀ call ∈ simulationCircuitCalls c d R t,
      call.coherent ≤ 2*simulationWidthBudget (2*(c+1)) R+4 := by
  induction t with
  | zero => simp [simulationCircuitCalls]
  | succ t ih =>
    intro call hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih call hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact simulationLayerOutsideCalls_bound _ _ _
          (simulationCoherentAfter_bound hR hd t) call hc
      · exact simulationLayerRetainedCalls_bound _ (simulationIdleBoundary c) _ _ _
          (simulationBrickworkLayer_split_cover c (t+1) _)
          Finset.card_le_two (simulationRetainedLayer_le_budget hR hd) call hc

lemma simulationBrickworkLayer_card_le (c t : ℕ) :
    (simulationBrickworkLayer c t).card ≤ c+1 := by
  unfold simulationBrickworkLayer
  split_ifs
  · have h := List.toFinset_card_le (brickworkOddBonds c)
    simpa [brickworkOddBonds] using h
  · have h := List.toFinset_card_le (brickworkEvenBonds c)
    have he : (brickworkEvenBonds c).length = c := by simp [brickworkEvenBonds]
    rw [he] at h
    omega

theorem simulationCircuitCalls_length_le (c d t : ℕ) (R : ℝ) :
    (simulationCircuitCalls c d R t).length ≤ t*(c+1) := by
  induction t with
  | zero => simp [simulationCircuitCalls]
  | succ t ih =>
    rw [simulationCircuitCalls,List.length_append,simulationLayerCalls_length]
    · have h := simulationBrickworkLayer_card_le c (t+1)
      nlinarith
    · exact Finset.filter_subset _ _

/-- The sampler's arithmetic-work bound on the explicitly generated call
schedule; no support-size or gate-count assumption remains. -/
theorem simulationCritical_sampleWork (s : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    simulationSampleWork (6*(s+1))
      (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
      (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1))) ≤
    180000*(6*(s+1))^2*4^(2*simulationWidthBudget (6*(s+1)) R+4) := by
  have hn : 2*(3*s+2+1)=6*(s+1) := by omega
  have hd : ((10*(s+1):ℕ):ℝ)=5*(2*(3*s+2+1):ℕ)/3 := by push_cast; ring
  have hc := simulationCircuitCalls_bound (R:=R) hR hd (10*(s+1))
  have hf := simulationCoherentAfter_bound (R:=R) hR hd (10*(s+1))
  rw [hn] at hc hf
  have h := simulationSampleWork_le (6*(s+1))
    (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
    (2*simulationWidthBudget (6*(s+1)) R+4) _ hc (by omega)
  have hl := simulationCircuitCalls_length_le (3*s+2) (10*(s+1)) (10*(s+1)) R
  have hq : (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1))).length+
      6*(s+1)+1 ≤ 2*(6*(s+1))^2 := by nlinarith
  have hm := Nat.mul_le_mul_right (90000*4^(2*simulationWidthBudget (6*(s+1)) R+4)) hq
  nlinarith

/-- Repeating the exact sampler `N` times and averaging its signs. -/
theorem simulationCritical_estimatorWork (s N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    simulationEstimatorWork N (6*(s+1))
      (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
      (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1))) ≤
    180002*(N+1)*(6*(s+1))^2*4^(2*simulationWidthBudget (6*(s+1)) R+4) := by
  have h := simulationCritical_sampleWork s hR
  have hm := Nat.mul_le_mul_left N h
  have hp : 1 ≤ (6*(s+1))^2*4^(2*simulationWidthBudget (6*(s+1)) R+4) := by
    apply Nat.one_le_iff_ne_zero.mpr
    positivity
  have hr : N+1 ≤ (N+1)*((6*(s+1))^2*4^(2*simulationWidthBudget (6*(s+1)) R+4)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold simulationEstimatorWork
  nlinarith

end
end Fluctuations
