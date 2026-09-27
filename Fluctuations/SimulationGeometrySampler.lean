import Fluctuations.SimulationGeometryCost
import Fluctuations.SimulationSamplerSupport
import Fluctuations.SimulationSamplerCovariance
import Fluctuations.SimulationMixedCircuit

/-! Connect the generated support/cost schedule to the actual finite branching
sampler. Every positive-probability trajectory has the compressed representation
used in the cost proof; zero-probability fallback vectors are never charged as
realized trajectories. -/
namespace Fluctuations
noncomputable section
set_option linter.unusedSectionVars false
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- All branches which can actually be drawn admit the same coherent-site set;
the classical labels can depend on the drawn branch. -/
def simulationEnsembleSupported (C : Finset Site)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) : Prop :=
  ∀ x, E.weight x ≠ 0 → ∃ labels, amplitudeSupported C labels (E.vector x)

theorem simulationEnsembleSupported_step (C : Finset Site)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) (hE : simulationEnsembleSupported C E)
    (i j : Site) (hij : i ≠ j) (retained : Bool) (U : TwoQubitUnitary) :
    simulationEnsembleSupported (if retained then C ∪ {i,j} else C \ {i,j})
      (pauliSamplerStep i j hij retained U E) := by
  cases retained
  · simp only [Bool.false_eq_true,↓reduceIte,pauliSamplerStep]
    intro x hx
    have hleft : E.weight x.1 ≠ 0 := by
      intro he
      exact hx (by simp [FiniteAmplitudeEnsemble.bind,he])
    have hright : pauliSamplerWeight i j hij (E.vector x.1) x.2 ≠ 0 := by
      intro he
      exact hx (by simp [FiniteAmplitudeEnsemble.bind,he])
    obtain ⟨labels,hl⟩ := hE x.1 hleft
    exact ⟨pauliPairUpdate i j labels x.2.2,
      pauliSamplerBranch_supported i j hij C labels _ hl x.2 hright⟩
  · simp only [↓reduceIte,pauliSamplerStep]
    intro x hx
    obtain ⟨labels,hl⟩ := hE x hx
    exact ⟨labels,pauliSamplerFixed_supported i j hij C labels U _ hl⟩

/-- Invalid self-bonds are harmless identity calls. They never occur in the
physical schedule; this total definition avoids proof-dependent list indices. -/
def simulationPairEnsembleStep (retained : Bool) (U : TwoQubitUnitary)
    (p : Site × Site) (E : FiniteAmplitudeEnsemble (PauliString Site)) :=
  if hij : p.1 ≠ p.2 then pauliSamplerStep p.1 p.2 hij retained U E else E

def simulationListEnsemble (retained : Bool) (gates : Site × Site → TwoQubitUnitary)
    (word : List (Site × Site)) (E : FiniteAmplitudeEnsemble (PauliString Site)) :=
  word.foldl (fun E p => simulationPairEnsembleStep retained (gates p) p E) E

def simulationListSupport (retained : Bool) (word : List (Site × Site)) (C : Finset Site) :=
  word.foldl (fun C p => if retained then C ∪ {p.1,p.2} else C \ {p.1,p.2}) C

/-- The complete branching law follows exactly the same deterministic coherent
support recursion as the arithmetic-call trace. -/
theorem simulationListEnsemble_supported (retained : Bool)
    (gates : Site × Site → TwoQubitUnitary) (word : List (Site × Site))
    (hword : ∀ p ∈ word, p.1 ≠ p.2) (C : Finset Site)
    (E : FiniteAmplitudeEnsemble (PauliString Site)) (hE : simulationEnsembleSupported C E) :
    simulationEnsembleSupported (simulationListSupport retained word C)
      (simulationListEnsemble retained gates word E) := by
  induction word generalizing C E with
  | nil => exact hE
  | cons p word ih =>
    have hp := hword p (by simp)
    have hs := simulationEnsembleSupported_step C E hE p.1 p.2 hp retained (gates p)
    have he : simulationPairEnsembleStep retained (gates p) p E =
        pauliSamplerStep p.1 p.2 hp retained (gates p) E := by
      simp [simulationPairEnsembleStep,hp]
    simp only [simulationListSupport,simulationListEnsemble,List.foldl_cons]
    rw [he]
    exact ih (fun q hq => hword q (by simp [hq])) _ _ hs

lemma simulationListSupport_outside (word : List (Site × Site)) (C : Finset Site) :
    simulationListSupport false word C = simulationOutsideSupport C word.toFinset := by
  induction word generalizing C with
  | nil => simp [simulationListSupport,simulationOutsideSupport,simulationGateSites]
  | cons p word ih =>
    change simulationListSupport false word (C \ {p.1,p.2}) = _
    rw [ih]
    ext x
    simp [simulationOutsideSupport,simulationGateSites]
    tauto

lemma simulationListSupport_retained (word : List (Site × Site)) (C : Finset Site) :
    simulationListSupport true word C = C ∪ simulationGateSites word.toFinset := by
  induction word generalizing C with
  | nil => simp [simulationListSupport,simulationGateSites]
  | cons p word ih =>
    change simulationListSupport true word (C ∪ {p.1,p.2}) = _
    rw [ih]
    ext x
    simp [simulationGateSites]

lemma simulationBrickworkLayer_distinct (c t : ℕ)
    (p : BrickworkSite c × BrickworkSite c) (hp : p ∈ simulationBrickworkLayer c t) :
    p.1 ≠ p.2 := by
  unfold simulationBrickworkLayer at hp
  split_ifs at hp
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    simp [brickworkOddBond]
  · obtain ⟨a,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hp)
    simp [brickworkEvenBond]

/-- The outside-first implementation of one actual physical layer. -/
def simulationPhysicalLayerEnsemble (c d t : ℕ) (R : ℝ)
    (gates : BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (E : FiniteAmplitudeEnsemble (PauliString (BrickworkSite c))) :=
  simulationListEnsemble true gates (simulationRetainedLayer c d t R).toList
    (simulationListEnsemble false gates
      (simulationBrickworkLayer c t \ simulationRetainedLayer c d t R).toList E)

theorem simulationPhysicalLayerEnsemble_supported (c d t : ℕ) (R : ℝ)
    (gates : BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (C : Finset (BrickworkSite c))
    (E : FiniteAmplitudeEnsemble (PauliString (BrickworkSite c)))
    (hE : simulationEnsembleSupported C E) :
    simulationEnsembleSupported
      (simulationRetainedSupport C
        (simulationBrickworkLayer c t \ simulationRetainedLayer c d t R)
        (simulationRetainedLayer c d t R))
      (simulationPhysicalLayerEnsemble c d t R gates E) := by
  have ho := simulationListEnsemble_supported false gates
    (simulationBrickworkLayer c t \ simulationRetainedLayer c d t R).toList
    (fun p hp => simulationBrickworkLayer_distinct c t p
      (Finset.mem_sdiff.mp (Finset.mem_toList.mp hp)).1) C E hE
  rw [simulationListSupport_outside,Finset.toList_toFinset] at ho
  have hr := simulationListEnsemble_supported true gates
    (simulationRetainedLayer c d t R).toList
    (fun p hp => simulationBrickworkLayer_distinct c t p
      (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).1) _ _ ho
  rw [simulationListSupport_retained,Finset.toList_toFinset] at hr
  exact hr

/-- Actual sampled-vector law through the reordered physical layers. -/
def simulationPhysicalEnsemble (c d : ℕ) (R : ℝ)
    (gates : ℕ → BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (P₀ : PauliString (BrickworkSite c)) : ℕ → FiniteAmplitudeEnsemble (PauliString (BrickworkSite c))
  | 0 => amplitudePoint (pauliInitialVector P₀) (pauliInitialVector_normalized P₀)
  | t+1 => simulationPhysicalLayerEnsemble c d (t+1) R (gates (t+1))
      (simulationPhysicalEnsemble c d R gates P₀ t)

theorem simulationPhysicalEnsemble_supported (c d : ℕ) (R : ℝ)
    (gates : ℕ → BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (P₀ : PauliString (BrickworkSite c)) (t : ℕ) :
    simulationEnsembleSupported (simulationCoherentAfter c d R t)
      (simulationPhysicalEnsemble c d R gates P₀ t) := by
  induction t with
  | zero =>
    intro x hx
    refine ⟨P₀,?_⟩
    intro P s hs hne
    have hp : P ≠ P₀ := by intro h; exact hne (congrFun h s)
    simp [simulationPhysicalEnsemble,amplitudePoint,pauliInitialVector,hp]
  | succ t ih => exact simulationPhysicalLayerEnsemble_supported c d (t+1) R _ _ _ ih

/-- Every realizable trajectory of the same sampler has an exact compressed
vector with at most `4^(2W+2)` entries at the end of every layer. -/
theorem simulationPhysicalEnsemble_compressed {c d : ℕ} {R : ℝ}
    (hR : 0≤R) (hd : (d:ℝ)=5*(2*(c+1):ℕ)/3)
    (gates : ℕ → BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (P₀ : PauliString (BrickworkSite c)) (t : ℕ)
    (x : (simulationPhysicalEnsemble c d R gates P₀ t).Index)
    (hx : (simulationPhysicalEnsemble c d R gates P₀ t).weight x ≠ 0) :
    ∃ labels, ∃ v : compressedPauliAmplitude (simulationCoherentAfter c d R t),
      inflatePauliAmplitude (simulationCoherentAfter c d R t) labels v =
        (simulationPhysicalEnsemble c d R gates P₀ t).vector x ∧
      Fintype.card (↥(simulationCoherentAfter c d R t) → Fin 4) ≤
        4^(2*simulationWidthBudget (2*(c+1)) R+2) := by
  obtain ⟨labels,hl⟩ := simulationPhysicalEnsemble_supported c d R gates P₀ t x hx
  obtain ⟨v,hv⟩ := amplitudeSupported_compress _ labels _ hl
  refine ⟨labels,v,hv,?_⟩
  rw [compressedPauliAmplitude_entries]
  exact Nat.pow_le_pow_right (by decide) (simulationCoherentAfter_bound hR hd t)

/-- Outside calls include both distinct gate sites before marginalizing. -/
lemma simulationLayerOutsideCalls_size_two (C : Finset Site)
    (outside : Finset (Site × Site)) (hv : ∀ p ∈ outside, p.1 ≠ p.2) :
    ∀ call ∈ simulationLayerOutsideCalls C outside, 2 ≤ call.coherent := by
  intro call hc
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
  let p := outside.toList[k.val]'(by simp)
  have hp : p ∈ outside := Finset.mem_toList.mp (List.getElem_mem (by simp))
  have hcard := Finset.card_pair (hv p hp)
  have hs : ({p.1,p.2}:Finset Site) ⊆
      simulationOutsideSupport C (outside.toList.take k.val).toFinset ∪ {p.1,p.2} :=
    Finset.subset_union_right
  have hh := Finset.card_le_card hs
  rw [hcard] at hh
  exact hh

/-- Every retained call has already adjoined the current gate's two sites. -/
lemma simulationLayerRetainedCalls_size_two (C : Finset Site)
    (outside retained : Finset (Site × Site)) (hv : ∀ p ∈ retained, p.1 ≠ p.2) :
    ∀ call ∈ simulationLayerRetainedCalls C outside retained, 2 ≤ call.coherent := by
  intro call hc
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
  let p := retained.toList[k.val]'(by simp)
  have hp : p ∈ retained := Finset.mem_toList.mp (List.getElem_mem (by simp))
  have hpre : p ∈ (retained.toList.take (k.val+1)).toFinset := by
    apply List.mem_toFinset.mpr
    apply List.mem_take_iff_getElem.mpr
    refine ⟨k.val,?_,rfl⟩
    simp
  have hsub : ({p.1,p.2}:Finset Site) ⊆
      simulationRetainedSupport C outside (retained.toList.take (k.val+1)).toFinset := by
    intro x hx
    apply Finset.mem_union_right
    apply mem_simulationGateSites.mpr
    exact ⟨p,hpre,by simpa using hx⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_pair (hv p hp)] at hh
  exact hh

/-- Every generated physical call admits the exact local/spectator indexing
with 16 local Pauli states; there are never fewer than two coherent sites. -/
theorem simulationCircuitCalls_size_two (c d t : ℕ) (R : ℝ) :
    ∀ call ∈ simulationCircuitCalls c d R t, 2 ≤ call.coherent := by
  induction t with
  | zero => simp [simulationCircuitCalls]
  | succ t ih =>
    intro call hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih call hc
    · rcases List.mem_append.mp hc with hc | hc
      · apply simulationLayerOutsideCalls_size_two _ _ _ call hc
        intro p hp
        exact simulationBrickworkLayer_distinct c (t+1) p (Finset.mem_sdiff.mp hp).1
      · apply simulationLayerRetainedCalls_size_two _ _ _ _ call hc
        intro p hp
        exact simulationBrickworkLayer_distinct c (t+1) p (Finset.mem_filter.mp hp).1

/-- Exactly the local-16 by spectator-array factorization used in the loop
operation counts, for every actual generated call. -/
theorem simulationCircuitCalls_entry_factorization (c d t : ℕ) (R : ℝ)
    (call : SimulationLocalCall) (hc : call ∈ simulationCircuitCalls c d R t) :
    16*4^(call.coherent-2) = 4^call.coherent := by
  have hm := simulationCircuitCalls_size_two c d t R call hc
  rw [show (16:ℕ)=4^2 by norm_num,←pow_add]
  congr 1
  omega

end
end Fluctuations
