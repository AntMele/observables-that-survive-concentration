import Fluctuations.SimulationGeometryReorder
import Fluctuations.SimulationMixedListIndex
import Fluctuations.SimulationGateCoordinates
import Fluctuations.SimulationSamplingKernel

/-! Identification of the inexpensive outside-first sampler with the
chronological physical mixed-circuit law used for accuracy. -/
open MeasureTheory ProbabilityTheory
namespace Fluctuations
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000

/-- Chronological coordinate of a physical bond in its one-based layer.
Only matching-layer members are used by the sampler. -/
def simulationPhysicalGateIndex (c t : ℕ) (p : BrickworkSite c × BrickworkSite c) : ℕ :=
  ((t-1)/2)*(2*c+1)+(if t%2=1 then 0 else c+1)+p.1.1.val

/-- The outside-first sampler reads each retained matrix from the same input
coordinate as the original chronological circuit. -/
def simulationPhysicalGateInput (c T : ℕ) (x : Fin (T*(2*c+1)) → TwoQubitUnitary)
    (t : ℕ) (p : BrickworkSite c × BrickworkSite c) : TwoQubitUnitary :=
  simulationFixedGates (T*(2*c+1)) x (simulationPhysicalGateIndex c t p)

lemma simulationPhysicalGateIndex_odd (c s : ℕ) (a : Fin (c+1)) :
    simulationPhysicalGateIndex c (2*s+1) (brickworkOddBond a) = s*(2*c+1)+a.val := by
  simp [simulationPhysicalGateIndex,brickworkOddBond]

lemma simulationPhysicalGateIndex_even (c s : ℕ) (a : Fin c) :
    simulationPhysicalGateIndex c (2*s+2) (brickworkEvenBond a) = s*(2*c+1)+(c+1)+a.val := by
  have hdiv : (2*s+2-1)/2=s := by omega
  have hmod : (2*s+2)%2≠1 := by omega
  unfold simulationPhysicalGateIndex
  rw [hdiv,if_neg hmod]
  rfl

lemma simulationOddBond_mem_layer (c s : ℕ) (a : Fin (c+1)) :
    brickworkOddBond a ∈ simulationBrickworkLayer c (2*s+1) := by
  unfold simulationBrickworkLayer
  rw [if_pos (by omega)]
  exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨a,rfl⟩)

lemma simulationEvenBond_mem_layer (c s : ℕ) (a : Fin c) :
    brickworkEvenBond a ∈ simulationBrickworkLayer c (2*s+2) := by
  unfold simulationBrickworkLayer
  rw [if_neg (by omega)]
  exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨a,rfl⟩)

lemma simulationPhysicalRetained_coordinate (c T t : ℕ) (R : ℝ)
    (z : Fin (T*(2*c+1))) (p : BrickworkSite c × BrickworkSite c)
    (ht : simulationGateTime c T z=t) (hp : brickworkCircuitBond c T z.val=p)
    (hm : p ∈ simulationBrickworkLayer c t) :
    decide (p ∈ simulationRetainedLayer c (2*T) t R) = simulationRetainedSchedule c T R z.val := by
  rw [simulationRetainedSchedule_at]
  congr 1
  apply propext
  simp only [simulationRetainedLayer,Finset.mem_filter,hm,true_and,simulationRetainedGate]
  rw [simulationGatePosition_eq_bondPosition,ht,hp]

lemma simulationPhysicalRetained_odd (c T s : ℕ) (hs : s<T) (R : ℝ) (a : Fin (c+1)) :
    decide (brickworkOddBond a ∈ simulationRetainedLayer c (2*T) (2*s+1) R) =
      simulationRetainedSchedule c T R (s*(2*c+1)+a.val) := by
  have hn : s*(2*c+1)+a.val<T*(2*c+1) := by
    have h := Nat.mul_le_mul_right (2*c+1) (show s+1≤T by omega)
    have ha:=a.isLt
    nlinarith
  let z : Fin (T*(2*c+1)) := ⟨s*(2*c+1)+a.val,hn⟩
  obtain ⟨ht,_,hb⟩ := simulationGate_odd_coordinates c T s hs a z rfl
  exact simulationPhysicalRetained_coordinate c T (2*s+1) R z (brickworkOddBond a)
    ht hb (simulationOddBond_mem_layer c s a)

lemma simulationPhysicalRetained_even (c T s : ℕ) (hs : s<T) (R : ℝ) (a : Fin c) :
    decide (brickworkEvenBond a ∈ simulationRetainedLayer c (2*T) (2*s+2) R) =
      simulationRetainedSchedule c T R (s*(2*c+1)+(c+1)+a.val) := by
  have hn : s*(2*c+1)+(c+1)+a.val<T*(2*c+1) := by
    have h := Nat.mul_le_mul_right (2*c+1) (show s+1≤T by omega)
    have ha:=a.isLt
    nlinarith
  let z : Fin (T*(2*c+1)) := ⟨s*(2*c+1)+(c+1)+a.val,hn⟩
  obtain ⟨ht,_,hb⟩ := simulationGate_even_coordinates c T s hs a z rfl
  exact simulationPhysicalRetained_coordinate c T (2*s+2) R z (brickworkEvenBond a)
    ht hb (simulationEvenBond_mem_layer c s a)

/-- Within every actual physical layer the full ensemble covariance is
unchanged by the exact outside-first lists traversed by the cost model. -/
theorem simulationPhysicalLayerEnsemble_covariance (c d t : ℕ) (R : ℝ)
    (gates : BrickworkSite c × BrickworkSite c → TwoQubitUnitary)
    (E : FiniteAmplitudeEnsemble (PauliString (BrickworkSite c))) :
    (simulationPhysicalLayerEnsemble c d t R gates E).covariance =
      (simulationMixedListEnsemble
        (fun p => decide (p ∈ simulationRetainedLayer c d t R)) gates
        (simulationChronologicalLayer c t) E).covariance := by
  have hset : (simulationChronologicalLayer c t).toFinset = simulationBrickworkLayer c t := by
    unfold simulationChronologicalLayer simulationBrickworkLayer
    split_ifs <;> rfl
  have hp := (List.toFinset_toList (simulationChronologicalLayer_nodup c t)).symm
  rw [hset] at hp
  have hperm := hp.trans (simulationOutsideRetained_perm (simulationBrickworkLayer c t)
    (simulationRetainedLayer c d t R) (Finset.filter_subset _ _))
  symm
  apply simulationMixedListEnsemble_outside_covariance _ gates _ _ _ hperm
  · intro p hp
    have hh := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hp)).2
    simp [hh]
  · intro p hp
    have hh := Finset.mem_toList.mp hp
    simp [hh]
  · intro p hp q hq he
    apply simulationBrickworkLayer_matching c t p q
    · rw [←hset]; exact List.mem_toFinset.mpr hp
    · rw [←hset]; exact List.mem_toFinset.mpr hq
    · exact he

/-- At every completed physical period, the inexpensive outside-first sampler
and the original chronological sampler have identical full covariance. -/
theorem simulationPhysicalEnsemble_covariance_prefix (c T : ℕ) (R : ℝ)
    (x : Fin (T*(2*c+1)) → TwoQubitUnitary) (P₀ : PauliString (BrickworkSite c))
    (s : ℕ) (hs : s≤T) :
    (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*s)).covariance =
      (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (s*(2*c+1))).covariance := by
  induction s with
  | zero => simp only [Nat.zero_mul,simulationPhysicalEnsemble,mixedPauliSampler]
  | succ s ih =>
    have hst : s<T := by omega
    have hprev := ih (by omega)
    have hodd :
        (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*s+1)).covariance =
          (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
            (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
            (s*(2*c+1)+(c+1))).covariance := by
      rw [simulationPhysicalEnsemble,simulationPhysicalLayerEnsemble_covariance]
      have he : simulationChronologicalLayer c (2*s+1)=brickworkOddBonds c := by
        simp [simulationChronologicalLayer]
      rw [he]
      exact simulationMixedListEnsemble_ofFn_covariance
        (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (s*(2*c+1)) (c+1) brickworkOddBond
        (fun p => decide (p ∈ simulationRetainedLayer c (2*T) (2*s+1) R))
        (simulationPhysicalGateInput c T x (2*s+1))
        (fun a => (brickworkCircuitBond_odd c T s a hst).symm)
        (fun a => simulationPhysicalRetained_odd c T s hst R a)
        (fun a => by rw [simulationPhysicalGateInput,simulationPhysicalGateIndex_odd])
        _ hprev
    have heven :
        (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*s+2)).covariance =
          (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
            (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
            (s*(2*c+1)+(c+1)+c)).covariance := by
      have ht : 2*s+2=(2*s+1)+1 := by omega
      rw [ht,simulationPhysicalEnsemble,simulationPhysicalLayerEnsemble_covariance]
      have he : simulationChronologicalLayer c (2*s+1+1)=brickworkEvenBonds c := by
        unfold simulationChronologicalLayer
        rw [if_neg (by omega)]
      rw [he]
      apply simulationMixedListEnsemble_ofFn_covariance
        (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (s*(2*c+1)+(c+1)) c brickworkEvenBond
        (fun p => decide (p ∈ simulationRetainedLayer c (2*T) (2*s+1+1) R))
        (simulationPhysicalGateInput c T x (2*s+1+1))
      · intro a
        exact (brickworkCircuitBond_even c T s a hst).symm
      · intro a
        exact simulationPhysicalRetained_even c T s hst R a
      · intro a
        change simulationFixedGates _ x (simulationPhysicalGateIndex c (2*s+2) (brickworkEvenBond a)) = _
        rw [simulationPhysicalGateIndex_even]
      · exact hodd
    rw [show 2*(s+1)=2*s+2 by omega,
      show (s+1)*(2*c+1)=s*(2*c+1)+(c+1)+c by ring]
    exact heven

/-- Full physical covariance identity: the same cheap sampler analyzed by the
operation-count theorem has exactly the law used by the accuracy theorem. -/
theorem simulationPhysicalEnsemble_covariance (c T : ℕ) (R : ℝ)
    (x : Fin (T*(2*c+1)) → TwoQubitUnitary) (P₀ : PauliString (BrickworkSite c)) :
    (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T)).covariance =
      (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (T*(2*c+1))).covariance :=
  simulationPhysicalEnsemble_covariance_prefix c T R x P₀ T le_rfl

/-- In particular the exact output probability of every full Pauli string
agrees. Internal branch-index types and zero-weight fallbacks are irrelevant. -/
theorem simulationPhysicalEnsemble_probability (c T : ℕ) (R : ℝ)
    (x : Fin (T*(2*c+1)) → TwoQubitUnitary) (P₀ : PauliString (BrickworkSite c))
    (P : PauliString (BrickworkSite c)) :
    (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T)).probability P =
      (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (T*(2*c+1))).probability P := by
  unfold FiniteAmplitudeEnsemble.probability
  rw [simulationPhysicalEnsemble_covariance]

/-- The physical implementation's output PMF equals the canonical mixed law. -/
theorem simulationPhysicalEnsemble_outputPMF (c T : ℕ) (R : ℝ)
    (x : Fin (T*(2*c+1)) → TwoQubitUnitary) (P₀ : PauliString (BrickworkSite c)) :
    amplitudeOutputPMF
      (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T)) =
      amplitudeOutputPMF
      (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
        (T*(2*c+1))) := by
  ext P
  change ENNReal.ofReal
    ((simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T)).probability P) =
    ENNReal.ofReal
    ((mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
      (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀
      (T*(2*c+1))).probability P)
  rw [simulationPhysicalEnsemble_probability]

/-- The physical implementation's output law depends continuously on the input
circuit, including across zero-weight internal branches. -/
theorem simulationPhysicalEnsemble_probability_continuous (c T : ℕ) (R : ℝ)
    (P₀ : PauliString (BrickworkSite c)) (P : PauliString (BrickworkSite c)) :
    Continuous (fun x : Fin (T*(2*c+1)) → TwoQubitUnitary =>
      (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T)).probability P) := by
  simp_rw [simulationPhysicalEnsemble_probability]
  exact mixedPauliSampler_probability_continuous (brickworkCircuitBond c T)
    (brickworkCircuitBond_distinct c T) (simulationRetainedSchedule c T R) P₀ _ P

/-- The genuine joint-law kernel of the physically costed outside-first
algorithm, independently repeated N times. -/
def simulationPhysicalSamplerKernel (c T : ℕ) (R : ℝ)
    (P₀ : PauliString (BrickworkSite c)) (N : ℕ) :
    Kernel (Fin (T*(2*c+1)) → TwoQubitUnitary) (Fin N → PauliString (BrickworkSite c)) :=
  amplitudeOutputKernel
    (fun x => simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T))
    (fun P => (simulationPhysicalEnsemble_probability_continuous c T R P₀ P).measurable) N

instance simulationPhysicalSamplerKernel_isMarkov (c T : ℕ) (R : ℝ)
    (P₀ : PauliString (BrickworkSite c)) (N : ℕ) :
    IsMarkovKernel (simulationPhysicalSamplerKernel c T R P₀ N) := by
  unfold simulationPhysicalSamplerKernel
  infer_instance

/-- Equality of the physical algorithm's probability kernel with the
chronological law used to prove the bias and concentration estimates. -/
theorem simulationPhysicalSamplerKernel_eq (c T : ℕ) (R : ℝ)
    (P₀ : PauliString (BrickworkSite c)) (N : ℕ) :
    simulationPhysicalSamplerKernel c T R P₀ N =
      mixedPauliSamplerKernel (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
        (simulationRetainedSchedule c T R) P₀ (T*(2*c+1)) N := by
  ext x s hs
  change (Measure.pi (fun _ : Fin N =>
    (amplitudeOutputPMF (simulationPhysicalEnsemble c (2*T) R (simulationPhysicalGateInput c T x) P₀ (2*T))).toMeasure)) s =
    (Measure.pi (fun _ : Fin N =>
    (amplitudeOutputPMF (mixedPauliSampler (brickworkCircuitBond c T) (brickworkCircuitBond_distinct c T)
      (simulationRetainedSchedule c T R) (simulationFixedGates (T*(2*c+1)) x) P₀ (T*(2*c+1)))).toMeasure)) s
  simp_rw [simulationPhysicalEnsemble_outputPMF]

end
end Fluctuations
