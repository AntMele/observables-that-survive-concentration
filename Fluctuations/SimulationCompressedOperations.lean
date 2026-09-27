import Fluctuations.SimulationSamplerReorder
import Fluctuations.SimulationSamplerSupport
import Fluctuations.SimulationCost

open scoped BigOperators
namespace Fluctuations
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Restrict a full Pauli label assignment to the stored coherent coordinates. -/
def restrictCoherent (C : Finset Site) (P : PauliString Site) : ↥C → Fin 4 := fun s => P s

/-- Adjoin the stored classical labels to a coherent array index. -/
def extendCoherent (C : Finset Site) (labels : PauliString Site) (p : ↥C → Fin 4)
    (s : Site) : Fin 4 := if hs : s ∈ C then p ⟨s,hs⟩ else labels s

@[simp] theorem restrict_extendCoherent (C : Finset Site) (labels : PauliString Site)
    (p : ↥C → Fin 4) : restrictCoherent C (extendCoherent C labels p) = p := by
  funext s
  simp [restrictCoherent,extendCoherent,s.prop]

lemma extendCoherent_classical (C : Finset Site) (labels : PauliString Site)
    (p : ↥C → Fin 4) : ∀ s, s ∉ C → extendCoherent C labels p s = labels s := by
  intro s hs
  simp [extendCoherent,hs]

lemma extend_restrictCoherent (C : Finset Site) (labels P : PauliString Site)
    (hP : ∀ s, s ∉ C → P s = labels s) : extendCoherent C labels (restrictCoherent C P) = P := by
  funext s
  by_cases hs : s ∈ C
  · simp [extendCoherent,restrictCoherent,hs]
  · simp [extendCoherent,hs,hP s hs]

/-- Every full-space sum of an inflated function is exactly a sum over the
stored array. There is no hidden enumeration of classical coordinates. -/
theorem sum_inflatePauliAmplitude (C : Finset Site) (labels : PauliString Site)
    (v : compressedPauliAmplitude C) :
    (∑ P, inflatePauliAmplitude C labels v P) = ∑ p, v p := by
  unfold inflatePauliAmplitude
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun P _ => restrictCoherent C P)
  · intro P hP
    exact Finset.mem_univ _
  · intro P hP Q hQ he
    rw [← extend_restrictCoherent C labels P (Finset.mem_filter.mp hP).2,
      ← extend_restrictCoherent C labels Q (Finset.mem_filter.mp hQ).2,he]
  · intro p hp
    refine ⟨extendCoherent C labels p, ?_, restrict_extendCoherent C labels p⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,extendCoherent_classical C labels p⟩
  · intro P hP
    rfl

lemma coherent_update_classical (C : Finset Site) (labels P : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (a : TwoQubitPauliLabel) :
    (∀ s, s ∉ C → pauliPairReplace i j P a s = labels s) ↔
      ∀ s, s ∉ C → P s = labels s := by
  have hs (s : Site) (h : s ∉ C) : pauliPairReplace i j P a s = P s :=
    pauliPairReplace_apply_away i j s (fun he => h (he.symm ▸ hi))
      (fun he => h (he.symm ▸ hj)) P a
  constructor
  · intro h s hh
    simpa only [hs s hh] using h s hh
  · intro h s hh
    simpa only [hs s hh] using h s hh

lemma restrictCoherent_update (C : Finset Site) (P : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (a : TwoQubitPauliLabel) :
    restrictCoherent C (pauliPairReplace i j P a) =
      pauliPairReplace (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) (restrictCoherent C P) a := by
  funext s
  by_cases hsi : s.val=i <;> by_cases hsj : s.val=j <;>
    simp_all [restrictCoherent,pauliPairReplace,Function.update_apply,Subtype.ext_iff]

/-- Exact compressed retained-gate update: the 16-by-16 local transform on the
small coherent array inflates to the full physical coefficient update. -/
theorem pauliSamplerFixed_compressed (C : Finset Site) (labels : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j)
    (U : TwoQubitUnitary) (v : compressedPauliAmplitude C) :
    inflatePauliAmplitude C labels
      (pauliSamplerFixed (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
        (by exact fun h => hij (congrArg Subtype.val h)) U v) =
      pauliSamplerFixed i j hij U (inflatePauliAmplitude C labels v) := by
  funext P
  simp_rw [pauliSamplerFixed_eq_pairEvolution]
  unfold pauliPairEvolution
  change (if ∀ s, s ∉ C → P s=labels s then
    ∑ a, twoQubitPauliTransfer U (P i,P j) a *
      v (pauliPairReplace (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) (restrictCoherent C P) a)
    else 0) = _
  simp_rw [inflatePauliAmplitude,coherent_update_classical C labels P i j hi hj]
  by_cases hP : ∀ s, s ∉ C → P s=labels s
  · rw [if_pos hP]
    simp_rw [if_pos hP]
    apply Finset.sum_congr rfl
    intro a _
    rw [← restrictCoherent_update C P i j hi hj a]
    rfl
  · simp [hP]

/-- The local input marginal, exposed independently of branch weights. -/
def pauliSamplerInputMarginal (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (a : TwoQubitPauliLabel) : ℝ :=
  amplitudeMarginal (fun x => ψ ((pairSplitEquiv i j hij (Fin 4)).symm x)) a

lemma pauliSamplerInputMarginal_global_sum (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (a : TwoQubitPauliLabel) :
    pauliSamplerInputMarginal i j hij ψ a =
      ∑ P, if (P i,P j)=a then ψ P ^ 2 else 0 := by
  conv_rhs => rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm,
    Fintype.sum_prod_type]
  have he (b : TwoQubitPauliLabel) (s : PairSpectator i j → Fin 4) :
      (((pairSplitEquiv i j hij (Fin 4)).symm (b,s)) i,
       ((pairSplitEquiv i j hij (Fin 4)).symm (b,s)) j) = b := by
    simp [pairSplitEquiv,hij.symm]
  simp only [he,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  rfl

/-- All 16 Haar-input probabilities are obtained by summing squares of just
the compressed array; classical labels introduce no extra loops. -/
theorem pauliSamplerInputMarginal_compressed (C : Finset Site) (labels : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j)
    (v : compressedPauliAmplitude C) (a : TwoQubitPauliLabel) :
    pauliSamplerInputMarginal i j hij (inflatePauliAmplitude C labels v) a =
      pauliSamplerInputMarginal (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
        (by exact fun h => hij (congrArg Subtype.val h)) v a := by
  rw [pauliSamplerInputMarginal_global_sum,pauliSamplerInputMarginal_global_sum]
  let w : compressedPauliAmplitude C := fun p =>
    if (p ⟨i,hi⟩,p ⟨j,hj⟩)=a then v p ^ 2 else 0
  have he (P : PauliString Site) :
      (if (P i,P j)=a then (inflatePauliAmplitude C labels v P)^2 else 0) =
        inflatePauliAmplitude C labels w P := by
    unfold inflatePauliAmplitude
    by_cases hc : ∀ s, s ∉ C → P s = labels s
    · simp only [if_pos hc, w]
    · simp only [if_neg hc, zero_pow (by decide : 2 ≠ 0), ite_self]
  simp_rw [he]
  exact sum_inflatePauliAmplitude C labels w

lemma pauliSamplerBranch_of_nonzero (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel)
    (hq : pauliSamplerInputMarginal i j hij ψ ab.1 ≠ 0) (P : PauliString Site) :
    pauliSamplerBranch i j hij ψ ab P =
      if (P i,P j)=ab.2 then ψ (pauliPairReplace i j P ab.1) /
        Real.sqrt (pauliSamplerInputMarginal i j hij ψ ab.1) else 0 := by
  unfold pauliSamplerBranch amplitudeHaarBranch amplitudeConditional
  change (if (P i,P j)=ab.2 then
    (if pauliSamplerInputMarginal i j hij ψ ab.1 = 0 then _
     else ψ ((pairSplitEquiv i j hij (Fin 4)).symm (ab.1,fun s => P s)) /
       Real.sqrt (pauliSamplerInputMarginal i j hij ψ ab.1)) else 0) = _
  rw [if_neg hq,pairSplitEquiv_symm_pauli]
  rfl

/-- The finite input/output branch weights are computed on the same small
array as the marginal calculation. -/
theorem pauliSamplerWeight_compressed (C : Finset Site) (labels : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j)
    (v : compressedPauliAmplitude C) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel) :
    pauliSamplerWeight i j hij (inflatePauliAmplitude C labels v) ab =
      pauliSamplerWeight (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
        (by exact fun h => hij (congrArg Subtype.val h)) v ab := by
  change pauliSamplerInputMarginal i j hij (inflatePauliAmplitude C labels v) ab.1 * _ =
    pauliSamplerInputMarginal (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
      (by exact fun h => hij (congrArg Subtype.val h)) v ab.1 * _
  rw [pauliSamplerInputMarginal_compressed]

/-- On every realizable branch, normalizing the chosen slice of the small
array produces exactly the full physical Haar-sampler vector. The zero-mass
branch is deliberately excluded because it has zero sampling probability. -/
theorem pauliSamplerBranch_compressed (C : Finset Site) (labels : PauliString Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j)
    (v : compressedPauliAmplitude C) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel)
    (hq : pauliSamplerInputMarginal i j hij (inflatePauliAmplitude C labels v) ab.1 ≠ 0) :
    inflatePauliAmplitude C labels
      (pauliSamplerBranch (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
        (by exact fun h => hij (congrArg Subtype.val h)) v ab) =
      pauliSamplerBranch i j hij (inflatePauliAmplitude C labels v) ab := by
  have he := pauliSamplerInputMarginal_compressed C labels i j hi hj hij v ab.1
  have hlocal : pauliSamplerInputMarginal (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)
      (by exact fun h => hij (congrArg Subtype.val h)) v ab.1 ≠ 0 := by
    rw [← he]
    exact hq
  funext P
  rw [pauliSamplerBranch_of_nonzero i j hij _ ab hq]
  unfold inflatePauliAmplitude
  rw [pauliSamplerBranch_of_nonzero _ _ _ v ab hlocal]
  change (if ∀ s, s ∉ C → P s=labels s then
    (if (P i,P j)=ab.2 then
      v (pauliPairReplace (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) (restrictCoherent C P) ab.1) /
        Real.sqrt (pauliSamplerInputMarginal _ _ _ v ab.1) else 0) else 0) = _
  rw [← restrictCoherent_update C P i j hi hj ab.1]
  simp_rw [coherent_update_classical C labels P i j hi hj]
  unfold inflatePauliAmplitude at he
  rw [he]
  by_cases hc : ∀ s, s ∉ C → P s=labels s
  · simp only [if_pos hc]
    rfl
  · simp only [if_neg hc,zero_div,ite_self]

/-- The exact number of spectator coordinates after removing a distinct pair
from a coherent array. -/
theorem compressedPairSpectator_card (C : Finset Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) :
    Fintype.card (PairSpectator (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C)) = C.card-2 := by
  have hd : (⟨i,hi⟩ : ↥C) ≠ ⟨j,hj⟩ := fun h => hij (congrArg Subtype.val h)
  rw [Fintype.card_subtype]
  have he : ({s : ↥C | s ≠ ⟨i,hi⟩ ∧ s ≠ ⟨j,hj⟩} : Finset ↥C) =
      Finset.univ \ {⟨i,hi⟩,⟨j,hj⟩} := by
    ext s
    simp
  rw [he,Finset.card_sdiff]
  simp [hd]

/-- The conditional vector stored after a Haar gate has exactly `4^(m-2)`
entries, the spectator loop bound used by the arithmetic counter. -/
theorem compressedPairSpectator_entries (C : Finset Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) :
    Fintype.card (PairSpectator (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) → Fin 4) = 4^(C.card-2) := by
  rw [Fintype.card_fun,compressedPairSpectator_card C i j hi hj hij]
  rfl

/-- The two Pauli-pair indices really account for sixteen spectator slices;
there is no use of truncated subtraction at coherent sizes smaller than two. -/
theorem compressedPair_entries (C : Finset Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) :
    16*4^(C.card-2) = 4^C.card := by
  have hc : 2 ≤ C.card := by
    have hp : ({i,j}:Finset Site) ⊆ C := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hi
      · obtain rfl := Finset.mem_singleton.mp hx
        exact hj
    have hh := Finset.card_le_card hp
    simpa [hij] using hh
  have he : C.card = (C.card-2)+2 := by omega
  calc
    _ = 4^(C.card-2)*4^2 := by norm_num; ring
    _ = _ := by rw [←pow_add,←he]

/-- Enlarge a coherent register by adjoining classical basis labels. Every
new entry is obtained from an old entry or zero by indexing alone. -/
def enlargeCoherentArray (C D : Finset Site) (hCD : C ⊆ D) (labels : PauliString Site)
    (v : compressedPauliAmplitude C) : compressedPauliAmplitude D := fun p =>
  if ∀ s : ↥D, s.val ∉ C → p s = labels s then
    v (fun s => p ⟨s.val,hCD s.prop⟩) else 0

/-- Adjoining a gate's classical sites preserves the represented full vector
exactly; no global coefficient array need be built. -/
theorem enlargeCoherentArray_inflate (C D : Finset Site) (hCD : C ⊆ D)
    (labels : PauliString Site) (v : compressedPauliAmplitude C) :
    inflatePauliAmplitude D labels (enlargeCoherentArray C D hCD labels v) =
      inflatePauliAmplitude C labels v := by
  funext P
  unfold inflatePauliAmplitude enlargeCoherentArray
  by_cases hc : ∀ s, s ∉ C → P s=labels s
  · have hd : ∀ s, s ∉ D → P s=labels s := fun s hs => hc s (fun h => hs (hCD h))
    have hn : ∀ s : ↥D, s.val ∉ C → P s=labels s := fun s hs => hc s hs
    simp only [if_pos hc,if_pos hd,if_pos hn]
  · by_cases hd : ∀ s, s ∉ D → P s=labels s
    · have hn : ¬(∀ s : ↥D, s.val ∉ C → P s=labels s) := by
        intro h
        apply hc
        intro s hs
        by_cases hsd : s ∈ D
        · exact h ⟨s,hsd⟩ hs
        · exact hd s hsd
      simp only [if_neg hc,if_pos hd,if_neg hn]
    · simp only [if_neg hc,if_neg hd]

/-- Initial storage consists of one scalar and all classical initial labels. -/
theorem compressed_initial_vector (labels : PauliString Site) :
    inflatePauliAmplitude ∅ labels (fun _ => 1) = pauliInitialVector labels := by
  funext P
  unfold inflatePauliAmplitude pauliInitialVector
  have he : (∀ s, s ∉ (∅ : Finset Site) → P s=labels s) ↔ P=labels := by
    simp [funext_iff]
  by_cases hp : P=labels
  · subst P
    simp
  · simp only [if_neg hp,if_neg (he.not.mpr hp)]

/-- Squaring the final compressed array is the correct final categorical law.
Together with classical extension this is the full Pauli output, with no
sum over fixed classical labels. -/
theorem inflatePauliAmplitude_squared (C : Finset Site) (labels : PauliString Site)
    (v : compressedPauliAmplitude C) (P : PauliString Site) :
    (inflatePauliAmplitude C labels v P)^2 =
      inflatePauliAmplitude C labels (fun p => v p ^ 2) P := by
  unfold inflatePauliAmplitude
  split_ifs <;> simp

/-- The exact compressed fixed and averaged loops use precisely the spectator
entry count appearing in the checked arithmetic model. -/
theorem compressed_operation_work (C : Finset Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) :
    pauliFixedVectorWork
      (Fintype.card (PairSpectator (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) → Fin 4)) =
        31*(4^C.card) ∧
    pauliAveragedVectorWork
      (Fintype.card (PairSpectator (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) → Fin 4)) =
        33*4^(C.card-2)+3 := by
  rw [compressedPairSpectator_entries C i j hi hj hij,
    pauliFixedVectorWork_eq,pauliAveragedVectorWork_eq,compressedPair_entries C i j hi hj hij]
  exact ⟨rfl,rfl⟩

/-- A realizable finite branch cannot request normalization by a zero marginal. -/
theorem pauliSamplerWeight_ne_zero_marginal (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel)
    (h : pauliSamplerWeight i j hij ψ ab ≠ 0) :
    pauliSamplerInputMarginal i j hij ψ ab.1 ≠ 0 := by
  intro hq
  apply h
  change pauliSamplerInputMarginal i j hij ψ ab.1 * _ = 0
  rw [hq,zero_mul]

/-- Normalization of the actual full vector is equivalent to normalization
of its small stored array. -/
theorem inflatePauliAmplitude_normalized_iff (C : Finset Site) (labels : PauliString Site)
    (v : compressedPauliAmplitude C) :
    amplitudeNormalized (inflatePauliAmplitude C labels v) ↔ amplitudeNormalized v := by
  unfold amplitudeNormalized
  simp_rw [inflatePauliAmplitude_squared]
  rw [sum_inflatePauliAmplitude]

/-- Removing the two coherent gate coordinates is exactly reindexing the
spectator slice by the remaining coherent sites. -/
def compressedSpectatorEquiv (C : Finset Site)
    (i j : Site) (hi : i ∈ C) (hj : j ∈ C) :
    PairSpectator (⟨i,hi⟩ : ↥C) (⟨j,hj⟩ : ↥C) ≃ ↥(C \ {i,j}) where
  toFun s := ⟨s.val.val,Finset.mem_sdiff.mpr ⟨s.val.prop,by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨fun h => s.prop.1 (Subtype.ext h),fun h => s.prop.2 (Subtype.ext h)⟩⟩⟩
  invFun s := ⟨⟨s.val,(Finset.mem_sdiff.mp s.prop).1⟩,by
    have hs := (Finset.mem_sdiff.mp s.prop).2
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hs
    exact ⟨fun h => hs.1 (congrArg Subtype.val h),fun h => hs.2 (congrArg Subtype.val h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end Fluctuations
