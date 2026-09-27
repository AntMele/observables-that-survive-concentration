import Fluctuations.SimulationSampler

open scoped BigOperators
namespace Fluctuations
set_option linter.unusedSectionVars false

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Outside the coherent set every site has a definite classical Pauli label.
This is a compressed-vector representation invariant, not a sparsity guess. -/
def amplitudeSupported (C : Finset Site) (labels : PauliString Site)
    (ψ : PauliString Site → ℝ) : Prop :=
  ∀ P s, s ∉ C → P s ≠ labels s → ψ P = 0

theorem pauliSamplerFixed_supported (i j : Site) (hij : i ≠ j)
    (C : Finset Site) (labels : PauliString Site) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeSupported C labels ψ) :
    amplitudeSupported (C ∪ {i,j}) labels (pauliSamplerFixed i j hij U ψ) := by
  intro P s hs hlabel
  have hC : s ∉ C := fun h => hs (Finset.mem_union_left _ h)
  have hsi : s ≠ i := by intro h; subst s; simp at hs
  have hsj : s ≠ j := by intro h; subst s; simp at hs
  unfold pauliSamplerFixed amplitudeLocalUpdate
  apply Finset.sum_eq_zero
  intro a _
  change twoQubitPauliTransfer U (P i,P j) a *
    ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a, fun s => P s)) = 0
  rw [pairSplitEquiv_symm_pauli]
  rw [hψ _ s hC (by simpa [pauliPairUpdate_other i j s hsi hsj] using hlabel)]
  simp

/-- Every positive-probability Haar branch removes the gate's two qubits from
the coherent register and stores its sampled output pair classically. -/
theorem pauliSamplerBranch_supported (i j : Site) (hij : i ≠ j)
    (C : Finset Site) (labels : PauliString Site)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeSupported C labels ψ)
    (ab : TwoQubitPauliLabel × TwoQubitPauliLabel)
    (hab : pauliSamplerWeight i j hij ψ ab ≠ 0) :
    amplitudeSupported (C \ {i,j}) (pauliPairUpdate i j labels ab.2)
      (pauliSamplerBranch i j hij ψ ab) := by
  intro P s hs hlabel
  let e := pairSplitEquiv i j hij (Fin 4)
  have hq : amplitudeMarginal (fun x => ψ (e.symm x)) ab.1 ≠ 0 := by
    intro h
    exact hab (by simp [pauliSamplerWeight, amplitudeHaarWeight, e] at h ⊢; exact Or.inl h)
  unfold pauliSamplerBranch amplitudeHaarBranch amplitudeConditional
  change (if (P i,P j) = ab.2 then
    (if amplitudeMarginal (fun x => ψ (e.symm x)) ab.1 = 0 then _
    else ψ (e.symm (ab.1, fun s => P s)) /
      Real.sqrt (amplitudeMarginal (fun x => ψ (e.symm x)) ab.1)) else 0) = 0
  rw [if_neg hq]
  by_cases hpair : (P i,P j) = ab.2
  · rw [if_pos hpair]
    by_cases hsi : s = i
    · subst s
      exact (hlabel (by simpa [pauliPairUpdate_left i j hij] using congrArg Prod.fst hpair)).elim
    by_cases hsj : s = j
    · subst s
      exact (hlabel (by simpa using congrArg Prod.snd hpair)).elim
    have hC : s ∉ C := by
      intro hc
      exact hs (Finset.mem_sdiff.mpr ⟨hc, by simp [hsi,hsj]⟩)
    have hp : P s ≠ labels s := by
      simpa [pauliPairUpdate_other i j s hsi hsj] using hlabel
    change ψ ((pairSplitEquiv i j hij (Fin 4)).symm (ab.1,fun s => P s)) / _ = 0
    rw [pairSplitEquiv_symm_pauli,
      hψ _ s hC (by simpa [pauliPairUpdate_other i j s hsi hsj] using hp), zero_div]
  · simp [hpair]

/-- The coherent representation stores precisely one real amplitude per
assignment of Pauli labels to the coherent set. -/
def compressedPauliAmplitude (C : Finset Site) := (↥C → Fin 4) → ℝ

theorem compressedPauliAmplitude_entries (C : Finset Site) :
    Fintype.card (↥C → Fin 4) = 4 ^ C.card := by
  simp

/-- Inflate a stored coherent vector by adjoining fixed classical labels. -/
noncomputable def inflatePauliAmplitude (C : Finset Site) (labels : PauliString Site)
    (v : compressedPauliAmplitude C) (P : PauliString Site) : ℝ :=
  if ∀ s, s ∉ C → P s = labels s then v (fun s => P s) else 0

/-- Every vector satisfying the support invariant has this explicit compressed
representation; no density matrix or exponentially large mixture is stored. -/
theorem amplitudeSupported_compress (C : Finset Site) (labels : PauliString Site)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeSupported C labels ψ) :
    ∃ v : compressedPauliAmplitude C, inflatePauliAmplitude C labels v = ψ := by
  classical
  let extend (p : ↥C → Fin 4) (s : Site) := if hs : s ∈ C then p ⟨s,hs⟩ else labels s
  refine ⟨fun p => ψ (extend p), ?_⟩
  funext P
  unfold inflatePauliAmplitude
  by_cases hp : ∀ s, s ∉ C → P s = labels s
  · rw [if_pos hp]
    change ψ (extend (fun s => P s)) = ψ P
    congr 1
    funext s
    by_cases hs : s ∈ C
    · simp [extend,hs]
    · simpa [extend,hs] using (hp s hs).symm
  · rw [if_neg hp]
    push_neg at hp
    obtain ⟨s,hs,hne⟩ := hp
    exact (hψ P s hs hne).symm

end Fluctuations
