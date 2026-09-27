import Fluctuations.SimulationMixedCircuit
import Fluctuations.PauliPairCommutation

open scoped BigOperators
namespace Fluctuations
set_option linter.unusedSectionVars false
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma pauliSamplerFixed_eq_pairEvolution (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) :
    pauliSamplerFixed i j hij U ψ = pauliPairEvolution i j (twoQubitPauliTransfer U) ψ := by
  funext P
  unfold pauliSamplerFixed amplitudeLocalUpdate pauliPairEvolution
  apply Finset.sum_congr rfl
  intro a _
  change twoQubitPauliTransfer U (P i,P j) a *
    ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a,fun s => P s)) = _
  rw [pairSplitEquiv_symm_pauli]
  rfl

/-- Actual coherent gate updates commute on disjoint physical bonds. -/
theorem pauliSamplerFixed_commute (i j k l : Site) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (U V : TwoQubitUnitary) (ψ : PauliString Site → ℝ) :
    pauliSamplerFixed i j hij U (pauliSamplerFixed k l hkl V ψ) =
      pauliSamplerFixed k l hkl V (pauliSamplerFixed i j hij U ψ) := by
  simp_rw [pauliSamplerFixed_eq_pairEvolution]
  exact pauliPairEvolution_commute i j k l hik hil hjk hjl _ _ ψ

/-- Ordered physical gate-word action. Gate values are indexed by their
physical identities so reordering never resamples or changes a retained gate. -/
noncomputable def pauliWordEvolution {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word : List A) (ψ : PauliString Site → ℝ) : PauliString Site → ℝ :=
  word.foldl (fun v a => pauliSamplerFixed (bond a).1 (bond a).2 (hbond a) (gate a) v) ψ

/-- Any permutation of a matching layer has exactly the same coherent action,
pointwise in all gate values, before any Haar integration. -/
theorem pauliWordEvolution_perm {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word other : List A) (hp : word.Perm other)
    (hm : ∀ a ∈ word, ∀ b ∈ word, a ≠ b →
      (bond a).1 ≠ (bond b).1 ∧ (bond a).1 ≠ (bond b).2 ∧
      (bond a).2 ≠ (bond b).1 ∧ (bond a).2 ≠ (bond b).2)
    (ψ : PauliString Site → ℝ) :
    pauliWordEvolution bond hbond gate word ψ = pauliWordEvolution bond hbond gate other ψ := by
  apply hp.foldl_eq'
  intro a ha b hb v
  by_cases hab : a = b
  · subst b
    rfl
  · obtain ⟨h1,h2,h3,h4⟩ := hm a ha b hb hab
    exact (pauliSamplerFixed_commute (bond a).1 (bond a).2 (bond b).1 (bond b).2
      (hbond a) (hbond b) h1 h2 h3 h4 (gate a) (gate b) v).symm

/-- The manuscript's outside-first, retained-second implementation is exactly
valid on a physical matching layer, for every realization of both gate types. -/
theorem pauliWordEvolution_outside_first {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word : List A) (retained : A → Bool)
    (hm : ∀ a ∈ word, ∀ b ∈ word, a ≠ b →
      (bond a).1 ≠ (bond b).1 ∧ (bond a).1 ≠ (bond b).2 ∧
      (bond a).2 ≠ (bond b).1 ∧ (bond a).2 ≠ (bond b).2)
    (ψ : PauliString Site → ℝ) :
    pauliWordEvolution bond hbond gate word ψ =
      pauliWordEvolution bond hbond gate
        (word.filter (fun a => !retained a) ++ word.filter retained) ψ := by
  apply pauliWordEvolution_perm bond hbond gate word _ _ hm ψ
  simpa only [Bool.not_not] using (List.filter_append_perm (fun a => !retained a) word).symm

/-- The gate-word semantics is the same actual coefficient evolution used in
the quantum circuit and sampler covariance theorems. -/
theorem pauliWordEvolution_ofFn
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (ψ : PauliString Site → ℝ) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    pauliWordEvolution (fun a : ℕ × TwoQubitUnitary => bond a.1) (fun a => hbond a.1)
      (fun a => a.2) (List.ofFn (fun t : Fin n => (t.val,x t))) ψ =
      randomLinearEvolution (pauliCircuitTransfer bond) ψ n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last]
    simp only [pauliWordEvolution, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change pauliSamplerFixed (bond n).1 (bond n).2 (hbond n) (x (Fin.last n))
      (pauliWordEvolution _ _ _ (List.ofFn (fun t : Fin n => (t.val,x t.castSucc))) ψ) = _
    rw [ih]
    exact funext (pauliSamplerFixed_eq_mulVec _ _ _ _ _)

end Fluctuations
