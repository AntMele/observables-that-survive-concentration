import Fluctuations.PauliBrickwork

/-! Actual Pauli kernel updates on disjoint site pairs commute. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section
variable {Site : Type*} [DecidableEq Site]

lemma pauliPairReplace_apply_away (i j s : Site) (hsi : s ≠ i) (hsj : s ≠ j)
    (P : Site → Fin 4) (p : TwoQubitPauliLabel) :
    pauliPairReplace i j P p s = P s := by
  simp [pauliPairReplace, Function.update_of_ne hsi, Function.update_of_ne hsj]

lemma pauliPairReplace_commute (i j k l : Site)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (P : Site → Fin 4) (p q : TwoQubitPauliLabel) :
    pauliPairReplace i j (pauliPairReplace k l P q) p =
      pauliPairReplace k l (pauliPairReplace i j P p) q := by
  funext s
  by_cases hi : s = i <;> by_cases hj : s = j <;>
    by_cases hk : s = k <;> by_cases hl : s = l <;>
      simp_all [pauliPairReplace, Function.update_apply]

/-- Disjoint two-site kernels commute as operators on the full Pauli-string law.
Neither kernel is required to be Haar or stochastic. -/
theorem pauliPairEvolution_commute (i j k l : Site)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (K L : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (w : (Site → Fin 4) → ℝ) :
    pauliPairEvolution i j K (pauliPairEvolution k l L w) =
      pauliPairEvolution k l L (pauliPairEvolution i j K w) := by
  funext P
  simp only [pauliPairEvolution, Finset.mul_sum,
    pauliPairReplace_apply_away i j k hik.symm hjk.symm,
    pauliPairReplace_apply_away i j l hil.symm hjl.symm,
    pauliPairReplace_apply_away k l i hik hil,
    pauliPairReplace_apply_away k l j hjk hjl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  rw [pauliPairReplace_commute i j k l hik hil hjk hjl]
  ring

/-- A fixed pair kernel can be moved past any list of disjoint Haar gates. -/
theorem pauliPairEvolution_commute_layer (i j : Site)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (bs : List (Site × Site))
    (hmiss : ∀ p ∈ bs, i ≠ p.1 ∧ i ≠ p.2 ∧ j ≠ p.1 ∧ j ≠ p.2)
    (w : (Site → Fin 4) → ℝ) :
    pauliPairEvolution i j K (pauliLayerEvolution bs w) =
      pauliLayerEvolution bs (pauliPairEvolution i j K w) := by
  induction bs generalizing w with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨k,l⟩
    have hm := hmiss (k,l) (by simp)
    simp only [pauliLayerEvolution]
    rw [ih (fun p hp => hmiss p (by simp [hp])),
      pauliPairEvolution_commute i j k l hm.1 hm.2.1 hm.2.2.1 hm.2.2.2]

/-- Reordering a selected fixed gate to the start of its matching layer is
valid for the actual full Pauli distribution, before endpoint projection. -/
theorem pauliFixedPair_first (i j : Site)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (before after : List (Site × Site))
    (hmiss : ∀ p ∈ before, i ≠ p.1 ∧ i ≠ p.2 ∧ j ≠ p.1 ∧ j ≠ p.2)
    (w : (Site → Fin 4) → ℝ) :
    pauliLayerEvolution after (pauliPairEvolution i j K (pauliLayerEvolution before w)) =
      pauliLayerEvolution (before ++ after) (pauliPairEvolution i j K w) := by
  rw [pauliPairEvolution_commute_layer i j K before hmiss, pauliLayerEvolution_append]

end
end Fluctuations
