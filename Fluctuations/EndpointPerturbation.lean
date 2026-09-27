import Fluctuations.EndpointLumpability

/-! Endpoint perturbations propagate through untouched matching bonds. -/

open scoped BigOperators
namespace Fluctuations
noncomputable section
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- A Haar gate preserves the difference between two endpoint profiles when
the profiles agree at the gate's two endpoints. -/
lemma pauliEndpointMass_pair_difference (rank : Site → ℕ)
    (hrank : Function.Injective rank) (i j : Site) (hadj : rank j = rank i + 1)
    (w v : (Site → Fin 4) → ℝ)
    (hi : pauliEndpointMass rank w (rank i) = pauliEndpointMass rank v (rank i))
    (hj : pauliEndpointMass rank w (rank j) = pauliEndpointMass rank v (rank j)) (s : Site) :
    pauliEndpointMass rank (pauliPairEvolution i j localPauliHaarKernel w) (rank s) -
      pauliEndpointMass rank (pauliPairEvolution i j localPauliHaarKernel v) (rank s) =
    pauliEndpointMass rank w (rank s) - pauliEndpointMass rank v (rank s) := by
  rw [pauliEndpointMass_haar_pair rank hrank i j hadj,
    pauliEndpointMass_haar_pair rank hrank i j hadj]
  split_ifs with hsi hsj
  · rw [hsi, hi, hj]
    ring
  · rw [hsj, hi, hj]
    ring
  · rfl

/-- A whole list of Haar gates preserves an endpoint perturbation supported
outside the endpoints of every gate in that list. The full Pauli laws may be
arbitrary and correlated. -/
theorem pauliEndpointMass_layer_difference (rank : Site → ℕ)
    (hrank : Function.Injective rank) (bs : List (Site × Site))
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (w v : (Site → Fin 4) → ℝ)
    (he : ∀ p ∈ bs,
      pauliEndpointMass rank w (rank p.1) = pauliEndpointMass rank v (rank p.1) ∧
      pauliEndpointMass rank w (rank p.2) = pauliEndpointMass rank v (rank p.2)) (s : Site) :
    pauliEndpointMass rank (pauliLayerEvolution bs w) (rank s) -
      pauliEndpointMass rank (pauliLayerEvolution bs v) (rank s) =
    pauliEndpointMass rank w (rank s) - pauliEndpointMass rank v (rank s) := by
  induction bs generalizing w v with
  | nil => rfl
  | cons p bs ih =>
    rcases p with ⟨i,j⟩
    have hpair := pauliEndpointMass_pair_difference rank hrank i j
      (hadj (i,j) (by simp)) w v (he (i,j) (by simp)).1 (he (i,j) (by simp)).2
    change pauliEndpointMass rank (pauliLayerEvolution bs
      (pauliPairEvolution i j localPauliHaarKernel w)) (rank s) -
      pauliEndpointMass rank (pauliLayerEvolution bs
        (pauliPairEvolution i j localPauliHaarKernel v)) (rank s) = _
    rw [ih (fun p hp => hadj p (by simp [hp])) _ _ (by
      intro p hp
      have hp' := he p (by simp [hp])
      constructor
      · apply sub_eq_zero.mp
        rw [hpair, hp'.1, sub_self]
      · apply sub_eq_zero.mp
        rw [hpair, hp'.2, sub_self])]
    exact hpair s

/-- In particular, other disjoint gates of a matching leave a two-site endpoint
perturbation unchanged. -/
theorem pauliEndpointMass_layer_twoSite_difference (rank : Site → ℕ)
    (hrank : Function.Injective rank) (bs : List (Site × Site))
    (hadj : ∀ p ∈ bs, rank p.2 = rank p.1 + 1)
    (i j : Site) (η : ℝ) (w v : (Site → Fin 4) → ℝ)
    (hdelta : ∀ s, pauliEndpointMass rank w (rank s) - pauliEndpointMass rank v (rank s) =
      η * ((if s = j then 1 else 0) - (if s = i then 1 else 0)))
    (hmiss : ∀ p ∈ bs, p.1 ≠ i ∧ p.1 ≠ j ∧ p.2 ≠ i ∧ p.2 ≠ j) (s : Site) :
    pauliEndpointMass rank (pauliLayerEvolution bs w) (rank s) -
      pauliEndpointMass rank (pauliLayerEvolution bs v) (rank s) =
      η * ((if s = j then 1 else 0) - (if s = i then 1 else 0)) := by
  rw [pauliEndpointMass_layer_difference rank hrank bs hadj w v (by
    intro p hp
    have hm := hmiss p hp
    constructor
    · apply sub_eq_zero.mp
      simp [hdelta, hm.1, hm.2.1]
    · apply sub_eq_zero.mp
      simp [hdelta, hm.2.2.1, hm.2.2.2])]
  exact hdelta s

end
end Fluctuations
