import Fluctuations.PauliLocalHaar
import Fluctuations.EndpointMarkov

/-! Exact product-form Pauli shock distributions and their local evolution. -/

open scoped BigOperators

namespace Fluctuations

noncomputable section

def pauliIdentityWeight (p : Fin 4) : ℝ := if p = 0 then 1 else 0
def pauliNonzeroWeight (p : Fin 4) : ℝ := if p = 0 then 0 else 1/3
def pauliUniformWeight (_p : Fin 4) : ℝ := 1/4

lemma pauliHaar_identity_product (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      (pauliIdentityWeight p.1 * pauliIdentityWeight p.2)) =
      pauliIdentityWeight q.1 * pauliIdentityWeight q.2 := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight]

lemma pauliHaar_uniform_product (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      (pauliUniformWeight p.1 * pauliUniformWeight p.2)) =
      pauliUniformWeight q.1 * pauliUniformWeight q.2 := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliUniformWeight]

lemma pauliHaar_front_left (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      (pauliNonzeroWeight p.1 * pauliIdentityWeight p.2)) =
      (1/5 : ℝ) * (pauliNonzeroWeight q.1 * pauliIdentityWeight q.2) +
      (4/5 : ℝ) * (pauliUniformWeight q.1 * pauliNonzeroWeight q.2) := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight, pauliNonzeroWeight, pauliUniformWeight]

lemma pauliHaar_front_right (q : TwoQubitPauliLabel) :
    (∑ p : TwoQubitPauliLabel, localPauliHaarKernel q p *
      (pauliUniformWeight p.1 * pauliNonzeroWeight p.2)) =
      (1/5 : ℝ) * (pauliNonzeroWeight q.1 * pauliIdentityWeight q.2) +
      (4/5 : ℝ) * (pauliUniformWeight q.1 * pauliNonzeroWeight q.2) := by
  rcases q with ⟨q₁,q₂⟩
  fin_cases q₁ <;> fin_cases q₂ <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, localPauliHaarKernel,
      pauliIdentityWeight, pauliNonzeroWeight, pauliUniformWeight]

section ProductWeights

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- Product distribution with one one-qubit weight at each site. -/
def pauliProductWeight (w : Site → Fin 4 → ℝ) (P : Site → Fin 4) : ℝ :=
  ∏ s, w s (P s)

def pauliPairReplace (i j : Site) (P : Site → Fin 4) (p : TwoQubitPauliLabel) : Site → Fin 4 :=
  Function.update (Function.update P i p.1) j p.2

/-- Apply a two-site stochastic kernel, summing its sixteen possible inputs. -/
def pauliPairEvolution (i j : Site) (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (w : (Site → Fin 4) → ℝ) (Q : Site → Fin 4) : ℝ :=
  ∑ p, K (Q i,Q j) p * w (pauliPairReplace i j Q p)

lemma pauliProductWeight_split (w : Site → Fin 4 → ℝ) (i j : Site) (hij : i ≠ j)
    (P : Site → Fin 4) :
    pauliProductWeight w P = w i (P i) * w j (P j) *
      ∏ s ∈ (Finset.univ.erase i).erase j, w s (P s) := by
  unfold pauliProductWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])]
  ring

lemma pauliPairEvolution_product (w : Site → Fin 4 → ℝ) (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ) (Q : Site → Fin 4) :
    pauliPairEvolution i j K (pauliProductWeight w) Q =
      (∑ p, K (Q i,Q j) p * (w i p.1 * w j p.2)) *
      ∏ s ∈ (Finset.univ.erase i).erase j, w s (Q s) := by
  have he (p : TwoQubitPauliLabel) :
      pauliProductWeight w (pauliPairReplace i j Q p) =
      w i p.1 * w j p.2 * ∏ s ∈ (Finset.univ.erase i).erase j, w s (Q s) := by
    rw [pauliProductWeight_split w i j hij]
    simp only [pauliPairReplace, Function.update_self, Function.update_of_ne hij]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    have hsi : s ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
    have hsj : s ≠ j := (Finset.mem_erase.mp hs).1
    simp [Function.update_of_ne hsi, Function.update_of_ne hsj]
  simp only [pauliPairEvolution, he, ← mul_assoc, ← Finset.sum_mul]

lemma pauliPairEvolution_product_fixed (w : Site → Fin 4 → ℝ) (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ)
    (hl : ∀ q : TwoQubitPauliLabel,
      (∑ p, K q p * (w i p.1 * w j p.2)) = w i q.1 * w j q.2)
    (Q : Site → Fin 4) :
    pauliPairEvolution i j K (pauliProductWeight w) Q = pauliProductWeight w Q := by
  rw [pauliPairEvolution_product w i j hij, hl, pauliProductWeight_split w i j hij]

lemma pauliPairEvolution_product_mix (w w₁ w₂ : Site → Fin 4 → ℝ)
    (i j : Site) (hij : i ≠ j)
    (K : TwoQubitPauliLabel → TwoQubitPauliLabel → ℝ) (a b : ℝ)
    (hout₁ : ∀ s, s ≠ i → s ≠ j → w₁ s = w s)
    (hout₂ : ∀ s, s ≠ i → s ≠ j → w₂ s = w s)
    (hl : ∀ q : TwoQubitPauliLabel,
      (∑ p, K q p * (w i p.1 * w j p.2)) =
        a * (w₁ i q.1 * w₁ j q.2) + b * (w₂ i q.1 * w₂ j q.2))
    (Q : Site → Fin 4) :
    pauliPairEvolution i j K (pauliProductWeight w) Q =
      a * pauliProductWeight w₁ Q + b * pauliProductWeight w₂ Q := by
  have ho (w' : Site → Fin 4 → ℝ)
      (h : ∀ s, s ≠ i → s ≠ j → w' s = w s) :
      (∏ s ∈ (Finset.univ.erase i).erase j, w' s (Q s)) =
      ∏ s ∈ (Finset.univ.erase i).erase j, w s (Q s) := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [h s ((Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1)
      (Finset.mem_erase.mp hs).1]
  rw [pauliPairEvolution_product w i j hij, hl,
    pauliProductWeight_split w₁ i j hij, pauliProductWeight_split w₂ i j hij,
    ho w₁ hout₁, ho w₂ hout₂]
  ring

/-- A Pauli string with uniform sites behind its rightmost nonidentity site. -/
def pauliShockMarginal (rank : Site → ℕ) (x : ℕ) (s : Site) : Fin 4 → ℝ :=
  if rank s < x then pauliUniformWeight
  else if rank s = x then pauliNonzeroWeight else pauliIdentityWeight

def pauliShock (rank : Site → ℕ) (x : ℕ) : (Site → Fin 4) → ℝ :=
  pauliProductWeight (pauliShockMarginal rank x)

omit [Fintype Site] [DecidableEq Site] in
lemma pauliShockMarginal_adjacent_away (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (s : Site) (hsi : s ≠ i) (hsj : s ≠ j) :
    pauliShockMarginal rank (rank i) s = pauliShockMarginal rank (rank j) s := by
  have hi : rank s ≠ rank i := fun h => hsi (hrank h)
  have hj : rank s ≠ rank j := fun h => hsj (hrank h)
  by_cases hs : rank s < rank i
  · simp [pauliShockMarginal, hs, show rank s < rank j by omega]
  · simp [pauliShockMarginal, hs, hi, hj, show ¬rank s < rank j by omega]

/-- Exact one-bond evolution of the full Pauli shock distribution. This
includes every Pauli string, so it proves more than an endpoint-mass rule. -/
theorem pauliShock_haar_pair (rank : Site → ℕ) (hrank : Function.Injective rank)
    (i j : Site) (hadj : rank j = rank i + 1) (x : ℕ) (Q : Site → Fin 4) :
    pauliPairEvolution i j localPauliHaarKernel (pauliShock rank x) Q =
      if x = rank i ∨ x = rank j then
        (1/5 : ℝ) * pauliShock rank (rank i) Q +
        (4/5 : ℝ) * pauliShock rank (rank j) Q
      else pauliShock rank x Q := by
  have hij : i ≠ j := by intro h; subst j; omega
  have hlt : rank i < rank j := by omega
  have hne : rank i ≠ rank j := Nat.ne_of_lt hlt
  by_cases hi : x = rank i
  · subst x
    rw [if_pos (Or.inl rfl)]
    apply pauliPairEvolution_product_mix _ _ _ i j hij
    · intro s _ _; rfl
    · intro s hsi hsj
      exact (pauliShockMarginal_adjacent_away rank hrank i j hadj s hsi hsj).symm
    · intro q
      simpa [pauliShockMarginal, hlt, hne, hne.symm, not_lt_of_ge hlt.le] using
        pauliHaar_front_left q
  · by_cases hj : x = rank j
    · subst x
      rw [if_pos (Or.inr rfl)]
      apply pauliPairEvolution_product_mix _ _ _ i j hij
      · intro s hsi hsj
        exact pauliShockMarginal_adjacent_away rank hrank i j hadj s hsi hsj
      · intro s _ _; rfl
      · intro q
        simpa [pauliShockMarginal, hlt, hne, hne.symm, not_lt_of_ge hlt.le] using
          pauliHaar_front_right q
    · rw [if_neg (not_or.mpr ⟨hi,hj⟩)]
      apply pauliPairEvolution_product_fixed _ i j hij
      intro q
      by_cases hx : x < rank i
      · simpa [pauliShockMarginal, show ¬rank i < x by omega,
          show ¬rank j < x by omega, Ne.symm hi, Ne.symm hj] using pauliHaar_identity_product q
      · simpa [pauliShockMarginal, show rank i < x by omega,
          show rank j < x by omega] using pauliHaar_uniform_product q

end ProductWeights

end

end Fluctuations
