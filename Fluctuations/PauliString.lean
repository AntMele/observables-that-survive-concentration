import Fluctuations.PauliLocalHaar
import Fluctuations.PatchEmbedding

open scoped BigOperators Matrix Kronecker

namespace Fluctuations

abbrev PauliString (Site : Type*) := Site → Fin 4

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

abbrev PairSpectator (i j : Site) := {s : Site // s ≠ i ∧ s ≠ j}

/-- The canonical ordered pair of coordinates and all untouched coordinates. -/
def pairSplitEquiv (i j : Site) (hij : i ≠ j) (A : Type*) :
    (Site → A) ≃ (A × A) × (PairSpectator i j → A) where
  toFun x := ((x i, x j), fun s => x s)
  invFun p s := if hsi : s = i then p.1.1 else if hsj : s = j then p.1.2 else p.2 ⟨s, hsi, hsj⟩
  left_inv x := by
    funext s
    by_cases hsi : s = i
    · subst s
      simp
    by_cases hsj : s = j
    · subst s
      simp [hsi]
    · simp [hsi, hsj]
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, x⟩
    apply Prod.ext
    · simp [hij.symm]
    · funext s
      simp [s.prop.1, s.prop.2]

def pauliPairUpdate (i j : Site) (P : PauliString Site) (q : TwoQubitPauliLabel) :
    PauliString Site := Function.update (Function.update P i q.1) j q.2

omit [Fintype Site] in
@[simp] lemma pauliPairUpdate_left (i j : Site) (hij : i ≠ j)
    (P : PauliString Site) (q : TwoQubitPauliLabel) : pauliPairUpdate i j P q i = q.1 := by
  simp [pauliPairUpdate, hij]

omit [Fintype Site] in
@[simp] lemma pauliPairUpdate_right (i j : Site)
    (P : PauliString Site) (q : TwoQubitPauliLabel) : pauliPairUpdate i j P q j = q.2 := by
  simp [pauliPairUpdate]

omit [Fintype Site] in
lemma pauliPairUpdate_other (i j s : Site) (hsi : s ≠ i) (hsj : s ≠ j)
    (P : PauliString Site) (q : TwoQubitPauliLabel) : pauliPairUpdate i j P q s = P s := by
  simp [pauliPairUpdate, hsi, hsj]

omit [Fintype Site] in
lemma pairSplitEquiv_symm_pauli (i j : Site) (hij : i ≠ j)
    (P : PauliString Site) (q : TwoQubitPauliLabel) :
    (pairSplitEquiv i j hij (Fin 4)).symm (q, fun s => P s) = pauliPairUpdate i j P q := by
  funext s
  by_cases hsi : s = i
  · subst s
    simp [pairSplitEquiv, pauliPairUpdate, hij]
  by_cases hsj : s = j
  · subst s
    simp [pairSplitEquiv, pauliPairUpdate, hsi]
  · simp [pairSplitEquiv, pauliPairUpdate, hsi, hsj]

/-- The actual global tensor Pauli matrix in the computational basis. -/
def pauliStringMatrix (P : PauliString Site) : QubitOperator Site :=
  tensorMatrix (fun s => pauliMatrix (P s))

noncomputable def pauliPairKernel (i j : Site) (Q P : PauliString Site) : ℝ :=
  if (∀ s, s ≠ i → s ≠ j → Q s = P s) then
    localPauliHaarKernel (Q i, Q j) (P i, P j) else 0

noncomputable def pauliPairTransfer (i j : Site) (U : TwoQubitUnitary)
    (Q P : PauliString Site) : ℝ :=
  if (∀ s, s ≠ i → s ≠ j → Q s = P s) then
    twoQubitPauliTransfer U (Q i, Q j) (P i, P j) else 0

/-- Full matrix action equals the explicit sixteen-input local update. -/
theorem pauliPairKernel_mul (i j : Site) (hij : i ≠ j)
    (w : PauliString Site → ℝ) (Q : PauliString Site) :
    (∑ P, pauliPairKernel i j Q P * w P) =
      ∑ r : TwoQubitPauliLabel, localPauliHaarKernel (Q i, Q j) r *
        w (pauliPairUpdate i j Q r) := by
  classical
  rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have heq (x : PairSpectator i j → Fin 4) :
      (∀ s, s ≠ i → s ≠ j → Q s =
        (pairSplitEquiv i j hij (Fin 4)).symm (r, x) s) ↔ x = fun s : PairSpectator i j => Q s := by
    constructor
    · intro h
      funext s
      simpa [pairSplitEquiv, s.prop.1, s.prop.2] using (h s s.prop.1 s.prop.2).symm
    · rintro rfl s hsi hsj
      simp [pairSplitEquiv, hsi, hsj]
  simp only [pauliPairKernel, heq, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, pairSplitEquiv_symm_pauli,
    pauliPairUpdate_left i j hij, pauliPairUpdate_right, Prod.mk.eta]

end Fluctuations
