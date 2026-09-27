import Fluctuations.PauliEndpointObservable

open MeasureTheory
open scoped BigOperators

namespace Fluctuations

set_option maxHeartbeats 800000

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The full local Haar covariance, including unequal global input strings.
Untouched coordinates retain their exact spectator constraints. -/
theorem pauliPairTransfer_haar_mixed (i j : Site) (P S Q R : PauliString Site) :
    gateSecondMoment (globalHaar TwoQubitBasis) (pauliPairTransfer i j) (Q, R) (P, S) =
      if (∀ s, s ≠ i → s ≠ j → Q s = P s) ∧
          (∀ s, s ≠ i → s ≠ j → R s = S s) ∧
          (P i, P j) = (S i, S j) ∧ (Q i, Q j) = (R i, R j)
      then localPauliHaarKernel (Q i, Q j) (P i, P j) else 0 := by
  classical
  by_cases hQ : ∀ s, s ≠ i → s ≠ j → Q s = P s
  · by_cases hR : ∀ s, s ≠ i → s ≠ j → R s = S s
    · simp only [gateSecondMoment, pauliPairTransfer, if_pos hQ, if_pos hR]
      rw [twoQubitPauliTransfer_haar_covariance]
      by_cases hlocal : (P i, P j) = (S i, S j) ∧ (Q i, Q j) = (R i, R j)
      · rw [if_pos hlocal, if_pos ⟨hQ, hR, hlocal.1, hlocal.2⟩]
      · rw [if_neg hlocal, if_neg (fun h => hlocal h.2.2)]
    · simp [gateSecondMoment, pauliPairTransfer, hR]
  · simp [gateSecondMoment, pauliPairTransfer, hQ]

lemma pauliPairMoment_support (i j : Site) (P S Q R : PauliString Site)
    (h : gateSecondMoment (globalHaar TwoQubitBasis) (pauliPairTransfer i j)
      (Q, R) (P, S) ≠ 0) :
    (∀ s, s ≠ i → s ≠ j → Q s = P s) ∧
      (∀ s, s ≠ i → s ≠ j → R s = S s) ∧
      (P i, P j) = (S i, S j) ∧ (Q i, Q j) = (R i, R j) := by
  rw [pauliPairTransfer_haar_mixed] at h
  split_ifs at h with hs
  · exact hs
  · exact (h rfl).elim

/-- A diagonal output receives no contribution from off-diagonal inputs,
even when the preceding covariance matrix itself is not diagonal. -/
theorem pauliPairTransfer_haar_row_covariance (i j : Site) (P S Q : PauliString Site) :
    gateSecondMoment (globalHaar TwoQubitBasis) (pauliPairTransfer i j) (Q, Q) (P, S) =
      if P = S then pauliPairKernel i j Q P else 0 := by
  classical
  by_cases h : P = S
  · subst S
    simpa using pauliPairTransfer_haar_column_covariance i j P Q Q
  · rw [if_neg h]
    by_contra hn
    rcases pauliPairMoment_support i j P S Q Q hn with ⟨hP, hS, hpair, _⟩
    apply h
    funext s
    by_cases hi : s = i
    · subst s
      exact congrArg Prod.fst hpair
    by_cases hj : s = j
    · subst s
      exact congrArg Prod.snd hpair
    exact (hP s hi hj).symm.trans (hS s hi hj)

/-- The inhomogeneous classical weights induced by one fixed actual gate.
Only that gate uses its squared real Pauli transfer coefficients. -/
noncomputable def pauliCircuitFixedKernel (bond : ℕ → Site × Site)
    (t : ℕ) (g : TwoQubitUnitary) (u : ℕ) :
    Matrix (PauliString Site) (PauliString Site) ℝ :=
  if u = t then fun Q P => (pauliCircuitTransfer bond u g Q P) ^ 2
  else pauliCircuitHaarKernel bond u

lemma pauliFrozenCovariance_before (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (t : ℕ) (g : TwoQubitUnitary) (n : ℕ) (hn : n ≤ t)
    (P Q : PauliString Site) :
    fullSecondMomentEvolution (globalHaar TwoQubitBasis)
      (freezeGateKernel (pauliCircuitTransfer bond) t g) (pauliInitialVector P₀) n P Q =
    fullSecondMomentEvolution (globalHaar TwoQubitBasis)
      (pauliCircuitTransfer bond) (pauliInitialVector P₀) n P Q := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    have hnt : n ≠ t := by omega
    have hK : freezeGateKernel (pauliCircuitTransfer bond) t g n =
        pauliCircuitTransfer bond n := by funext U; simp [freezeGateKernel, hnt]
    simp only [fullSecondMomentEvolution, hK]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    rw [ih (by omega)]

/-- The diagonal evolves by the fixed-gate squared-transfer kernel at every
time. Off-diagonal entries are retained separately until a covering Haar tail. -/
theorem pauliFrozenCovariance_diagonal (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (t : ℕ) (g : TwoQubitUnitary) (n : ℕ)
    (P : PauliString Site) :
    fullSecondMomentEvolution (globalHaar TwoQubitBasis)
      (freezeGateKernel (pauliCircuitTransfer bond) t g) (pauliInitialVector P₀) n P P =
      markovWeightEvolution (pauliCircuitFixedKernel bond t g) (pauliInitialVector P₀) n P := by
  classical
  induction n generalizing P with
  | zero => simpa [fullSecondMomentEvolution, markovWeightEvolution] using
      pauliInitialVector_covariance P₀ P P
  | succ n ih =>
    rw [fullSecondMomentEvolution]
    by_cases hnt : n = t
    · have hdiag (A B : PauliString Site) :
          fullSecondMomentEvolution (globalHaar TwoQubitBasis)
            (freezeGateKernel (pauliCircuitTransfer bond) t g) (pauliInitialVector P₀) n A B =
          if A = B then markovWeightEvolution (pauliCircuitFixedKernel bond t g)
            (pauliInitialVector P₀) n A else 0 := by
        by_cases hAB : A = B
        · subst B
          simp [ih]
        · rw [pauliFrozenCovariance_before bond P₀ t g n (by omega),
            pauliCircuit_haar_covariance]
          simp [hAB]
      simp_rw [hdiag, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hK : freezeGateKernel (pauliCircuitTransfer bond) t g n =
          fun _ => pauliCircuitTransfer bond n g := by funext U; simp [freezeGateKernel, hnt]
      simp only [hK, markovWeightEvolution, pauliCircuitFixedKernel, if_pos hnt,
        Matrix.mulVec, dotProduct, pow_two]
      apply Finset.sum_congr rfl
      intro A _
      congr 1
      simp [gateSecondMoment]
    · have hK : freezeGateKernel (pauliCircuitTransfer bond) t g n =
          pauliCircuitTransfer bond n := by funext U; simp [freezeGateKernel, hnt]
      rw [hK]
      change (∑ A, ∑ B, gateSecondMoment (globalHaar TwoQubitBasis)
        (pauliPairTransfer (bond n).1 (bond n).2) (P, P) (A, B) * _) = _
      simp_rw [pauliPairTransfer_haar_row_covariance, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp_rw [ih]
      simp only [markovWeightEvolution, pauliCircuitFixedKernel, if_neg hnt,
        pauliCircuitHaarKernel, Matrix.mulVec, dotProduct]

/-- Once a Haar gate after the fixed coordinate touches a site, all later
covariances with unequal labels at that site vanish. -/
theorem pauliFrozenCovariance_site_zero (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (t : ℕ) (g : TwoQubitUnitary) (n : ℕ)
    (s : Site) (hs : ∃ u, t < u ∧ u < n ∧ (s = (bond u).1 ∨ s = (bond u).2))
    (Q R : PauliString Site) (hQR : Q s ≠ R s) :
    fullSecondMomentEvolution (globalHaar TwoQubitBasis)
      (freezeGateKernel (pauliCircuitTransfer bond) t g) (pauliInitialVector P₀) n Q R = 0 := by
  classical
  induction n generalizing Q R with
  | zero => obtain ⟨u, _, hu, _⟩ := hs; omega
  | succ n ih =>
    obtain ⟨u, htu, hun, htouch⟩ := hs
    have hnt : n ≠ t := by omega
    have hK : freezeGateKernel (pauliCircuitTransfer bond) t g n =
        pauliCircuitTransfer bond n := by funext U; simp [freezeGateKernel, hnt]
    simp only [fullSecondMomentEvolution, hK]
    apply Finset.sum_eq_zero
    intro P _
    apply Finset.sum_eq_zero
    intro S _
    by_cases hm : gateSecondMoment (globalHaar TwoQubitBasis)
        (pauliPairTransfer (bond n).1 (bond n).2) (Q, R) (P, S) = 0
    · exact mul_eq_zero_of_left hm _
    have hsup := pauliPairMoment_support (bond n).1 (bond n).2 P S Q R hm
    by_cases hi : s = (bond n).1
    · exact (hQR (hi ▸ congrArg Prod.fst hsup.2.2.2)).elim
    by_cases hj : s = (bond n).2
    · exact (hQR (hj ▸ congrArg Prod.snd hsup.2.2.2)).elim
    have hun' : u < n := by
      have hne : u ≠ n := by
        rintro rfl
        exact htouch.elim hi hj
      omega
    have hPS : P s ≠ S s := by
      intro h
      exact hQR ((hsup.1 s hi hj).trans (h.trans (hsup.2.1 s hi hj).symm))
    rw [ih ⟨u, htu, hun', htouch⟩ P S hPS, mul_zero]

/-- A later collection of Haar gates covering every physical site removes
all cross terms, with no shock-family or covariance assumption. -/
theorem pauliFrozenCovariance_eq_diagonal (bond : ℕ → Site × Site)
    (P₀ : PauliString Site) (t : ℕ) (g : TwoQubitUnitary) (n : ℕ)
    (hcover : ∀ s, ∃ u, t < u ∧ u < n ∧ (s = (bond u).1 ∨ s = (bond u).2))
    (P Q : PauliString Site) :
    fullSecondMomentEvolution (globalHaar TwoQubitBasis)
      (freezeGateKernel (pauliCircuitTransfer bond) t g) (pauliInitialVector P₀) n P Q =
      if P = Q then markovWeightEvolution (pauliCircuitFixedKernel bond t g)
        (pauliInitialVector P₀) n P else 0 := by
  classical
  by_cases hPQ : P = Q
  · subst Q
    simpa using pauliFrozenCovariance_diagonal bond P₀ t g n P
  · rw [if_neg hPQ]
    have hne : ¬ ∀ s, P s = Q s := fun h => hPQ (funext h)
    obtain ⟨s, hs⟩ := not_forall.mp hne
    exact pauliFrozenCovariance_site_zero bond P₀ t g n s (hcover s) P Q hs

/-- The actual conditional OTOC is the inhomogeneous Pauli-weight evolution
when Haar gates after the fixed gate cover all sites. -/
theorem pauliCircuit_fixed_gate_otoc_markov
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ M : QubitOperator Site) (n : ℕ)
    (t : Fin n) (g : TwoQubitUnitary)
    (hcover : ∀ s, ∃ u, t.val < u ∧ u < n ∧ (s = (bond u).1 ∨ s = (bond u).2)) :
    coordinateAverage (fun _ : Fin n => globalHaar TwoQubitBasis) t
      (fun x => globalOTOC ρ (pauliStringMatrix P₀) M 1
        (pauliCircuitUnitary bond hbond n x)) g =
      ∑ P : PauliString Site, pauliOTOCWeight ρ M P P *
        (markovWeightEvolution (pauliCircuitFixedKernel bond t.val g)
          (pauliInitialVector P₀) n P : ℂ) := by
  classical
  rw [pauliCircuit_fixed_gate_otoc]
  simp_rw [pauliFrozenCovariance_eq_diagonal bond P₀ t.val g n hcover]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The fixed-gate endpoint OTOC is state-independent for every trace-one
input matrix, after the proven covering Haar tail. -/
theorem pauliCircuit_fixed_gate_endpoint_otoc
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ : QubitOperator Site) (hρ : Matrix.trace ρ = 1)
    (j : Site) (n : ℕ) (t : Fin n) (g : TwoQubitUnitary)
    (hcover : ∀ s, ∃ u, t.val < u ∧ u < n ∧ (s = (bond u).1 ∨ s = (bond u).2)) :
    coordinateAverage (fun _ : Fin n => globalHaar TwoQubitBasis) t
      (fun x => globalOTOC ρ (pauliStringMatrix P₀) (pauliStringMatrix (pauliSiteZ j)) 1
        (pauliCircuitUnitary bond hbond n x)) g =
      ∑ P : PauliString Site, (pauliEndpointSign (P j) : ℂ) *
        (markovWeightEvolution (pauliCircuitFixedKernel bond t.val g)
          (pauliInitialVector P₀) n P : ℂ) := by
  rw [pauliCircuit_fixed_gate_otoc_markov bond hbond P₀ ρ _ n t g hcover]
  simp_rw [pauliOTOCWeight_siteZ_diagonal ρ hρ]

/-- The fixed global squared-transfer action is precisely the sixteen-input
local update used by the classical endpoint calculation. -/
theorem pauliPairSquaredTransfer_mul (i j : Site) (hij : i ≠ j)
    (g : TwoQubitUnitary) (w : PauliString Site → ℝ) (Q : PauliString Site) :
    (∑ P, (pauliPairTransfer i j g Q P) ^ 2 * w P) =
      ∑ r : TwoQubitPauliLabel, (twoQubitPauliTransfer g (Q i, Q j) r) ^ 2 *
        w (pauliPairUpdate i j Q r) := by
  classical
  rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  have heq (x : PairSpectator i j → Fin 4) :
      (∀ s, s ≠ i → s ≠ j → Q s =
        (pairSplitEquiv i j hij (Fin 4)).symm (r, x) s) ↔
          x = fun s : PairSpectator i j => Q s := by
    constructor
    · intro h
      funext s
      simpa [pairSplitEquiv, s.prop.1, s.prop.2] using (h s s.prop.1 s.prop.2).symm
    · rintro rfl s hsi hsj
      simp [pairSplitEquiv, hsi, hsj]
  simp only [pauliPairTransfer, heq, ite_pow, zero_pow (by decide : 2 ≠ 0),
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, pairSplitEquiv_symm_pauli,
    pauliPairUpdate_left i j hij, pauliPairUpdate_right, Prod.mk.eta]

/-- Continuity of the actual OTOC on the finite physical gate product. -/
theorem pauliCircuit_otoc_continuous
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (P₀ : PauliString Site) (ρ M : QubitOperator Site) (n : ℕ) :
    Continuous (fun x : Fin n → TwoQubitUnitary =>
      globalOTOC ρ (pauliStringMatrix P₀) M 1 (pauliCircuitUnitary bond hbond n x)) := by
  simp_rw [pauliCircuit_otoc_quadratic]
  have hc := randomLinearEvolution_continuous (pauliCircuitTransfer bond)
    (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) n
  unfold quadraticCoefficientObservable
  fun_prop

end Fluctuations
