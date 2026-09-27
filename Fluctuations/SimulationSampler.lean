import Fluctuations.PauliFrozenCircuit
import Fluctuations.PauliKernelMass

open MeasureTheory
open scoped BigOperators

namespace Fluctuations

set_option linter.unusedSectionVars false

/-- Squared Euclidean normalization of a real Pauli-amplitude vector. -/
def amplitudeNormalized {Q : Type*} [Fintype Q] (ψ : Q → ℝ) : Prop :=
  ∑ x, ψ x ^ 2 = 1

/-- A finite, normalized law on normalized coherent vectors. This is a semantic
law for the branching sampler; the algorithm stores only its sampled vector. -/
structure FiniteAmplitudeEnsemble (Q : Type*) [Fintype Q] where
  Index : Type
  finiteIndex : Fintype Index
  weight : Index → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1
  vector : Index → Q → ℝ
  normalized : ∀ x, amplitudeNormalized (vector x)

attribute [instance] FiniteAmplitudeEnsemble.finiteIndex

noncomputable def FiniteAmplitudeEnsemble.covariance {Q : Type*} [Fintype Q]
    (E : FiniteAmplitudeEnsemble Q) (i j : Q) : ℝ :=
  ∑ x, E.weight x * (E.vector x i * E.vector x j)

noncomputable def FiniteAmplitudeEnsemble.probability {Q : Type*} [Fintype Q]
    (E : FiniteAmplitudeEnsemble Q) (i : Q) : ℝ := E.covariance i i

theorem FiniteAmplitudeEnsemble.probability_nonneg {Q : Type*} [Fintype Q]
    (E : FiniteAmplitudeEnsemble Q) (i : Q) : 0 ≤ E.probability i := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (E.nonneg x) (mul_self_nonneg _)

theorem FiniteAmplitudeEnsemble.probability_total {Q : Type*} [Fintype Q]
    (E : FiniteAmplitudeEnsemble Q) : ∑ i, E.probability i = 1 := by
  unfold FiniteAmplitudeEnsemble.probability FiniteAmplitudeEnsemble.covariance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← pow_two]
  have hn (x : E.Index) : ∑ i, E.vector x i ^ 2 = 1 := E.normalized x
  simpa only [hn, mul_one] using E.total

noncomputable def amplitudePoint {Q : Type*} [Fintype Q]
    (ψ : Q → ℝ) (hψ : amplitudeNormalized ψ) : FiniteAmplitudeEnsemble Q where
  Index := Unit
  finiteIndex := inferInstance
  weight := fun _ => 1
  nonneg := by simp
  total := by simp
  vector := fun _ => ψ
  normalized := fun _ => hψ

@[simp] theorem amplitudePoint_covariance {Q : Type*} [Fintype Q]
    (ψ : Q → ℝ) (hψ : amplitudeNormalized ψ) (i j : Q) :
    (amplitudePoint ψ hψ).covariance i j = ψ i * ψ j := by
  simp [FiniteAmplitudeEnsemble.covariance, amplitudePoint]

section Local
variable {A S : Type*} [Fintype A] [Fintype S] [DecidableEq A] [DecidableEq S]

/-- The input-pair marginal used by the sampler. -/
noncomputable def amplitudeMarginal (ψ : A × S → ℝ) (a : A) : ℝ :=
  ∑ s, ψ (a, s) ^ 2

lemma amplitudeMarginal_nonneg (ψ : A × S → ℝ) (a : A) : 0 ≤ amplitudeMarginal ψ a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma amplitudeMarginal_total (ψ : A × S → ℝ) (hψ : amplitudeNormalized ψ) :
    ∑ a, amplitudeMarginal ψ a = 1 := by
  simpa [amplitudeNormalized, amplitudeMarginal, Fintype.sum_prod_type] using hψ

lemma amplitudeMarginal_zero (ψ : A × S → ℝ) (a : A)
    (h : amplitudeMarginal ψ a = 0) (s : S) : ψ (a,s) = 0 := by
  have hle : ψ (a,s)^2 ≤ amplitudeMarginal ψ a :=
    Finset.single_le_sum (fun x _ => sq_nonneg (ψ (a,x))) (Finset.mem_univ s)
  rw [h] at hle
  nlinarith [sq_nonneg (ψ (a,s))]

/-- Normalized conditional spectator vector. The zero-weight branch uses a
fixed basis vector so every stored trajectory remains normalized. -/
noncomputable def amplitudeConditional (s₀ : S) (ψ : A × S → ℝ) (a : A) (s : S) : ℝ :=
  if amplitudeMarginal ψ a = 0 then (if s = s₀ then 1 else 0)
  else ψ (a,s) / Real.sqrt (amplitudeMarginal ψ a)

theorem amplitudeConditional_normalized (s₀ : S) (ψ : A × S → ℝ) (a : A) :
    amplitudeNormalized (amplitudeConditional s₀ ψ a) := by
  classical
  unfold amplitudeNormalized amplitudeConditional
  by_cases hq : amplitudeMarginal ψ a = 0
  · simp [hq]
  · simp only [hq, ↓reduceIte, div_pow]
    rw [Real.sq_sqrt (amplitudeMarginal_nonneg ψ a), ← Finset.sum_div]
    exact div_self hq

/-- Exact cancellation holds even on zero-probability input branches. -/
theorem amplitudeConditional_covariance (s₀ : S) (ψ : A × S → ℝ)
    (a : A) (s t : S) :
    amplitudeMarginal ψ a *
      (amplitudeConditional s₀ ψ a s * amplitudeConditional s₀ ψ a t) =
      ψ (a,s) * ψ (a,t) := by
  by_cases hq : amplitudeMarginal ψ a = 0
  · simp [hq, amplitudeMarginal_zero ψ a hq]
  · have hs : Real.sqrt (amplitudeMarginal ψ a) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne (amplitudeMarginal_nonneg ψ a) (Ne.symm hq)))
    simp only [amplitudeConditional, hq, ↓reduceIte]
    field_simp
    rw [Real.sq_sqrt (amplitudeMarginal_nonneg ψ a)]
    ring

/-- Full vector represented after sampling input `a`, output `b`, and storing
`b` classically. Only the spectator amplitudes remain coherent. -/
noncomputable def amplitudeHaarBranch (s₀ : S) (ψ : A × S → ℝ)
    (ab : A × A) (p : A × S) : ℝ :=
  if p.1 = ab.2 then amplitudeConditional s₀ ψ ab.1 p.2 else 0

theorem amplitudeHaarBranch_normalized (s₀ : S) (ψ : A × S → ℝ) (ab : A × A) :
    amplitudeNormalized (amplitudeHaarBranch s₀ ψ ab) := by
  classical
  unfold amplitudeNormalized amplitudeHaarBranch
  rw [Fintype.sum_prod_type]
  simpa only [ite_pow, zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using
    amplitudeConditional_normalized s₀ ψ ab.1

noncomputable def amplitudeHaarWeight (K : Matrix A A ℝ) (ψ : A × S → ℝ)
    (ab : A × A) : ℝ := amplitudeMarginal ψ ab.1 * K ab.2 ab.1

theorem amplitudeHaarWeight_nonneg (K : Matrix A A ℝ) (hK : ∀ b a, 0 ≤ K b a)
    (ψ : A × S → ℝ) (ab : A × A) : 0 ≤ amplitudeHaarWeight K ψ ab :=
  mul_nonneg (amplitudeMarginal_nonneg ψ ab.1) (hK _ _)

theorem amplitudeHaarWeight_total (K : Matrix A A ℝ) (hK : ∀ a, ∑ b, K b a = 1)
    (ψ : A × S → ℝ) (hψ : amplitudeNormalized ψ) :
    ∑ ab, amplitudeHaarWeight K ψ ab = 1 := by
  simp only [amplitudeHaarWeight, Fintype.sum_prod_type, ← Finset.mul_sum, hK, mul_one]
  exact amplitudeMarginal_total ψ hψ

/-- The finite branch law preserves every spectator off-diagonal covariance. -/
theorem amplitudeHaarBranch_covariance (K : Matrix A A ℝ) (s₀ : S)
    (ψ : A × S → ℝ) (p q : A × S) :
    (∑ ab, amplitudeHaarWeight K ψ ab *
      (amplitudeHaarBranch s₀ ψ ab p * amplitudeHaarBranch s₀ ψ ab q)) =
      if p.1 = q.1 then ∑ a, K p.1 a * (ψ (a,p.2) * ψ (a,q.2)) else 0 := by
  classical
  simp only [Fintype.sum_prod_type, amplitudeHaarWeight, amplitudeHaarBranch]
  by_cases hpq : p.1 = q.1
  · simp only [← hpq, mul_ite, ite_mul, mul_zero, zero_mul ]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro a _
    rw [show amplitudeMarginal ψ a * K p.1 a *
        (amplitudeConditional s₀ ψ a p.2 * amplitudeConditional s₀ ψ a q.2) =
        K p.1 a * (amplitudeMarginal ψ a *
        (amplitudeConditional s₀ ψ a p.2 * amplitudeConditional s₀ ψ a q.2)) by ring,
      amplitudeConditional_covariance]
  · rw [if_neg hpq]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hp : p.1 = b
    · have hq : q.1 ≠ b := fun hq => hpq (hp.trans hq.symm)
      simp [hp, hq]
    · simp [hp]

/-- Coherent action of a retained local gate. -/
noncomputable def amplitudeLocalUpdate (T : Matrix A A ℝ) (ψ : A × S → ℝ)
    (p : A × S) : ℝ := ∑ a, T p.1 a * ψ (a,p.2)

theorem amplitudeLocalUpdate_covariance (T : Matrix A A ℝ) (ψ : A × S → ℝ)
    (p q : A × S) :
    amplitudeLocalUpdate T ψ p * amplitudeLocalUpdate T ψ q =
      ∑ a, ∑ b, (T p.1 a * T q.1 b) * (ψ (a,p.2) * ψ (b,q.2)) := by
  simp only [amplitudeLocalUpdate, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem amplitudeLocalUpdate_normalized (T : Matrix A A ℝ)
    (hT : ∀ a b, ∑ p, T p a * T p b = if a = b then 1 else 0)
    (ψ : A × S → ℝ) (hψ : amplitudeNormalized ψ) :
    amplitudeNormalized (amplitudeLocalUpdate T ψ) := by
  have hn (s : S) : (∑ p : A, amplitudeLocalUpdate T ψ (p,s) ^ 2) =
      ∑ a : A, ψ (a,s) ^ 2 := by
    simp_rw [pow_two, amplitudeLocalUpdate_covariance]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hT]
    simp
  unfold amplitudeNormalized
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hn]
  rw [Finset.sum_comm]
  exact amplitudeMarginal_total ψ hψ

end Local

section Ensembles
variable {Q : Type*} {B : Type} [Fintype Q] [Fintype B]

noncomputable def FiniteAmplitudeEnsemble.map (E : FiniteAmplitudeEnsemble Q)
    (f : (Q → ℝ) → Q → ℝ)
    (hf : ∀ ψ, amplitudeNormalized ψ → amplitudeNormalized (f ψ)) :
    FiniteAmplitudeEnsemble Q where
  Index := E.Index
  finiteIndex := E.finiteIndex
  weight := E.weight
  nonneg := E.nonneg
  total := E.total
  vector := fun x => f (E.vector x)
  normalized := fun x => hf _ (E.normalized x)

noncomputable def FiniteAmplitudeEnsemble.bind (E : FiniteAmplitudeEnsemble Q)
    (w : (Q → ℝ) → B → ℝ) (v : (Q → ℝ) → B → Q → ℝ)
    (hw : ∀ ψ b, 0 ≤ w ψ b)
    (ht : ∀ ψ, amplitudeNormalized ψ → ∑ b, w ψ b = 1)
    (hv : ∀ ψ b, amplitudeNormalized (v ψ b)) : FiniteAmplitudeEnsemble Q where
  Index := E.Index × B
  finiteIndex := inferInstance
  weight := fun x => E.weight x.1 * w (E.vector x.1) x.2
  nonneg := fun x => mul_nonneg (E.nonneg x.1) (hw _ _)
  total := by
    rw [Fintype.sum_prod_type]
    have htt (x : E.Index) := ht (E.vector x) (E.normalized x)
    simp only [← Finset.mul_sum, htt, mul_one]
    exact E.total
  vector := fun x => v (E.vector x.1) x.2
  normalized := fun x => hv _ _

theorem FiniteAmplitudeEnsemble.bind_covariance (E : FiniteAmplitudeEnsemble Q)
    (w : (Q → ℝ) → B → ℝ) (v : (Q → ℝ) → B → Q → ℝ)
    (hw : ∀ ψ b, 0 ≤ w ψ b)
    (ht : ∀ ψ, amplitudeNormalized ψ → ∑ b, w ψ b = 1)
    (hv : ∀ ψ b, amplitudeNormalized (v ψ b)) (i j : Q) :
    (E.bind w v hw ht hv).covariance i j =
      ∑ x, E.weight x * (∑ b, w (E.vector x) b * (v (E.vector x) b i * v (E.vector x) b j)) := by
  simp only [FiniteAmplitudeEnsemble.bind, FiniteAmplitudeEnsemble.covariance,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end Ensembles

section Reindex
variable {Q R : Type*} [Fintype Q] [Fintype R]

theorem amplitudeNormalized_reindex (e : Q ≃ R) (ψ : R → ℝ)
    (hψ : amplitudeNormalized ψ) : amplitudeNormalized (fun q => ψ (e q)) := by
  unfold amplitudeNormalized at *
  rw [Equiv.sum_comp e (fun r => ψ r ^ 2)]
  exact hψ

end Reindex

section Physical
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

noncomputable def pauliSamplerFixed (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (P : PauliString Site) : ℝ :=
  amplitudeLocalUpdate (twoQubitPauliTransfer U)
    (fun x => ψ ((pairSplitEquiv i j hij (Fin 4)).symm x))
    (pairSplitEquiv i j hij (Fin 4) P)

noncomputable def pauliSamplerBranch (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel)
    (P : PauliString Site) : ℝ :=
  amplitudeHaarBranch (fun _ => 0)
    (fun x => ψ ((pairSplitEquiv i j hij (Fin 4)).symm x)) ab
    (pairSplitEquiv i j hij (Fin 4) P)

noncomputable def pauliSamplerWeight (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel) : ℝ :=
  amplitudeHaarWeight localPauliHaarKernel
    (fun x => ψ ((pairSplitEquiv i j hij (Fin 4)).symm x)) ab

theorem pauliSamplerFixed_normalized (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeNormalized ψ) :
    amplitudeNormalized (pauliSamplerFixed i j hij U ψ) := by
  apply amplitudeNormalized_reindex
  apply amplitudeLocalUpdate_normalized
  · intro a b
    exact twoQubitPauliTransfer_column_inner a b U
  · exact amplitudeNormalized_reindex _ ψ hψ

theorem pauliSamplerBranch_normalized (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel) :
    amplitudeNormalized (pauliSamplerBranch i j hij ψ ab) :=
  amplitudeNormalized_reindex _ _ (amplitudeHaarBranch_normalized _ _ ab)

theorem pauliSamplerWeight_nonneg (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (ab : TwoQubitPauliLabel × TwoQubitPauliLabel) :
    0 ≤ pauliSamplerWeight i j hij ψ ab := by
  apply amplitudeHaarWeight_nonneg
  intro b a
  unfold localPauliHaarKernel
  split_ifs <;> norm_num

theorem pauliSamplerWeight_total (i j : Site) (hij : i ≠ j)
    (ψ : PauliString Site → ℝ) (hψ : amplitudeNormalized ψ) :
    ∑ ab, pauliSamplerWeight i j hij ψ ab = 1 := by
  apply amplitudeHaarWeight_total
  · intro a
    rcases a with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [localPauliHaarKernel, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · exact amplitudeNormalized_reindex _ ψ hψ

/-- The sampler applies the literal global Pauli transfer matrix coherently. -/
theorem pauliSamplerFixed_eq_mulVec (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary)
    (ψ : PauliString Site → ℝ) (P : PauliString Site) :
    pauliSamplerFixed i j hij U ψ P = Matrix.mulVec (pauliPairTransfer i j U) ψ P := by
  classical
  unfold pauliSamplerFixed amplitudeLocalUpdate Matrix.mulVec dotProduct
  conv_rhs => rw [← Equiv.sum_comp (pairSplitEquiv i j hij (Fin 4)).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have heq (x : PairSpectator i j → Fin 4) :
      (∀ s, s ≠ i → s ≠ j → P s =
        (pairSplitEquiv i j hij (Fin 4)).symm (a, x) s) ↔
          x = fun s : PairSpectator i j => P s := by
    constructor
    · intro h
      funext s
      simpa [pairSplitEquiv, s.prop.1, s.prop.2] using (h s s.prop.1 s.prop.2).symm
    · rintro rfl s hsi hsj
      simp [pairSplitEquiv, hsi, hsj]
  simp only [pauliPairTransfer, heq, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, pairSplitEquiv_symm_pauli,
    pauliPairUpdate_left i j hij, pauliPairUpdate_right, Prod.mk.eta]
  change twoQubitPauliTransfer U (P i,P j) a *
    ψ ((pairSplitEquiv i j hij (Fin 4)).symm (a, fun s => P s)) = _
  rw [pairSplitEquiv_symm_pauli]

end Physical
end Fluctuations
