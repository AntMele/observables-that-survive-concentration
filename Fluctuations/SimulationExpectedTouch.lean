import Fluctuations.SimulationTailReflection
import Fluctuations.SimulationLocalInfluence
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Fluctuations
noncomputable section

/-- Extracting any injective family of coordinates from an independent
product leaves precisely the corresponding independent product law. -/
theorem simulationExtract_measurePreserving {G : Type*} [MeasurableSpace G]
    (ν : Measure G) [IsProbabilityMeasure ν] {m n : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e) :
    MeasurePreserving (fun x : Fin n → G => fun i => x (e i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ : Fin m => ν)) := by
  have hi : iIndepFun (fun i : Fin n => fun x : Fin n → G => x i)
      (Measure.pi (fun _ => ν)) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hs := hi.precomp he
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin m => (measurable_pi_apply (e i)).aemeasurable)).mp hs
  refine ⟨by fun_prop, ?_⟩
  simpa only [(measurePreserving_eval (fun _ : Fin n => ν) _).map_eq] using hm

theorem simulationExtract_integral {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : (Fin m → TwoQubitUnitary) → ℝ) (hf : Continuous f) :
    (∫ x : Fin n → TwoQubitUnitary, f (fun i => x (e i))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ∫ x : Fin m → TwoQubitUnitary, f x ∂Measure.pi (fun _ => globalHaar TwoQubitBasis) := by
  have hp := simulationExtract_measurePreserving (globalHaar TwoQubitBasis) e he
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm

/-- Coordinate extraction followed by inversion also preserves the actual
product Haar law. This is the law needed for the backwards quantum word. -/
theorem simulationExtract_inv_integral {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (f : (Fin m → TwoQubitUnitary) → ℝ) (hf : Continuous f) :
    (∫ x : Fin n → TwoQubitUnitary, f (fun i => (x (e i))⁻¹)
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      ∫ x : Fin m → TwoQubitUnitary, f x ∂Measure.pi (fun _ => globalHaar TwoQubitBasis) := by
  have hi := measurePreserving_pi (fun _ : Fin m => globalHaar TwoQubitBasis)
    (fun _ : Fin m => globalHaar TwoQubitBasis)
    (fun _ => Measure.measurePreserving_inv (globalHaar TwoQubitBasis))
  have hp := hi.comp (simulationExtract_measurePreserving (globalHaar TwoQubitBasis) e he)
  rw [← hp.map_eq]
  exact (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm

section Active
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma simulationActiveMass_eq (i j : Site) (ψ : PauliString Site → ℝ) :
    pauliGateActiveMass i j ψ = simulationTouching i j (fun P => ψ P ^ 2) := by
  unfold pauliGateActiveMass amplitudeMass pauliGateActiveVector simulationTouching
  apply Finset.sum_congr rfl
  intro P _
  simp only [Prod.mk.injEq]
  split_ifs <;> ring

lemma simulationActiveMass_continuous (i j : Site) :
    Continuous (pauliGateActiveMass i j : (PauliString Site → ℝ) → ℝ) := by
  change Continuous (fun ψ => pauliGateActiveMass i j ψ)
  simp only [simulationActiveMass_eq, simulationTouching]
  fun_prop

/-- The exact expected active Pauli mass is the touching probability in
the derived finite Haar Markov law, rather than an assumed coupling. -/
theorem simulationActiveMass_haar (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (i j : Site) (m : ℕ) :
    (∫ x : Fin m → TwoQubitUnitary,
      pauliGateActiveMass i j
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) m x)
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationTouching i j (markovWeightEvolution (pauliCircuitHaarKernel bond)
        (pauliInitialVector P₀) m) := by
  have hc := randomLinearEvolution_continuous (pauliCircuitTransfer bond)
    (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) m
  simp only [simulationActiveMass_eq, simulationTouching]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro P _
    rw [integral_mul_const]
    simp_rw [pow_two]
    rw [integral_randomLinearEvolution_mul (globalHaar TwoQubitBasis)
        (pauliCircuitTransfer bond) (pauliCircuitTransfer_continuous bond),
      pauliCircuit_haar_covariance]
    simp
  · intro P _
    exact (Continuous.mul (Continuous.pow (continuous_apply P |>.comp hc) 2)
      continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Expected active mass from an arbitrary injective extraction of gates in
a larger physical circuit. Unused gate coordinates are integrated out. -/
theorem simulationActiveMass_extracted (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (i j : Site) {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) :
    (∫ x : Fin n → TwoQubitUnitary,
      pauliGateActiveMass i j
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) m
          (fun a => x (e a)))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationTouching i j (markovWeightEvolution (pauliCircuitHaarKernel bond)
        (pauliInitialVector P₀) m) := by
  have hc := (simulationActiveMass_continuous i j).comp
    (randomLinearEvolution_continuous _ (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) m)
  exact (simulationExtract_integral e he _ hc).trans (simulationActiveMass_haar bond P₀ i j m)

theorem simulationActiveMass_extracted_inv (bond : ℕ → Site × Site) (P₀ : PauliString Site)
    (i j : Site) {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) :
    (∫ x : Fin n → TwoQubitUnitary,
      pauliGateActiveMass i j
        (randomLinearEvolution (pauliCircuitTransfer bond) (pauliInitialVector P₀) m
          (fun a => (x (e a))⁻¹))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationTouching i j (markovWeightEvolution (pauliCircuitHaarKernel bond)
        (pauliInitialVector P₀) m) := by
  have hc := (simulationActiveMass_continuous i j).comp
    (randomLinearEvolution_continuous _ (pauliCircuitTransfer_continuous bond) (pauliInitialVector P₀) m)
  exact (simulationExtract_inv_integral e he _ hc).trans (simulationActiveMass_haar bond P₀ i j m)

end Active


/-- The actual first `m` gate coordinates of the full brickwork circuit. -/
theorem simulationExpected_prefix (c T m : ℕ) (hm : m ≤ T*(2*c+1))
    (i j : BrickworkSite c) :
    (∫ x : Fin (T*(2*c+1)) → TwoQubitUnitary,
      pauliGateActiveMass i j
        (randomLinearEvolution (pauliCircuitTransfer (brickworkCircuitBond c T))
          (pauliInitialVector (brickworkInitialZ c)) m (fun a => x (Fin.castLE hm a)))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationTouching i j (pauliLayerEvolution ((brickworkGateSchedule c T).take m)
        (pauliInitialVector (brickworkInitialZ c))) := by
  rw [simulationActiveMass_extracted _ _ _ _ _ (Fin.castLE_injective hm),
    simulationChronologicalPrefix c T m hm]

/-- Extract the strictly later physical gates in reverse chronological order. -/
def simulationReverseSuffixEmbedding (n t : ℕ) (ht : t < n) : Fin (n-t-1) → Fin n :=
  fun k => ⟨n-1-k.val, by have := k.isLt; omega⟩

theorem simulationReverseSuffixEmbedding_injective (n t : ℕ) (ht : t < n) :
    Function.Injective (simulationReverseSuffixEmbedding n t ht) := by
  intro a b hab
  have h := congrArg Fin.val hab
  change n-1-a.val = n-1-b.val at h
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

lemma simulationList_reverseSuffix {A : Type*} (bs : List A) (default : A) (t : ℕ) :
    List.ofFn (fun k : Fin (bs.length-t) => bs.getD (bs.length-1-k.val) default) =
      (bs.drop t).reverse := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_ofFn, List.getElem_reverse, List.getElem_drop]
    rw [List.getD_eq_getElem]
    · congr 1
      simp only [List.length_drop]
      simp only [List.length_ofFn] at hk
      omega
    · simp only [List.length_ofFn] at hk
      omega

/-- Literal backwards Markov recurrence equals the reversed future list. -/
theorem simulationReverseChronologicalSuffix (c T t : ℕ)
    (w : PauliString (BrickworkSite c) → ℝ) :
    markovWeightEvolution
      (pauliCircuitHaarKernel (fun k => brickworkCircuitBond c T (T*(2*c+1)-1-k)))
      w (T*(2*c+1)-t-1) =
      pauliLayerEvolution ((brickworkGateSchedule c T).drop (t+1)).reverse w := by
  rw [← pauliLayerEvolution_ofFn _ (fun k => brickworkCircuitBond_distinct c T _)]
  unfold brickworkCircuitBond
  have h := simulationList_reverseSuffix (brickworkGateSchedule c T) (brickworkOddBond 0) (t+1)
  simp only [brickworkGateSchedule_length, Nat.sub_add_eq] at h
  simp only [Fin.coe_cast] at h
  rw [h]

/-- The genuine backwards amplitudes use inverse gates, but their expected
active mass is exactly the reversed-suffix Pauli touching law. -/
theorem simulationExpected_suffix (c T t : ℕ) (ht : t < T*(2*c+1))
    (i j : BrickworkSite c) :
    (∫ x : Fin (T*(2*c+1)) → TwoQubitUnitary,
      pauliGateActiveMass i j
        (randomLinearEvolution
          (pauliCircuitTransfer (fun k => brickworkCircuitBond c T (T*(2*c+1)-1-k)))
          (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2)))) (T*(2*c+1)-t-1)
          (fun a => (x (simulationReverseSuffixEmbedding (T*(2*c+1)) t ht a))⁻¹))
      ∂Measure.pi (fun _ => globalHaar TwoQubitBasis)) =
      simulationTouching i j (pauliLayerEvolution ((brickworkGateSchedule c T).drop (t+1)).reverse
        (pauliInitialVector (pauliSiteZ (Fin.last c,(1 : Fin 2))))) := by
  rw [simulationActiveMass_extracted_inv _ _ _ _ _
    (simulationReverseSuffixEmbedding_injective _ _ ht), simulationReverseChronologicalSuffix]

end
end Fluctuations
