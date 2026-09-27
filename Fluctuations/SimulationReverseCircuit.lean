import Fluctuations.SimulationSamplerReorder
import Fluctuations.SimulationTrace

open scoped BigOperators Matrix
namespace Fluctuations
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- Normalized-trace OTOC duality under reversing and inverting the circuit. -/
theorem globalOTOC_infiniteTemperature_reverse {N : Type*} [Fintype N] [DecidableEq N]
    (B M : Matrix N N ℂ) (U : GlobalUnitary N) :
    globalOTOC (globalMaximallyMixedState N) B M 1 U =
      globalOTOC (globalMaximallyMixedState N) M B 1 U⁻¹ := by
  change Matrix.trace ((Fintype.card N : ℂ)⁻¹ • (1 : Matrix N N ℂ) *
    ((globalHaarConjugate B U * M) ^ (2*1))) =
    Matrix.trace ((Fintype.card N : ℂ)⁻¹ • (1 : Matrix N N ℂ) *
    ((globalHaarConjugate M U⁻¹ * B) ^ (2*1)))
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Nat.mul_one, pow_two]
  congr 1
  have hc : globalHaarConjugate (globalHaarConjugate B U) U⁻¹ = B := by
    change (U⁻¹).val.conjTranspose * globalHaarConjugate B U * (U⁻¹).val = B
    rw [← globalHaarConjugate_mul_right, mul_inv_cancel]
    simp [globalHaarConjugate]
  rw [← globalHaarConjugate_trace
    ((globalHaarConjugate B U * M) * (globalHaarConjugate B U * M)) U⁻¹]
  simp only [← globalHaarConjugate_mul, hc]
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle B (globalHaarConjugate M U⁻¹ * B) (globalHaarConjugate M U⁻¹)

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

lemma pauliPairUnitary_inv (i j : Site) (hij : i ≠ j) (U : TwoQubitUnitary) :
    pauliPairUnitary i j hij U⁻¹ = (pauliPairUnitary i j hij U)⁻¹ := by
  apply Subtype.ext
  rw [← unitary.star_eq_inv, ← unitary.star_eq_inv, unitary.coe_star]
  change pauliPairEmbedding i j hij (star U).val = star (pauliPairEmbedding i j hij U.val)
  rw [unitary.coe_star, map_star]

/-- Actual global chronological unitary product of a physical gate word. -/
def pauliWordUnitary {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word : List A) : GlobalUnitary (QubitState Site) :=
  (word.map (fun a => pauliPairUnitary (bond a).1 (bond a).2 (hbond a) (gate a))).prod

theorem pauliWordUnitary_reverse {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word : List A) :
    pauliWordUnitary bond hbond (fun a => (gate a)⁻¹) word.reverse =
      (pauliWordUnitary bond hbond gate word)⁻¹ := by
  unfold pauliWordUnitary
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
  simp_rw [pauliPairUnitary_inv]
  rfl

theorem pauliWordUnitary_ofFn
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    pauliWordUnitary (fun a : ℕ × TwoQubitUnitary => bond a.1) (fun a => hbond a.1)
      (fun a => a.2) (List.ofFn (fun t : Fin n => (t.val,x t))) =
      pauliCircuitUnitary bond hbond n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last]
    simp only [pauliWordUnitary, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    change pauliWordUnitary _ _ _ (List.ofFn (fun t : Fin n => (t.val,x t.castSucc))) * _ = _
    rw [ih]
    rfl

/-- The exact trace duality applied to a literal reversed physical word. -/
theorem pauliWord_otoc_reverse {A : Type*} (bond : A → Site × Site)
    (hbond : ∀ a, (bond a).1 ≠ (bond a).2) (gate : A → TwoQubitUnitary)
    (word : List A) (B M : QubitOperator Site) :
    globalOTOC (globalMaximallyMixedState (QubitState Site)) B M 1
      (pauliWordUnitary bond hbond gate word) =
    globalOTOC (globalMaximallyMixedState (QubitState Site)) M B 1
      (pauliWordUnitary bond hbond (fun a => (gate a)⁻¹) word.reverse) := by
  rw [pauliWordUnitary_reverse, globalOTOC_infiniteTemperature_reverse]

lemma simulation_reverse_ofFn {A : Type*} {n : ℕ} (f : Fin n → A) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev, List.length_ofFn]
  omega

lemma pauliCircuitUnitary_eq_prod
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    pauliCircuitUnitary bond hbond n x =
      (List.ofFn (fun t : Fin n => pauliPairUnitary (bond t.val).1 (bond t.val).2
        (hbond t.val) (x t))).prod := by
  simpa only [pauliWordUnitary, List.map_ofFn, Function.comp_def] using
    (pauliWordUnitary_ofFn bond hbond n x).symm

/-- The actual reversed bond schedule. Values outside the processed finite word
are irrelevant but remain well-formed physical bonds. -/
def reverseCircuitBond (bond : ℕ → Site × Site) (n : ℕ) (t : ℕ) : Site × Site :=
  bond (n-(t+1))

def reverseGateRealization {n : ℕ} (x : Fin n → TwoQubitUnitary) : Fin n → TwoQubitUnitary :=
  fun t => (x t.rev)⁻¹

/-- Exact identification of the reversed, inverted finite gate word with the
inverse of the literal chronological circuit unitary. -/
theorem pauliCircuitUnitary_reverse
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    pauliCircuitUnitary (reverseCircuitBond bond n) (fun t => hbond (n-(t+1))) n
      (reverseGateRealization x) = (pauliCircuitUnitary bond hbond n x)⁻¹ := by
  rw [pauliCircuitUnitary_eq_prod, pauliCircuitUnitary_eq_prod, List.prod_inv_reverse,
    List.map_ofFn, simulation_reverse_ofFn]
  congr 2
  funext t
  simp only [Function.comp_def, reverseCircuitBond, reverseGateRealization, Fin.val_rev,
    pauliPairUnitary_inv]

/-- Trace duality in precisely the finite-coordinate form used for the
backward-cone influence bound. -/
theorem pauliCircuit_otoc_reverse
    (bond : ℕ → Site × Site) (hbond : ∀ t, (bond t).1 ≠ (bond t).2)
    (B M : QubitOperator Site) (n : ℕ) (x : Fin n → TwoQubitUnitary) :
    globalOTOC (globalMaximallyMixedState (QubitState Site)) B M 1
      (pauliCircuitUnitary bond hbond n x) =
    globalOTOC (globalMaximallyMixedState (QubitState Site)) M B 1
      (pauliCircuitUnitary (reverseCircuitBond bond n) (fun t => hbond (n-(t+1))) n
        (reverseGateRealization x)) := by
  rw [pauliCircuitUnitary_reverse, globalOTOC_infiniteTemperature_reverse]

end Fluctuations
