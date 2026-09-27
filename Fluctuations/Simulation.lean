import Fluctuations.SimulationAccuracy
import Fluctuations.SimulationEyeError
import Fluctuations.SimulationAsymptotics
import Fluctuations.SimulationPhysicalLaw
import Fluctuations.SimulationCompressedOperations

/-! The paper's classical simulation theorem for the infinite-temperature
endpoint OTOC. The circuit has `n = 6*(s+1)` qubits, `d = 5*n/3` layers,
and independent Haar U(4) gates. All approximation and support bounds are
proved for this circuit, rather than supplied as hypotheses.

The cost model counts scalar arithmetic (real or complex) and exact finite-distribution sampling;
it does not assert a finite-precision or bit-complexity bound. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Fluctuations
noncomputable section

/-- The literal normalized quantum trace `2⁻ⁿ Tr[(U† Z₁ U Zₙ)²]` at the
critical depth, with the actual chronological embedded-gate unitary. -/
def simulationCriticalOTOC (s : ℕ)
    (x : Fin (5*(s+1)*(2*(3*s+2)+1)) → TwoQubitUnitary) : ℂ :=
  globalOTOC (globalMaximallyMixedState (QubitState (BrickworkSite (3*s+2))))
    (pauliStringMatrix (brickworkInitialZ (3*s+2)))
    (pauliStringMatrix (pauliSiteZ (Fin.last (3*s+2),(1:Fin 2)))) 1
    (pauliCircuitUnitary (brickworkCircuitBond (3*s+2) (5*(s+1)))
      (brickworkCircuitBond_distinct (3*s+2) (5*(s+1)))
      (5*(s+1)*(2*(3*s+2)+1)) x)

/-- Arithmetic work of the exact generated outside-first call schedule and
the prescribed number of independent samples. -/
def simulationCriticalWork (s : ℕ) (ε δ : ℝ) : ℕ :=
  let n := 6*(s+1)
  let R := simulationRadius n ε δ
  simulationEstimatorWork (simulationSampleCount ε δ) n
    (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
    (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1)))

/-- Accuracy on the canonical mixed-circuit kernel. The physical
outside-first implementation is identified with this law separately. -/
theorem simulationCritical_mixed_accuracy (s : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ ≤ ((Measure.pi (fun _ : Fin (5*(s+1)*(2*(3*s+2)+1)) =>
        globalHaar TwoQubitBasis)) ⊗ₘ
      mixedPauliSamplerKernel (brickworkCircuitBond (3*s+2) (5*(s+1)))
        (brickworkCircuitBond_distinct (3*s+2) (5*(s+1)))
        (simulationRetainedSchedule (3*s+2) (5*(s+1)) (simulationRadius (6*(s+1)) ε δ))
        (brickworkInitialZ (3*s+2)) (5*(s+1)*(2*(3*s+2)+1))
        (simulationSampleCount ε δ)).real
      {z | ‖(simulationEstimator (Fin.last (3*s+2),(1:Fin 2))
        (simulationSampleCount ε δ) z.2 : ℂ) - simulationCriticalOTOC s z.1‖ ≤ ε} := by
  have hn : 0 < 6*(s+1) := by omega
  have hR : 0 ≤ simulationRadius (6*(s+1)) ε δ :=
    (show (0:ℝ) ≤ 1 by norm_num).trans (simulationRadius_ge_one hn hε hε1 hδ hδ1)
  have hb := simulationEye_bias (3*s+2) (5*(s+1))
    (simulationRadius (6*(s+1)) ε δ) hR (by push_cast; ring)
  have hsize : (2:ℝ)*((3*s+2:ℕ)+1) = (6*(s+1):ℕ) := by push_cast; ring
  rw [hsize] at hb
  have h := simulationSampler_joint_success_parameters
    (brickworkCircuitBond (3*s+2) (5*(s+1)))
    (brickworkCircuitBond_distinct (3*s+2) (5*(s+1)))
    (brickworkInitialZ (3*s+2)) (Fin.last (3*s+2),(1:Fin 2))
    (5*(s+1)*(2*(3*s+2)+1)) (6*(s+1)) hn
    (simulationRetainedSchedule (3*s+2) (5*(s+1)) (simulationRadius (6*(s+1)) ε δ))
    ε δ hε hε1 hδ hδ1 hb
  convert h using 3
  ext z
  rw [simulationCriticalOTOC, ← simulationCircuitOTOC_eq_trace]
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Explicit work bound for arbitrary requested error and failure probability. -/
theorem otoc1_simulation_work (s : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    simulationCriticalWork s ε δ ≤
      180002*(simulationSampleCount ε δ+1)*(6*(s+1))^2*
        4^(2*simulationWidthBudget (6*(s+1)) (simulationRadius (6*(s+1)) ε δ)+4) := by
  exact simulationCritical_estimatorWork s (simulationSampleCount ε δ)
    ((show (0:ℝ) ≤ 1 by norm_num).trans
      (simulationRadius_ge_one (by omega) hε hε1 hδ hδ1))

/-- Joint success probability over the actual Haar input circuit and the
costed outside-first algorithm's independent samples. The target is the
literal complex normalized quantum trace; the estimate is real. -/
def simulationCriticalSuccessProbability (s : ℕ) (ε δ : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin (5*(s+1)*(2*(3*s+2)+1)) =>
      globalHaar TwoQubitBasis)) ⊗ₘ
    simulationPhysicalSamplerKernel (3*s+2) (5*(s+1))
      (simulationRadius (6*(s+1)) ε δ) (brickworkInitialZ (3*s+2))
      (simulationSampleCount ε δ)).real
    {z | ‖(simulationEstimator (Fin.last (3*s+2),(1:Fin 2))
      (simulationSampleCount ε δ) z.2 : ℂ) - simulationCriticalOTOC s z.1‖ ≤ ε}

/-- The actual physical algorithm attains the requested accuracy with the
requested joint success probability, without an assumed error bound. -/
theorem otoc1_simulation_accuracy (s : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ ≤ simulationCriticalSuccessProbability s ε δ := by
  unfold simulationCriticalSuccessProbability
  rw [simulationPhysicalSamplerKernel_eq]
  exact simulationCritical_mixed_accuracy s ε δ hε hε1 hδ hδ1

/-- The manuscript's classical simulation theorem: the same physical sampler
has joint success probability at least `1-δ` and the displayed explicit
arithmetic-work bound. Its subexponential specialization is proved below.
There is no mean-change, local-variance, tail, bias, or width hypothesis. -/
theorem otoc1_subexponential_simulation (s : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1-δ ≤ simulationCriticalSuccessProbability s ε δ ∧
    simulationCriticalWork s ε δ ≤
      180002*(simulationSampleCount ε δ+1)*(6*(s+1))^2*
        4^(2*simulationWidthBudget (6*(s+1)) (simulationRadius (6*(s+1)) ε δ)+4) :=
  ⟨otoc1_simulation_accuracy s ε δ hε hε1 hδ hδ1,
    otoc1_simulation_work s ε δ hε hε1 hδ hδ1⟩

lemma simulationCritical_inversePower_range (s a : ℕ) (ha : 0 < a) :
    0 < 1/((6*(s+1):ℕ):ℝ)^a ∧ 1/((6*(s+1):ℕ):ℝ)^a < 1 := by
  have hn : (1:ℝ) < (6*(s+1):ℕ) := by exact_mod_cast (show 1 < 6*(s+1) by omega)
  have hp : (1:ℝ) < ((6*(s+1):ℕ):ℝ)^a := one_lt_pow₀ hn (by omega)
  exact ⟨by positivity, (div_lt_one (by positivity)).mpr hp⟩

/-- Full inverse-polynomial statement for the same algorithm: for any fixed
positive natural exponents, every circuit size has the stated joint accuracy,
and the logarithm of its arithmetic work divided by the qubit count tends to
zero. In particular, the cost is subexponential rather than just bounded by
an informally described asymptotic expression. -/
theorem otoc1_subexponential_simulation_inversePolynomial
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∀ s : ℕ, 1-1/((6*(s+1):ℕ):ℝ)^b ≤
      simulationCriticalSuccessProbability s
        (1/((6*(s+1):ℕ):ℝ)^a) (1/((6*(s+1):ℕ):ℝ)^b)) ∧
    Tendsto (fun s : ℕ =>
      Real.log (simulationCriticalWork s
        (1/((6*(s+1):ℕ):ℝ)^a) (1/((6*(s+1):ℕ):ℝ)^b)) /
        (6*(s+1):ℕ)) atTop (𝓝 0) := by
  refine ⟨?_, simulationCriticalPolynomialWork_subexponential a b⟩
  intro s
  obtain ⟨hε,hε1⟩ := simulationCritical_inversePower_range s a ha
  obtain ⟨hδ,hδ1⟩ := simulationCritical_inversePower_range s b hb
  exact otoc1_simulation_accuracy s _ _ hε hε1 hδ hδ1

end
end Fluctuations
