import Fluctuations.SimulationWidth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! An explicit arithmetic-operation model for the dense coherent Pauli-vector
sampler. Addition, multiplication, division and square root each cost one;
indexing and reading stored coefficients are not arithmetic operations. Drawing
from an explicitly computed finite probability vector is a unit-cost primitive. This is the arithmetic model of the manuscript,
not a bit-complexity or finite-precision claim. No exponentially large mixed
state is ever counted or constructed: the data array has `4^m` real entries.
-/
open scoped BigOperators
namespace Fluctuations

/-- Arithmetic cost of a straightforward `r × s` by `s × u` product:
`r*u*s` multiplications and `r*u*(s-1)` additions. -/
def denseMatrixProductWork (r s u : ℕ) : ℕ := r*u*s+r*u*(s-1)

/-- One application of the local 16-by-16 Pauli transfer matrix to each
spectator column. This counts the actual multiply-and-sum loops. -/
def pauliFixedVectorWork (spectators : ℕ) : ℕ :=
  ∑ _b : Fin 16, (∑ _α : Fin spectators, ((∑ _a : Fin 16, (1:ℕ))+(16-1)))

theorem pauliFixedVectorWork_eq (spectators : ℕ) :
    pauliFixedVectorWork spectators = 31*(16*spectators) := by
  simp [pauliFixedVectorWork]
  ring

/-- Compute all 16 marginals by squaring/accumulating each entry; normalize the
chosen spectator slice with one square root and one division per entry; make
the two finite draws. Real Pauli coefficients suffice for Hermitian input. -/
def pauliAveragedVectorWork (spectators : ℕ) : ℕ :=
  (∑ _a : Fin 16, ∑ _α : Fin spectators, 2)+1+spectators+2

theorem pauliAveragedVectorWork_eq (spectators : ℕ) :
    pauliAveragedVectorWork spectators = 33*spectators+3 := by
  simp [pauliAveragedVectorWork]
  omega

/-- Precomputing all 256 transfer coefficients using three ordinary 4-by-4
matrix products, a trace, and division by four. Complex operations count one
arithmetic operation; conjugation and input reads add a fixed 512 operations. -/
def pauliTransferConstructionWork : ℕ :=
  256*(3*denseMatrixProductWork 4 4 4+3+1)+512

theorem pauliTransferConstructionWork_eq : pauliTransferConstructionWork = 87552 := by decide

/-- The two kinds of actual local sampler call and its coherent-site count,
after the two gate sites have been adjoined. -/
inductive SimulationLocalCall where
  | fixed (coherent : ℕ)
  | averaged (coherent : ℕ)
  deriving DecidableEq

def SimulationLocalCall.coherent : SimulationLocalCall → ℕ
  | .fixed m => m
  | .averaged m => m

def SimulationLocalCall.work : SimulationLocalCall → ℕ
  | .fixed m => pauliTransferConstructionWork+pauliFixedVectorWork (4^(m-2))
  | .averaged m => pauliAveragedVectorWork (4^(m-2))

/-- The dense coherent vector has exactly four Pauli choices per site. -/
theorem simulationDenseVector_entries (m : ℕ) :
    Fintype.card (Fin m → Fin 4) = 4^m := by simp

theorem simulationLocalCall_work_le (call : SimulationLocalCall) {K : ℕ}
    (hsize : call.coherent ≤ K) : call.work ≤ 90000*4^K := by
  have hpow : 4^(call.coherent-2) ≤ 4^K :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 1 ≤ 4^K := Nat.one_le_pow _ _ (by decide)
  cases call with
  | fixed m =>
    simp only [SimulationLocalCall.work,SimulationLocalCall.coherent,
      pauliFixedVectorWork_eq,pauliTransferConstructionWork_eq] at *
    nlinarith
  | averaged m =>
    simp only [SimulationLocalCall.work,SimulationLocalCall.coherent,
      pauliAveragedVectorWork_eq] at *
    nlinarith

/-- Sum of the local arithmetic loops, final squaring/finite draw, and output
assembly of the `n` classical labels. -/
def simulationSampleWork (n finalCoherent : ℕ) (calls : List SimulationLocalCall) : ℕ :=
  (calls.map SimulationLocalCall.work).sum+4^finalCoherent+1+n

theorem simulationSampleWork_le (n finalCoherent K : ℕ)
    (calls : List SimulationLocalCall) (hc : ∀ call ∈ calls, call.coherent ≤ K)
    (hf : finalCoherent ≤ K) :
    simulationSampleWork n finalCoherent calls ≤
      90000*(calls.length+n+1)*4^K := by
  have hs : (calls.map SimulationLocalCall.work).sum ≤ calls.length*(90000*4^K) := by
    induction calls with
    | nil => simp
    | cons call calls ih =>
      have hcall := simulationLocalCall_work_le call (hc call (by simp))
      have hi := ih (fun x hx => hc x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hp : 4^finalCoherent ≤ 4^K := Nat.pow_le_pow_right (by decide) hf
  have hpos : 1 ≤ 4^K := Nat.one_le_pow _ _ (by decide)
  unfold simulationSampleWork
  nlinarith

/-- In a nontrivial critical circuit there are at least as many gates as sites,
so the arithmetic cost is a constant times gates times `4^(2W+4)`. -/
theorem simulationSampleWork_gate_bound (n finalCoherent W : ℕ)
    (calls : List SimulationLocalCall) (hc : ∀ call ∈ calls, call.coherent ≤ 2*W+4)
    (hf : finalCoherent ≤ 2*W+4) (hn : n ≤ calls.length) :
    simulationSampleWork n finalCoherent calls ≤
      180000*(calls.length+1)*4^(2*W+4) := by
  have h := simulationSampleWork_le n finalCoherent (2*W+4) calls hc hf
  nlinarith

/-- Exact count of the physical brickwork gates when `n=6(s+1)` and
`d=10(s+1)=5n/3`. -/
theorem simulationCritical_gate_count (s : ℕ) :
    (brickworkGateSchedule (3*s+2) (5*(s+1))).length = 5*(s+1)*(6*s+5) := by
  rw [brickworkGateSchedule_length]
  congr 1
  omega

theorem simulationCritical_gate_bounds (s : ℕ) :
    6*(s+1) ≤ (brickworkGateSchedule (3*s+2) (5*(s+1))).length ∧
    ((brickworkGateSchedule (3*s+2) (5*(s+1))).length : ℝ) ≤
      5*(6*(s+1):ℝ)^2/6 := by
  rw [simulationCritical_gate_count]
  constructor
  · nlinarith
  · push_cast
    nlinarith

/-- The paper's explicit choices of the enlarged eye and independent samples. -/
noncomputable def simulationRadius (n : ℕ) (ε δ : ℝ) : ℝ :=
  10*Real.sqrt (Real.log (400*(n:ℝ)^2/(3*ε*δ)))

noncomputable def simulationSampleCount (ε δ : ℝ) : ℕ :=
  ⌈8/ε^2*Real.log (4/δ)⌉₊

noncomputable def simulationWidthBudget (n : ℕ) (R : ℝ) : ℕ :=
  ⌈2*R*Real.sqrt n+1⌉₊

theorem simulationRetainedLayer_le_budget {c d t : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hd : (d:ℝ)=5*(2*(c+1):ℕ)/3) :
    (simulationRetainedLayer c d t R).card ≤ simulationWidthBudget (2*(c+1)) R := by
  have h := (simulationRetainedLayer_critical_card (t:=t) hR hd).trans
    (Nat.le_ceil (2*R*Real.sqrt (2*(c+1):ℕ)+1))
  exact_mod_cast h

theorem simulationWidthBudget_bound {n : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (2*simulationWidthBudget n R+4 : ℕ) < 4*R*Real.sqrt n+8 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2*R*Real.sqrt n+1 by positivity)
  change ((2*⌈2*R*Real.sqrt n+1⌉₊+4 : ℕ):ℝ) < _
  push_cast
  linarith

/-- The N-sample routine repeats the proved local loops and sums the signs. -/
def simulationEstimatorWork (N n finalCoherent : ℕ) (calls : List SimulationLocalCall) : ℕ :=
  N*simulationSampleWork n finalCoherent calls+N+1

theorem simulationEstimatorWork_le (N n finalCoherent W : ℕ)
    (calls : List SimulationLocalCall) (hc : ∀ call ∈ calls, call.coherent ≤ 2*W+4)
    (hf : finalCoherent ≤ 2*W+4) (hn : n ≤ calls.length) :
    simulationEstimatorWork N n finalCoherent calls ≤
      180002*(N+1)*(calls.length+1)*4^(2*W+4) := by
  have h := simulationSampleWork_gate_bound n finalCoherent W calls hc hf hn
  have hp : 1 ≤ 4^(2*W+4) := Nat.one_le_pow _ _ (by decide)
  have hm := Nat.mul_le_mul_left N h
  have hlarge : 1 ≤ (calls.length+1)*4^(2*W+4) := by nlinarith
  have hrest : N+1 ≤ (N+1)*((calls.length+1)*4^(2*W+4)) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold simulationEstimatorWork
  nlinarith

end Fluctuations
