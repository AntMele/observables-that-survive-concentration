import Fluctuations.SimulationGeometryCost
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative meaning of the subexponential arithmetic bound. The final
limit is `log(work bound)/n → 0`, not merely a suggestive name for a function.
The parameter choices are exactly those of the manuscript. -/
open Filter
open scoped Topology
namespace Fluctuations
noncomputable section

/-- Logarithmic eye radius at inverse-polynomial precision and failure rate. -/
def simulationPolynomialLog (a b : ℕ) (x : ℝ) : ℝ :=
  Real.log (400/3:ℝ)+(2+(a:ℝ)+b)*Real.log x

/-- An explicit majorant of the arithmetic work, expressed logarithmically. -/
def simulationLogWorkEnvelope (a b : ℕ) (x : ℝ) : ℝ :=
  Real.log (360004*(8*((b:ℝ)+4)+2))+(2*(a:ℝ)+3)*Real.log x+
    Real.log 4*(40*Real.sqrt (x*simulationPolynomialLog a b x)+8)

def simulationWorkEnvelope (a b : ℕ) (x : ℝ) : ℝ :=
  Real.exp (simulationLogWorkEnvelope a b x)

lemma simulationPolynomialLog_nonneg (a b : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ simulationPolynomialLog a b x := by
  unfold simulationPolynomialLog
  have hlog := Real.log_nonneg hx
  have hc := Real.log_nonneg (show (1:ℝ) ≤ 400/3 by norm_num)
  positivity

theorem simulationRadius_inversePolynomial (a b n : ℕ) (hn : 0 < n) :
    simulationRadius n (1/(n:ℝ)^a) (1/(n:ℝ)^b) =
      10*Real.sqrt (simulationPolynomialLog a b n) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hne : (n:ℝ) ≠ 0 := ne_of_gt hp
  unfold simulationRadius simulationPolynomialLog
  congr 2
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num : (400:ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity : (3*(1/(n:ℝ)^a)) ≠ 0) (by positivity),
    Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (pow_ne_zero _ hne),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (pow_ne_zero _ hne),
    Real.log_div (by norm_num : (400:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
  simp only [Real.log_one,Real.log_pow]
  ring

lemma simulationSampleCount_inversePolynomial (a b n : ℕ) (hn : 0 < n) :
    (simulationSampleCount (1/(n:ℝ)^a) (1/(n:ℝ)^b) + 1 : ℕ) ≤
      (8*((b:ℝ)+4)+2)*(n:ℝ)^(2*a+1) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hne := ne_of_gt hp
  have hlog : Real.log (4/(1/(n:ℝ)^b)) = Real.log 4+(b:ℝ)*Real.log n := by
    rw [one_div, div_inv_eq_mul, Real.log_mul (by norm_num : (4:ℝ)≠0) (pow_ne_zero _ hne),Real.log_pow]
  have hl4 : Real.log 4 ≤ (4:ℝ) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have hln : Real.log n ≤ (n:ℝ) := by linarith [Real.log_le_sub_one_of_pos hp]
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hbound : Real.log (4/(1/(n:ℝ)^b)) ≤ ((b:ℝ)+4)*n := by
    rw [hlog]
    nlinarith
  have hlog0 : 0 ≤ Real.log (4/(1/(n:ℝ)^b)) := by
    rw [hlog]
    positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8/(1/(n:ℝ)^a)^2*Real.log (4/(1/(n:ℝ)^b)) by positivity)
  have hpow : 8/(1/(n:ℝ)^a)^2 = 8*(n:ℝ)^(2*a) := by
    rw [one_div_pow,one_div,div_inv_eq_mul,← pow_mul]
    rw [Nat.mul_comm a 2]
  rw [hpow] at hc
  have hm := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 8*(n:ℝ)^(2*a) by positivity)
  have hp1 : 1 ≤ (n:ℝ)^(2*a+1) := one_le_pow₀ h1
  change ((⌈8/(1/(n:ℝ)^a)^2*Real.log (4/(1/(n:ℝ)^b))⌉₊+1 : ℕ):ℝ) ≤ _
  push_cast
  rw [hpow]
  rw [show (n:ℝ)^(2*a+1)=(n:ℝ)^(2*a)*(n:ℝ) by rw [pow_succ]]
  rw [pow_succ] at hp1
  nlinarith

/-- Evaluate the explicit exponential majorant as a polynomial times the
coherent-array exponential. -/
lemma simulationWorkEnvelope_eq (a b : ℕ) {x : ℝ} (hx : 0 < x) :
    simulationWorkEnvelope a b x =
      (360004*(8*((b:ℝ)+4)+2))*x^(2*a+3)*
        Real.exp (Real.log 4*(40*Real.sqrt (x*simulationPolynomialLog a b x)+8)) := by
  unfold simulationWorkEnvelope simulationLogWorkEnvelope
  rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity)]
  have he : Real.exp ((2*(a:ℝ)+3)*Real.log x) = x^(2*a+3) := by
    have hh := Real.exp_nat_mul (Real.log x) (2*a+3)
    rw [Real.exp_log hx] at hh
    convert hh using 1
    push_cast
    ring
  rw [he]

/-- The manuscript's exact choices `epsilon=n^-a`, `delta=n^-b` give a proved
subexponential bound for the generated physical sampler schedule. -/
theorem simulationCritical_inversePolynomial_work (s a b : ℕ) :
    let n := 6*(s+1)
    let R := simulationRadius n (1/(n:ℝ)^a) (1/(n:ℝ)^b)
    let N := simulationSampleCount (1/(n:ℝ)^a) (1/(n:ℝ)^b)
    (simulationEstimatorWork N n
      (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
      (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1))) : ℝ) ≤
      simulationWorkEnvelope a b n := by
  dsimp only
  let n := 6*(s+1)
  let R := simulationRadius n (1/(n:ℝ)^a) (1/(n:ℝ)^b)
  let N := simulationSampleCount (1/(n:ℝ)^a) (1/(n:ℝ)^b)
  have hn : 0 < n := by dsimp [n]; positivity
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hR : 0 ≤ R := by dsimp [R,simulationRadius]; positivity
  have hwork := simulationCritical_estimatorWork s N hR
  have hworkr := (Nat.cast_le (α:=ℝ)).mpr hwork
  push_cast at hworkr
  have hN := simulationSampleCount_inversePolynomial a b n hn
  have hK := simulationWidthBudget_bound (n:=n) hR
  have hReq := simulationRadius_inversePolynomial a b n hn
  have hK' : ((2*simulationWidthBudget n R+4:ℕ):ℝ) ≤
      40*Real.sqrt ((n:ℝ)*simulationPolynomialLog a b n)+8 := by
    dsimp [R] at hK ⊢
    rw [hReq] at hK ⊢
    rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ))]
    nlinarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpow : (4:ℝ)^(2*simulationWidthBudget n R+4) ≤
      Real.exp (Real.log 4*(40*Real.sqrt ((n:ℝ)*simulationPolynomialLog a b n)+8)) := by
    calc
      _ = Real.exp (((2*simulationWidthBudget n R+4:ℕ):ℝ)*Real.log 4) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hcoef : (180002:ℝ)*((N:ℝ)+1)*(n:ℝ)^2 ≤
      (360004*(8*((b:ℝ)+4)+2))*(n:ℝ)^(2*a+3) := by
    have hm := mul_le_mul_of_nonneg_right hN (show 0 ≤ (180002:ℝ)*(n:ℝ)^2 by positivity)
    change (((N+1:ℕ):ℝ)) ≤ _ at hN
    push_cast at hN hm
    have he : (n:ℝ)^(2*a+3)=(n:ℝ)^(2*a+1)*(n:ℝ)^2 := by
      rw [←pow_add]
    rw [he]
    dsimp [N]
    change (simulationSampleCount (1/(n:ℝ)^a) (1/(n:ℝ)^b):ℝ)+1 ≤ _ at hN
    nlinarith [show (0:ℝ) ≤ (8*((b:ℝ)+4)+2)*(n:ℝ)^(2*a+1)*(n:ℝ)^2 by positivity]
  have hm := mul_le_mul hcoef hpow (by positivity)
    (show (0:ℝ) ≤ (360004*(8*((b:ℝ)+4)+2))*(n:ℝ)^(2*a+3) by positivity)
  rw [← simulationWorkEnvelope_eq a b hnr] at hm
  change (simulationEstimatorWork N n _ _ : ℝ) ≤ simulationWorkEnvelope a b n
  exact hworkr.trans (by simpa [n] using hm)

lemma simulation_sqrt_ratio {x H : ℝ} (hx : 0 < x) (hH : 0 ≤ H) :
    Real.sqrt (x*H)/x = Real.sqrt (H/x) := by
  have he : H/x = (x*H)/(x^2) := by field_simp
  rw [he, Real.sqrt_div (mul_nonneg hx.le hH), Real.sqrt_sq hx.le]

/-- The square-root-log eye growth is genuinely sublinear. -/
theorem simulation_sqrtLog_div_tendsto (a b : ℕ) :
    Tendsto (fun x : ℝ => Real.sqrt (x*simulationPolynomialLog a b x)/x)
      atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hc : Tendsto (fun x : ℝ => Real.log (400/3:ℝ)/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum := hc.add (hlog.const_mul (2+(a:ℝ)+b))
  have hh : Tendsto (fun x : ℝ => simulationPolynomialLog a b x/x) atTop (𝓝 0) := by
    convert hsum using 1
    · ext x
      simp only [simulationPolynomialLog,add_div,mul_div_assoc,id_eq]
    · ring_nf
  have hs := hh.sqrt
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  exact (simulation_sqrt_ratio (by linarith) (simulationPolynomialLog_nonneg a b hx)).symm

/-- The precise subexponential assertion: the logarithm of the explicit
arithmetic-work majorant, divided by system size, tends to zero. -/
theorem simulationWorkEnvelope_subexponential (a b : ℕ) :
    Tendsto (fun x : ℝ => Real.log (simulationWorkEnvelope a b x)/x)
      atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hc : Tendsto (fun x : ℝ =>
      (Real.log (360004*(8*((b:ℝ)+4)+2))+8*Real.log 4)/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := (hc.add (hlog.const_mul (2*(a:ℝ)+3))).add
    ((simulation_sqrtLog_div_tendsto a b).const_mul (40*Real.log 4))
  convert h using 1
  · ext x
    simp only [simulationWorkEnvelope,Real.log_exp,simulationLogWorkEnvelope,id_eq]
    ring
  · ring_nf

/-- Equivalently, for every positive exponential rate, the bound is eventually
smaller than that exponential. This includes all inverse-polynomial choices. -/
theorem simulationWorkEnvelope_eventually_le_exp (a b : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, simulationWorkEnvelope a b x ≤ Real.exp (η*x) := by
  have h := (simulationWorkEnvelope_subexponential a b).eventually (gt_mem_nhds hη)
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with x hx hpos
  have he := (div_lt_iff₀ hpos).mp hx
  rw [← Real.exp_log (show 0 < simulationWorkEnvelope a b x from Real.exp_pos _)]
  exact Real.exp_le_exp.mpr he.le

/-- Arithmetic work of the actual generated schedule, with the paper's
inverse-polynomial parameter choices. -/
def simulationCriticalPolynomialWork (s a b : ℕ) : ℕ :=
  let n := 6*(s+1)
  let R := simulationRadius n (1/(n:ℝ)^a) (1/(n:ℝ)^b)
  let N := simulationSampleCount (1/(n:ℝ)^a) (1/(n:ℝ)^b)
  simulationEstimatorWork N n
    (simulationCoherentAfter (3*s+2) (10*(s+1)) R (10*(s+1))).card
    (simulationCircuitCalls (3*s+2) (10*(s+1)) R (10*(s+1)))

/-- Subexponential cost for the concrete physical call schedule itself. -/
theorem simulationCriticalPolynomialWork_subexponential (a b : ℕ) :
    Tendsto (fun s : ℕ => Real.log (simulationCriticalPolynomialWork s a b)/
      (6*(s+1):ℕ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun s : ℕ => (6*(s+1):ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with s hs
    omega
  have hnr := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hn
  have h := (simulationWorkEnvelope_subexponential a b).comp hnr
  apply squeeze_zero' _ _ h
  · filter_upwards [] with s
    have hp : (1:ℝ) ≤ simulationCriticalPolynomialWork s a b := by
      have hh : 1 ≤ simulationCriticalPolynomialWork s a b := by
        dsimp [simulationCriticalPolynomialWork,simulationEstimatorWork]
        omega
      exact_mod_cast hh
    exact div_nonneg (Real.log_nonneg hp) (by positivity)
  · filter_upwards [] with s
    have hw := simulationCritical_inversePolynomial_work s a b
    change (simulationCriticalPolynomialWork s a b:ℝ) ≤
      simulationWorkEnvelope a b (6*(s+1):ℕ) at hw
    have hp : (0:ℝ) < simulationCriticalPolynomialWork s a b := by
      have hh : 0 < simulationCriticalPolynomialWork s a b := by
        dsimp [simulationCriticalPolynomialWork,simulationEstimatorWork]
        omega
      exact_mod_cast hh
    exact div_le_div_of_nonneg_right (Real.log_le_log hp hw) (by positivity)

end
end Fluctuations
