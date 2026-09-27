# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

[![Lean verification](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml/badge.svg)](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)

Lean 4 companion to the paper's endpoint OTOC fluctuation and classical
simulation results for actual one-dimensional Haar U(4) circuits. It proves
an $\Omega(n^{-1/2})$ variance lower bound throughout the diffusive front
window, a concrete set of $\Theta(n^{3/2})$ contributing gates, and an
accurate classical estimator with subexponential arithmetic cost at critical
depth. The exact finite-circuit Haar mean and one-gate conditional formula
are also proved.

Start with the [fluctuation guide](docs/otoc1.md) and
[OTOC1.lean](Fluctuations/OTOC1.lean), or the
[classical simulation guide](docs/simulation.md) and
[Simulation.lean](Fluctuations/Simulation.lean). The
[earlier independent review](docs/otoc1-review.md) covers the fluctuation and
mean results; it predates the simulation extension.

The project also retains the general spatial variance-window theorem VI.14,
the exact local coefficient $4^{-8km}$, and the actual global-Haar mean bound
at every positive order and dimension. See the
[general mathematical guide](docs/guide.md),
[SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean), and
[paper-to-code map](docs/paper-mapping.md). Design convergence and transition
width remain inputs of that general spatial theorem.

## The first-order endpoint result

For even $n,d$, independent Haar U(4) gates on the open brickwork chain, and
$X_\rho=\mathrm{Tr}[\rho(U_d^\dagger Z_1U_dZ_n)^2]$, assume

```math
|d-5n/3|\le C\sqrt n,\qquad \sqrt n\ge12(C+2),\qquad
C\ge0,\qquad \mathrm{Tr}\rho=1.
```

[OTOC1.lean](Fluctuations/OTOC1.lean) proves, with a proved positive constant
$b_C$ independent of $n,d,\rho$,

```math
\mathrm{Var}(X_\rho)\ge\frac{b_C}{24\sqrt n},\qquad
\frac{n\sqrt n}{24}\le|\mathcal S|\le\frac{2n\sqrt n}{3},\qquad
\mathrm{Var}_{G_z}(\mathbb E[X_\rho\mid G_z])\ge\frac{b_C}{n^2}
\quad(z\in\mathcal S).
```

The set $\mathcal S$ consists of actual physical gates in the central eye.
The conditional mean, propagation factors, local Haar variance, gate count,
and independent-coordinate variance sum are proved. This endpoint theorem
has no design-convergence, mean-change, or mixing hypothesis. Every density
matrix satisfies its trace-one condition.

[BrickworkEndpointMean.lean](Fluctuations/BrickworkEndpointMean.lean) proves
the actual circuit mean through the exact finite endpoint walk and a
binomial-image formula, including zero depth and the two-qubit boundary case.
The manuscript's literal $\Psi$ regrouping, Gaussian mean-front approximation,
and full outer variance-influence envelope remain outside the proved results.

## Classical simulation at critical depth

The simulation theorem concerns the infinite-temperature observable

```math
F_\infty(U_d)=2^{-n}\mathrm{Tr}[(U_d^\dagger Z_1U_dZ_n)^2],
\qquad n=6(s+1),\quad d=10(s+1)=5n/3.
```

For $\varepsilon,\delta\in(0,1)$, choose

```math
R=10\sqrt{\log\frac{400n^2}{3\varepsilon\delta}},
\qquad N=\left\lceil\frac8{\varepsilon^2}\log\frac4\delta\right\rceil.
```

`otoc1_subexponential_simulation` in
[Simulation.lean](Fluctuations/Simulation.lean) proves

```math
\Pr[|\widetilde F-F_\infty(U_d)|\le\varepsilon]\ge1-\delta.
```

The probability is over both the Haar circuit and the algorithm's samples.
The algorithm retains the realized gates in the enlarged eye, averages the
other gates, and samples the resulting conditional Pauli distribution using
one coherent vector. The local perturbation estimate, averaging error,
exact sampler law, and concentration bound are proved; no bias, local
reverse-variance, or mean-change estimate is supplied to the final theorem.

For the counted sampling and readout loops, the explicit arithmetic bound is

```math
180002(N+1)n^2\,4^{\,2\lceil2R\sqrt n+1\rceil+4}.
```

For $\varepsilon=n^{-a}$ and $\delta=n^{-b}$ with fixed positive natural
exponents, `otoc1_subexponential_simulation_inversePolynomial` proves both
the accuracy guarantee at every size and $\log(\mathrm{work})/n\to0$ for
the same sampler. A concrete
$\mathrm{poly}(n)\,2^{O(\sqrt{n\log n})}$ majorant is also proved.
The model assumes exact scalar arithmetic (real or complex) and exact sampling from explicitly
computed finite distributions, as in the manuscript. The counter includes
transfer-matrix construction and the sampling and readout arithmetic; it
excludes indexing, stored-coefficient reads, and preprocessing that constructs
the schedule or computes its parameters. This is a formal algorithm and cost
analysis, without an extracted numerical executable or a bit-complexity or
finite-precision-stability claim. See the
[simulation guide](docs/simulation.md) for the operation counts and scope.

The fluctuation theorem above holds for every trace-one state; this
simulation theorem uses the maximally mixed state $I/2^n$.

## The general spatial Haar result

Each parallel layer consists of independent Haar SU(4) gates on disjoint pairs
of qubits. The matrices act on the full basis `Site → Fin 2`; the embedding
inserts the actual gate on its two sites and the identity elsewhere.

Let $B$ have support $S$, with $s=|S|$, and write

```math
F_d=\mathrm{Tr}\!\left[\rho\left(U_d^\dagger B U_dM\right)^{2k}\right],
\qquad \eta=4^{-8ks},\qquad \kappa=\frac{\eta}{1+\eta}.
```

A gate is active if its patch meets $S$. Lean proves that there are at most
$s$ active gates, that the inactive gates cancel from the fresh conjugation of
$B$, and that the local reverse-variance inequality holds with this explicit
$\eta$. All gates remain in the circuit history.

Given $a<b$, $b-a\le P$, and a half-unit change of the mean, Lean proves that
for every fixed $R$, some $a<d_*\le b$ satisfies

```math
\mathrm{Var}(F_{d_*+r})\ge
\frac{\eta\kappa^R}{4P^2}
\qquad (0\le r\le R).
```

This is `spatialHaarCircuit_variance_window`. For fixed $s,k,R$ and polynomial
$P$, the numerator is independent of system size and the number of inactive
gates. The assembled Haar history currently uses fixed active and inactive
counts across depths of each process; patches may change with depth. The
separate deterministic geometry results also allow variable gate counts.

## What is proved and what remains

| Ingredient | Status |
| --- | --- |
| Actual 1D Haar U(4) endpoint variance, many-gate influence, and exact conditional mean | Proved in [OTOC1.lean](Fluctuations/OTOC1.lean) and [BrickworkEndpointOTOC.lean](Fluctuations/BrickworkEndpointOTOC.lean) |
| Infinite-temperature endpoint simulation at critical depth: actual joint success probability and subexponential arithmetic cost | Proved in [Simulation.lean](Fluctuations/Simulation.lean), [SimulationAsymptotics.lean](Fluctuations/SimulationAsymptotics.lean) |
| Actual finite-circuit endpoint Haar mean and binomial-image expression | Proved in [BrickworkEndpointMean.lean](Fluctuations/BrickworkEndpointMean.lean) |
| Actual SU(4), independent normalized Haar gates, physical two-site embeddings | Proved |
| Disjoint support implies commutation; deterministic backward cone and early OTOC identity | Proved |
| Active count at most $\lvert S\rvert$; constant-depth support and active-block bounds | Proved |
| Exact local coefficient $4^{-8km}$ for $m$ gates, including conditional variance | Proved |
| Slope-to-variance, persistence, consecutive window, abstract polynomial-family bound | Proved |
| Actual global U($D$) Haar measure and OTOC mean, with Haar symmetry identities | Defined and proved in [GlobalHaarMean.lean](Fluctuations/GlobalHaarMean.lean) |
| State independence for every Hermitian, traceless involution probe, at all orders | Proved in [GlobalHaarPauliMean.lean](Fluctuations/GlobalHaarPauliMean.lean) |
| Actual Haar integration formula, inverse-Gram coefficients, and Pauli trace contractions | Proved |
| All-orders estimate $\lvert h\rvert\le 2((2k)!)^3/D^2$ in every dimension | Proved in [GlobalHaarMeanAllDimensions.lean](Fluctuations/GlobalHaarMeanAllDimensions.lean) |
| Exact first-order mean $h=-1/(D^2-1)$ | Proved in [GlobalHaarFirstOrderValue.lean](Fluctuations/GlobalHaarFirstOrderValue.lean) |
| Design convergence and polynomial mixing depth | External input |

`spatialHaarCircuit_allOrders_of_globalHaar_control` uses the **actual
normalized global-Haar mean** of the same observable. For Hermitian, traceless
involutions $B,M$ and $\mathrm{Tr}\rho=1$, it proves the Haar
quarter-bound whenever

```math
D=2^n,\qquad k\ge1,\qquad D^2\ge8((2k)!)^3.
```

Geometry gives the early mean $1$. The remaining analytic input is the
late observable-specific moment error $|\mathbb EF_b-h|\le1/4$, supplied
by design convergence; together these give the half-unit gap. The architecture,
observable support, cone separation, and transition-width bound are explicit
hypotheses. The first-order wrapper needs only $n\ge2$ for Haar smallness.

The inverse-square Haar estimate holds in every nonzero dimension. The
displayed threshold is needed only to make it at most $1/4$.

The general spatial pipeline uses SU(4); its phase-invariance/Haar-law bridge
to the manuscript's U(4) convention remains a correspondence step. The
one-dimensional endpoint pipeline uses genuine U(4) directly and has neither
this gap nor the fixed active/inactive-count restriction. General
graph-distance speeds and computational quantum advantage are not established.

## Read the proof

| Purpose | Source |
| --- | --- |
| Classical simulation: target, sampler, error and runtime | [Simulation.lean](Fluctuations/Simulation.lean), explained in [docs/simulation.md](docs/simulation.md) |
| Endpoint variance and many-gate influence | [OTOC1.lean](Fluctuations/OTOC1.lean), explained in [docs/otoc1.md](docs/otoc1.md) |
| Actual endpoint conditional mean and finite-depth mean | [BrickworkEndpointOTOC.lean](Fluctuations/BrickworkEndpointOTOC.lean), [BrickworkEndpointMean.lean](Fluctuations/BrickworkEndpointMean.lean) |
| Final spatial variance theorem | [SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean); first order: [SpatialHaarFirstOrder.lean](Fluctuations/SpatialHaarFirstOrder.lean) |
| Concrete support, patch insertion, and cones | [TensorSupport.lean](Fluctuations/TensorSupport.lean), [PatchEmbedding.lean](Fluctuations/PatchEmbedding.lean), [CircuitGeometry.lean](Fluctuations/CircuitGeometry.lean), [SpatialHaarGeometry.lean](Fluctuations/SpatialHaarGeometry.lean) |
| Explicit Haar coefficient | [HaarEvaluationBound.lean](Fluctuations/HaarEvaluationBound.lean), [BalancedHaarFeatures.lean](Fluctuations/BalancedHaarFeatures.lean), [ExplicitHaarVariance.lean](Fluctuations/ExplicitHaarVariance.lean) |
| Numerical full-layer theorem | [ExplicitHaarCircuit.lean](Fluctuations/ExplicitHaarCircuit.lean) |
| Actual global-Haar reference and state independence | [GlobalHaarMean.lean](Fluctuations/GlobalHaarMean.lean), [GlobalHaarPauliMean.lean](Fluctuations/GlobalHaarPauliMean.lean) |
| Complete Haar mean bound | [GlobalHaarMeanBound.lean](Fluctuations/GlobalHaarMeanBound.lean), [HaarWeingartenProjection.lean](Fluctuations/HaarWeingartenProjection.lean), [WeingartenGramBounds.lean](Fluctuations/WeingartenGramBounds.lean) |
| General ensembles and polynomial families | [Main.lean](Fluctuations/Main.lean) |

## Verify

Lean **4.24.0** and mathlib **v4.24.0** are pinned.

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

The scripts build the library, with all local modules compiled in dependency
order by the offline helper, and enforce a declaration-by-declaration
axiom allowlist: only `propext`, `Classical.choice`, and `Quot.sound`. Explicit
mathematical hypotheses must still be reviewed. See [reproduction instructions](docs/reproduce.md)
and the [verification record](docs/verification.txt) for the checked source.
A successful older CI run does not certify later edits.

When citing this companion, record the repository revision, theorem declaration,
and paper version. [Manuscript fingerprints](docs/paper-mapping.md#manuscript-provenance)
identify the inspected draft. The early shared gist is a historical snapshot
and does not contain the subsequent extensions.
