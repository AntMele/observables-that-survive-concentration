# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

[![Lean verification](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml/badge.svg)](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)

Lean 4 companion to the paper's variance lower bound, Theorem VI.14 in the
inspected manuscript. The project proves the probability argument, the exact
Haar SU(4) local coefficient, and the geometric certificates for concrete
finite-qubit circuits. It also proves the actual global-Haar mean bound at
every positive order and dimension, and gives an explicit size threshold for
the variance theorem. Design convergence and the transition-width bound
remain external inputs.

Start with the [mathematical guide](docs/guide.md), then the
[paper-to-code map](docs/paper-mapping.md). The strongest assembled spatial
result is in [SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean).
[REVIEW.md](REVIEW.md) lists the assumptions to inspect.

## The spatial Haar result

Each parallel layer consists of independent Haar SU(4) gates on disjoint pairs
of qubits. The matrices act on the full basis `Site → Fin 2`; the embedding
inserts the actual gate on its two sites and the identity elsewhere.

Let $B$ have support $S$, with $s=|S|$, and write

```math
F_d=\operatorname{Tr}\!\left[\rho\left(U_d^\dagger B U_dM\right)^{2k}\right],
\qquad \eta=4^{-8ks},\qquad \kappa=\frac{\eta}{1+\eta}.
```

A gate is active if its patch meets $S$. Lean proves that there are at most
$s$ active gates, that the inactive gates cancel from the fresh conjugation of
$B$, and that the local reverse-variance inequality holds with this explicit
$\eta$. All gates remain in the circuit history.

Given $a<b$, $b-a\le P$, and a half-unit change of the mean, Lean proves that
for every fixed $R$, some $a<d_*\le b$ satisfies

```math
\operatorname{Var}(F_{d_*+r})\ge
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
involutions $B,M$ and $\operatorname{Tr}\rho=1$, it proves the Haar
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

The formalized local ensemble is SU(4). The phase-invariance/Haar-law bridge to
the manuscript's U(4) convention is a remaining correspondence step. Specific
graph-distance speeds, the sharper one-dimensional fluctuation theorem, and
computational quantum advantage are not established here.

## Read the proof

| Purpose | Source |
| --- | --- |
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

The script builds the imported library and enforces a declaration-by-declaration
axiom allowlist: only `propext`, `Classical.choice`, and `Quot.sound`. Explicit
mathematical hypotheses must still be reviewed. See [reproduction instructions](docs/reproduce.md)
and the [verification record](docs/verification.txt) for the checked source.
A successful older CI run does not certify later edits.

When citing this companion, record the repository revision, theorem declaration,
and paper version. [Manuscript fingerprints](docs/paper-mapping.md#manuscript-provenance)
identify the inspected draft. The early shared gist is a historical snapshot
and does not contain the subsequent extensions.
