# Observables that survive concentration

### Towards verifiable quantum advantage with random circuits

**Lean 4 companion to the paper** · General OTOC fluctuations → one-dimensional OTOC₁ → classical simulation

[CI workflow & live status](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml) ·
[![Lean 4.24.0](https://img.shields.io/badge/Lean-4.24.0-blue)](lean-toolchain)
[![mathlib v4.24.0](https://img.shields.io/badge/mathlib-v4.24.0-blue)](lakefile.toml)

[**Read alongside the paper →**](docs/README.md) · [Paper → proof map](docs/reference/paper-map.md) · [Lean source index](Fluctuations/README.md) · [Verification](docs/verification/README.md)

The paper asks whether local random circuits retain resolvable OTOC
fluctuations at system-scale depths. Its central result is a **general
variance lower bound for every fixed OTOC order**. The one-dimensional
OTOC₁ analysis then sharpens this result and leads to a classical simulation
algorithm. This repository follows that order.

## 1. General variance lower bound for OTOC⁽ᵏ⁾

**Main text §II · Supplementary Material §VI, Theorem VI.14**

A constant change in the ensemble mean over a polynomial depth interval
forces inverse-polynomial variance over consecutive depths. The proof
converts a change of the mean into variance through a local reverse-variance
bound, then propagates that variance forward.

More precisely, if the mean changes by at least $1/2$ between depths $a<b$
with $b-a\le P$, the local reverse-variance condition with constant $\eta>0$
gives a depth $a<d_*\le b$ such that

```math
\mathrm{Var}(F_{d_*+r})\ge
\frac{\eta}{4P^2}\left(\frac{\eta}{1+\eta}\right)^R,
\qquad 0\le r\le R.
```

Here $F_d$ is the OTOC of order $k$. For fixed $R$ and a size-independent
$\eta$, a polynomial bound on $P$ gives the claimed inverse-polynomial
fluctuations.

Lean proves the general probability theorem and a spatial Haar SU(4)
realization. In that realization it also proves the local coefficient,
physical support bounds, and global Haar smallness. Late mean control from
design convergence and the transition-width bound remain inputs.

**[Read the general theorem](docs/results/01-general-otoc-variance.md)** ·
[Abstract proof](Fluctuations/Main.lean) ·
[Spatial Haar theorem](Fluctuations/SpatialHaarFinal.lean)

Supporting ingredient: [global Haar mean estimates](docs/reference/haar-mean.md).
The [scope review](docs/reviews/assumptions.md) records the precise models and assumptions.

## 2. Sharper results for one-dimensional OTOC₁

**Main text §III · Supplementary Material §VII**

For endpoint observables in open Haar U(4) brickwork circuits, Lean proves
an $\Omega(n^{-1/2})$ variance lower bound throughout the diffusive front
window around $d=5n/3$, and constructs $\Theta(n^{3/2})$ gates with individual
contributions $\Omega(n^{-2})$. These results hold uniformly over trace-one
states under the explicit size and depth conditions. The exact finite-depth
mean is also proved. No design-convergence hypothesis is needed here.

**[Read the OTOC₁ results](docs/results/02-otoc1-fluctuations.md)** ·
[Final theorems](Fluctuations/OTOC1.lean) ·
[Exact mean](Fluctuations/BrickworkEndpointMean.lean)

## 3. Application: subexponential classical simulation

**Main text §III B · Supplementary Material §VIII**

The one-dimensional structure yields an estimator for the
infinite-temperature endpoint OTOC at $d=5n/3$, for positive multiples of
six qubits. Lean proves its joint circuit-and-sampler accuracy guarantee
and subexponential arithmetic work for inverse-polynomial error and failure
parameters. The model uses exact scalar arithmetic and finite-distribution
sampling.

**[Read the algorithm and cost bound](docs/results/03-classical-simulation.md)** ·
[Final theorems](Fluctuations/Simulation.lean)

## Check or explore the formalization

| Purpose | Starting point |
| :--- | :--- |
| Follow the manuscript in order | [Reader guide](docs/README.md) and [paper-to-proof map](docs/reference/paper-map.md) |
| Find supporting Lean lemmas | [129-module source index](Fluctuations/README.md), grouped by the three parts above |
| Review the claims and their scope | [Reviewer guide](REVIEW.md) and [assumption audit](docs/reviews/assumptions.md) |
| Reproduce or extend the proof | [Verification instructions](docs/verification/README.md) and [contribution guide](CONTRIBUTING.md) |

The recorded complete build checks **129 modules** and audits **573 declarations**,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
[Checked source and verification evidence](docs/verification/record.txt)

<details>
<summary><strong>Quick start: reproduce the Lean checks</strong></summary>

With [Lean’s `elan` toolchain manager](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

Lean **4.24.0** and mathlib **v4.24.0** are pinned.

</details>

When citing a formal result, record the repository revision, theorem
declaration, and [paper version](docs/reference/paper-map.md#manuscript-provenance).
The previously shared gist is a historical snapshot; this repository contains
the subsequent extensions.
