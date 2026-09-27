# Observables that survive concentration

### Towards verifiable quantum advantage with random circuits

**Lean 4 companion to the paper** · Statements, proofs, and reproducible verification

[CI workflow & live status](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml) ·
[![Lean 4.24.0](https://img.shields.io/badge/Lean-4.24.0-blue)](lean-toolchain)
[![mathlib v4.24.0](https://img.shields.io/badge/mathlib-v4.24.0-blue)](lakefile.toml)

[**Start reading →**](docs/README.md) · [Paper → proof map](docs/reference/paper-map.md) · [Lean source index](Fluctuations/README.md) · [Verify the proofs](docs/verification/README.md)

This repository formalizes the paper’s endpoint OTOC fluctuations, classical
simulation algorithm, general variance-window argument, and global Haar mean
estimates. Each result has an English guide explaining its assumptions and a
direct link to the final Lean theorem.

## Find your result

| Result in the paper | What Lean proves | Read the proof |
| :--- | :--- | :--- |
| **Endpoint OTOC₁ fluctuations** | Variance of order at least $n^{-1/2}$ throughout the diffusive front window, with a constructed set of order $n^{3/2}$ influential gates. | [Statement & assumptions](docs/results/endpoint-fluctuations.md) · [Lean](Fluctuations/OTOC1.lean) |
| **Subexponential classical simulation** | An accurate infinite-temperature endpoint-OTOC estimator at critical depth, with subexponential arithmetic work for inverse-polynomial accuracy parameters. | [Algorithm & cost model](docs/results/classical-simulation.md) · [Lean](Fluctuations/Simulation.lean) |
| **General variance window · VI.14** | A controlled change in the mean forces a consecutive window of large variance; the local Haar coefficient and spatial support bounds are proved. | [Statement & remaining inputs](docs/results/spatial-variance.md) · [Lean](Fluctuations/SpatialHaarFinal.lean) |
| **Global Haar mean** | The all-order bound $2((2k)!)^3/D^2$ and the exact first-order value $-1/(D^2-1)$. | [Statement & proof route](docs/results/haar-mean.md) · [Lean](Fluctuations/GlobalHaarMeanAllDimensions.lean) |

The endpoint results use actual open one-dimensional Haar U(4) circuits.
Simulation is at infinite temperature and critical depth, with probability
over both the circuit and the sampler. The general spatial theorem uses
Haar SU(4) gates and retains design mean control and transition width as
inputs. See the [assumption boundary](docs/reviews/assumptions.md) for the full scope.

## Choose a reading route

- **Reading the paper?** Start with the [reader guide](docs/README.md), then use the [paper-to-proof map](docs/reference/paper-map.md) to find a theorem by its manuscript label.
- **Reviewing the formalization?** Follow the [reviewer guide](REVIEW.md) for theorem correspondence, assumptions, and verification evidence.
- **Working in Lean?** Browse the [129-module source index](Fluctuations/README.md), reproduce the build below, and read [CONTRIBUTING.md](CONTRIBUTING.md).

## Reproduce the verification

With [Lean’s `elan` toolchain manager](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

Lean **4.24.0** and mathlib **v4.24.0** are pinned. The recorded complete build
checks **129 modules** and audits **573 declarations**, allowing only Lean’s
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
[Build instructions](docs/verification/README.md) · [Checked source & evidence](docs/verification/record.txt)

## Repository at a glance

```text
Fluctuations/      Lean proofs, with a topic index
  README.md       Entry points and expandable module catalog
docs/
  README.md       Reader guide
  results/        Four result guides with precise scope
  reference/      Manuscript labels → Lean declarations
  reviews/        Assumption audit and independent reviews
  verification/   Build instructions and recorded evidence
scripts/          Build and axiom-audit tools
REVIEW.md         Reviewer starting point
CONTRIBUTING.md   Proof-development workflow
```

When referring to a formal result, record the repository revision, Lean
declaration, and paper version. The [manuscript provenance](docs/reference/paper-map.md#manuscript-provenance)
identifies the inspected draft. The previously shared gist is a historical
snapshot; this repository contains the subsequent extensions.
