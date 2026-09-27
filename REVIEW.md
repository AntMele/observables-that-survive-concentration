# Review the formalization in manuscript order

[Home](README.md) / [Reader guide](docs/README.md) / Review

Begin with the general fixed-order variance theorem, then review the
one-dimensional OTOC₁ refinement and its simulation application. The
[paper-to-proof map](docs/reference/paper-map.md) connects main-text and
Supplementary Material labels to Lean declarations.

| Order | Review task | Where to start |
| :--- | :--- | :--- |
| **1. General OTOC⁽ᵏ⁾ fluctuations** | Check the mean-change argument, local reverse variance, and consecutive-depth conclusion of VI.14. | [General guide](docs/results/01-general-otoc-variance.md) · [Main.lean](Fluctuations/Main.lean) · [SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean) |
| Supporting ingredients | Check physical support, the numerical Haar coefficient, and the actual global Haar mean. | [Assumptions and correspondence](docs/reviews/assumptions.md#general-spatial-geometry-and-physical-meaning) · [Haar mean guide](docs/reference/haar-mean.md) |
| **2. One-dimensional OTOC₁** | Check the exact mean, variance lower bound, and constructed influential gates. | [OTOC₁ guide](docs/results/02-otoc1-fluctuations.md) · [Independent review](docs/reviews/endpoint.md) |
| **3. Classical simulation** | Check estimator accuracy, the sampler law, and subexponential arithmetic work. | [Simulation guide](docs/results/03-classical-simulation.md) · [Independent review](docs/reviews/simulation.md) |
| Verification | Independently compile the proofs and inspect their axioms. | [Instructions](docs/verification/README.md) · [Recorded evidence](docs/verification/record.txt) |

The [assumption audit](docs/reviews/assumptions.md) distinguishes the generic
probability theorem from the concrete Haar realization. It also records the
remaining mean-control and width inputs, the model restrictions, and claims
in the manuscript that are not yet formalized.

The independent endpoint review covers the fluctuation and exact-mean results
and predates the simulation extension. Simulation has its own review. A Lean
build checks the formal proof; mathematical review additionally checks that
the statement corresponds to the intended claim in the paper.

The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`
for the listed declarations and their dependencies. When reporting a finding,
identify the paper label, Lean declaration, and exact repository revision.
See [Contributing](CONTRIBUTING.md) for the proof-development workflow.
