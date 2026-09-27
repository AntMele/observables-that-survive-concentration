# Review the formalization

[Home](README.md) / [Reader guide](docs/README.md) / Review

Review the mathematical statement and its hypotheses alongside the Lean proof.
The [paper-to-code map](docs/reference/paper-map.md) connects manuscript labels
to the corresponding declarations; the
[assumption review](docs/reviews/assumptions.md) explains exactly what remains
an input to each final theorem.

| Review task | Where to start |
| --- | --- |
| Check the endpoint variance theorem and influential gates | [Result guide](docs/results/endpoint-fluctuations.md) · [Independent review](docs/reviews/endpoint.md) |
| Check the classical estimator and subexponential arithmetic cost | [Result guide](docs/results/classical-simulation.md) · [Independent review](docs/reviews/simulation.md) |
| Check the general variance-window theorem VI.14 | [Result guide](docs/results/spatial-variance.md) · [Assumptions and correspondence](docs/reviews/assumptions.md#general-spatial-geometry-and-physical-meaning) |
| Check the global Haar mean estimates | [Result guide](docs/results/haar-mean.md) · [Mean assumption boundary](docs/reviews/assumptions.md#the-mean-assumption-boundary) |
| Independently compile and audit the proofs | [Reproduction instructions](docs/verification/README.md) · [Verification record](docs/verification/record.txt) |

The endpoint review is a historical, scope-specific review of the fluctuation
and mean results. The simulation extension has its own review. Both distinguish
proved ingredients from the hypotheses appearing in the final theorem.

A successful build checks the formal proof. Review also establishes that its
statement matches the intended claim in the paper. The enforced axiom audit
permits only `propext`, `Classical.choice`, and `Quot.sound` for the listed
declarations and their transitive dependencies.

When reporting a finding, identify the manuscript label, Lean declaration,
and exact repository revision. For changes to the proof or documentation,
see [Contributing](CONTRIBUTING.md).
