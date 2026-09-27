# Contributing

[Home](README.md) / [Reader guide](docs/README.md) / Contributing

Start with the [general OTOC(k) variance theorem](docs/results/01-general-otoc-variance.md),
then follow the manuscript to the one-dimensional OTOC₁ results and classical
simulation. Use the [paper-to-proof map](docs/reference/paper-map.md) to match
a manuscript statement, and the [review guide](REVIEW.md) to check its scope.

| Manuscript chapter | Guide | Main Lean entry points |
| :--- | :--- | :--- |
| **I. General OTOC(k) variance** | [Variance window · Theorem VI.14](docs/results/01-general-otoc-variance.md) | [SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean), [Main.lean](Fluctuations/Main.lean) |
| **II. One-dimensional OTOC₁** | [Exact mean, fluctuations, and influential gates](docs/results/02-otoc1-fluctuations.md) | [BrickworkEndpointMean.lean](Fluctuations/BrickworkEndpointMean.lean), [OTOC1.lean](Fluctuations/OTOC1.lean) |
| **III. Classical simulation** | [Accuracy and subexponential work](docs/results/03-classical-simulation.md) | [Simulation.lean](Fluctuations/Simulation.lean) |

The [global Haar mean estimates](docs/reference/haar-mean.md), local reverse
variance, and spatial support bounds belong to Chapter I’s proof route.
The [complete source index](Fluctuations/README.md) groups all supporting
modules within these three chapters.

For a theorem change, explain the mathematical statement before and after the
change. Identify any changes to assumptions, constants, quantifier order,
depth ranges, or manuscript correspondence. Keep the distinction between the
proved Haar local inequality and the assumed local condition for general
ensembles. In the spatial circuit theorem, locality certificates and the active-count
bound follow from physical patches and tensor support. The exact Haar constant
is `explicitHaarConstant m k`. The final global-Haar bound proves smallness
under explicit dimension threshold; no scalar integration identity or
smallness premise remains in the final spatial wrapper. Keep the design-control,
width, geometric, observable, and dimension hypotheses visible.
Keep constants independent of ambient dimension and inactive gate count for
fixed observable support and OTOC order.

Do not add `sorry`, `admit`, or custom axioms. All listed results and their
transitive dependencies must use only `propext`, `Classical.choice`, and
`Quot.sound`. Add new principal results explicitly to both
`scripts/Audit.lean` and the expected declaration list in
`scripts/check-axioms.py`. Update the library imports and offline build sequence
when adding a module. The offline build orders local modules automatically.
For the endpoint theorem, keep the actual U(4) product measure, chronological
circuit, endpoint operators, trace normalization, and explicit front window
visible. Its conditional-mean identity, propagation, positive local variance,
and gate count are proved ingredients; do not replace them with assumptions.

For simulation changes, preserve the same actual circuit, retained eye, and
sampler across accuracy and cost statements. The final probability is joint
over the Haar input and the conditional sampler kernel. The physical bias,
tail estimates, full-covariance sampler law, compressed update formulas, and
support bounds are proved ingredients. Keep the infinite-temperature and
critical-depth scope explicit. Explain the scalar-arithmetic cost convention
and distinguish the counted loops from preprocessing and bit complexity.
See the [simulation guide](docs/results/03-classical-simulation.md) and
[independent review](docs/reviews/simulation.md).

Follow the [reproduction guide](docs/verification/README.md). Before submitting proof
changes, run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

Include the verification result and checked revision in the pull request.
Keep the pinned toolchain and dependencies unless upgrading them is the purpose
of the change; document and verify an upgrade separately. For documentation-only
changes, check links, commands, and consistency with the formal statements,
and state which checks were performed.

New claims about graph-distance speeds, arbitrary varying-count Haar histories,
stronger Haar-average estimates, design convergence, or quantum advantage need their own
proofs and scope updates. Concrete support propagation, active-count bounds,
and the explicit local Haar coefficient are now proved.
Keep inactive gates in the full circuit history even when they cancel from a
single local observable. A successful build checks the formal proof;
mathematical review must also establish correspondence with the intended claim
in the paper.

---

**Related:** [Review guide](REVIEW.md) · [Assumptions and correspondence](docs/reviews/assumptions.md) · [Reproduce the checks](docs/verification/README.md)
