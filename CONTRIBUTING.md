# Contributing

Start with the [OTOC(1) guide](docs/otoc1.md), [paper mapping](docs/paper-mapping.md),
and [review notes](REVIEW.md). The main entry points are
[OTOC1.lean](Fluctuations/OTOC1.lean) for the concrete endpoint theorem,
[SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean) for the spatial
Haar model and
[Main.lean](Fluctuations/Main.lean) for the general probability theorem.

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

Follow the [reproduction guide](docs/reproduce.md). Before submitting proof
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
