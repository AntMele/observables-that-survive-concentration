# Contributing

Start with the [mathematical guide](docs/guide.md), [paper mapping](docs/paper-mapping.md),
and [review notes](REVIEW.md). The main entry points are
[ActiveHaarCircuit.lean](Fluctuations/ActiveHaarCircuit.lean) for the full-layer
Haar model and
[Main.lean](Fluctuations/Main.lean) for the general probability theorem.

For a theorem change, explain the mathematical statement before and after the
change. Identify any changes to assumptions, constants, quantifier order,
depth ranges, or manuscript correspondence. Keep the distinction between the
proved Haar local inequality and the assumed local condition for general
ensembles. In the strongest circuit theorem, the half-gap is derived from
explicit scalar mean estimates and the early commutation certificate. Track
those assumptions separately from the cancellation results in
[SpatialSupport.lean](Fluctuations/SpatialSupport.lean) and the mean identities
in [MeanChange.lean](Fluctuations/MeanChange.lean). A uniform Haar constant must
remain independent of the inactive-gate count $q$, ambient dimension,
embeddings, and observable matrices when $m,k$ are fixed.

Do not add `sorry`, `admit`, or custom axioms. All listed results and their
transitive dependencies must use only `propext`, `Classical.choice`, and
`Quot.sound`. Add new principal results explicitly to both
`scripts/Audit.lean` and the expected declaration list in
`scripts/check-axioms.py`. Update the library imports and offline build sequence
when adding a module.

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

Claims about graph light cones, support propagation, active-gate cardinality,
moment-control or Haar-average estimates, design convergence, explicit numerical
Haar constants, or quantum advantage need their own proofs and scope updates.
Keep inactive gates in the full circuit history even when they cancel from a
single local observable. A successful build checks the formal proof;
mathematical review must also establish correspondence with the intended claim
in the paper.
