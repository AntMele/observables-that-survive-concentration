# Contributing

Changes should make the formal statement and its relationship to the paper
easier to inspect. Start with [`Fluctuations/Main.lean`](Fluctuations/Main.lean),
the [paper mapping](docs/paper-mapping.md), and the
[review notes](REVIEW.md).

For a change to a theorem, explain the mathematical statement before and after
the change. Identify any change to assumptions, constants, quantifier order,
depth ranges, or the manuscript statement it represents. Keep the paper mapping
and relevant documentation consistent with the final Lean statement. In
particular, preserve the distinction between the two assumed scientific inputs
and the variance bounds proved from them.

Keep proof changes focused. Do not add `sorry`, `admit`, or custom axioms to
complete a proof. The nine audited results and their transitive dependencies
must use only `propext`, `Classical.choice`, and `Quot.sound`. A new public result
should have its statement documented and its axiom audit added explicitly to
both `scripts/Audit.lean` and the expected declarations in
`scripts/check-axioms.py`.

Follow the [reproduction guide](docs/reproduce.md). Before submitting a change,
run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

Include the verification result and the revision checked in the pull request.
Keep the committed Lean toolchain and dependency revisions unless the change
specifically upgrades them; document and verify any such upgrade. For a
documentation-only change, check links, commands, and consistency with the Lean
statements, and say which checks were performed.

A successful build checks the formal proof. Review must also establish that
the formal hypotheses and conclusion match the intended claim in the paper.
