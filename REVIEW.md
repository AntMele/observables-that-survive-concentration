# Notes for coauthor review

The entry point is [`Fluctuations/Main.lean`](Fluctuations/Main.lean).

## The four final results

| Declaration | Statement |
| --- | --- |
| `transition_window` | Arbitrary nonnegative mean gap `Δ`; selects one depth and proves the quantitative bound for every later offset. |
| `theorem_VI_14` | Mean gap `1/2`; uniform lower bound for offsets `r ≤ R`, with any upper bound `P` on the transition width. |
| `theorem_VI_14_interval` | Explicit interval of `R+1` consecutive depths, its location, and the variance lower bound at every depth in it. |
| `theorem_VI_14_family` | An actual polynomial bounds the window widths; one positive lower-bound constant is chosen before quantifying over system size `n`. |

## Assumptions to inspect

- `complexVariance` is `E[‖F - E[F]‖²]`, matching complex-valued OTOCs.
- `LocalReverseVariance` uses mathlib's conditional expectation. It states
  `η ‖E[F_(d+1) | G_d] - F_d‖² ≤ E[‖F_(d+1) - E[F_(d+1) | G_d]‖² | G_d]`
  almost everywhere.
- `η` is positive and uniform in depth. In the family result it is also
  independent of `n`.
- The endpoint mean gap is assumed. The Haar/design/light-cone derivation of
  that gap is outside this formalization.
- Square-integrability and the inclusion of each conditioning sigma-algebra
  in the ambient sigma-algebra are explicit.
- The physical OTOC formula, circuit construction, and proofs that a particular
  ensemble satisfies the two substantive inputs are not formalized here.

Both slope-to-variance and forward persistence are proved from these inputs.
They are only premises of the intermediate deterministic sequence lemma, not
of the final probabilistic theorems.

## Reproduce the check

Install Lean through Elan, then run from the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

`lean-toolchain` selects Lean 4.24.0. `lake-manifest.json` pins mathlib and its
transitive dependencies. The script builds the project, prints the final
statements, and rejects any audited axiom outside `propext`, `Classical.choice`,
and `Quot.sound`. GitHub Actions performs the same check.

The original local verification output is saved in
[`docs/verification.txt`](docs/verification.txt). A fresh successful CI run is
the check of the current repository revision.

## Useful review questions

1. Do the formal assumptions match the intended local reverse-variance and mean
   gap inputs of the physical argument?
2. Does the chosen conditioning information represent the depth-`d` circuit?
3. Is a common positive `η` available over the depths and system sizes needed?
4. Do the endpoint definitions agree with `a = d_lc` and `b = d_mc`?
5. Are changes to the manuscript's theorem numbering or constants reflected in
   the paper mapping?
