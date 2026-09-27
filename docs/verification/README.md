# Reproduce the Lean verification

[Home](../../README.md) / [Reader guide](../README.md) / Verification

This guide builds the library and checks the transitive axiom dependencies
of the listed principal results. Start with the [OTOC(1) guide](../results/endpoint-fluctuations.md)
and [OTOC1.lean](../../Fluctuations/OTOC1.lean) for the endpoint variance theorem.
For classical simulation, start with the [simulation guide](../results/classical-simulation.md)
and [Simulation.lean](../../Fluctuations/Simulation.lean).
The [paper mapping](../reference/paper-map.md) distinguishes this unconditional
brickwork result from the general spatial theorem, whose design-convergence
and transition-width bounds remain external inputs.

## First-time setup

Install Lean and its version manager, Elan, using the
[official Lean installation guide](https://lean-lang.org/install/). The
[official manual installation instructions](https://lean-lang.org/install/manual/)
also cover terminal-based setup. Elan selects the version specified by this
project's `lean-toolchain` file.

The commands below require Git, Bash, Python 3, and `lake` on your terminal's
`PATH`. They can be run in a Bash-compatible terminal on macOS or Linux; on
Windows, use a Bash environment such as WSL. Reopen the terminal after
installation so the Lean tools are available.

## Clone and check

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

`lake exe cache get` downloads the precompiled Mathlib cache and avoids building
Mathlib from source. The verification script prints the Lean version, runs
`lake build`, evaluates `scripts/Audit.lean`, and checks the reported axiom
dependencies. It exits with an error if a build or audit step fails.

A successful run reports a completed build and ends with:

```text
Axiom audit passed for all N declarations: only propext, Classical.choice, and Quot.sound are allowed.
```

Here `N` is the declaration count in the committed audit list; the verification record gives the count for the checked source.

To read the statements and axiom reports again after a successful build:

```sh
lake env lean scripts/Audit.lean
```

This last command displays the audit; `bash scripts/check.sh` is the command
that also enforces the allowlist.

## Pinned versions


| Component | Version or revision | Recorded in |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.24.0` | [`lean-toolchain`](../../lean-toolchain) |
| Mathlib | `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` | [`lakefile.toml`](../../lakefile.toml), [`lake-manifest.json`](../../lake-manifest.json) |
| Transitive packages | Exact Git revisions | [`lake-manifest.json`](../../lake-manifest.json) |

Keep the committed toolchain and manifest when reproducing a result. Updating
dependencies is a separate change that requires a fresh verification run.

## What the axiom audit checks

[`scripts/Audit.lean`](../../scripts/Audit.lean) displays definitions and theorem
types, then uses `#print axioms` on all listed public declarations. These cover
the probability/window results, finite-dimensional bound, actual Haar sampling,
matrix polynomial membership, physical embeddings, product conditioning, local
Haar inequalities, and circuit histories. The general spatial coverage
includes inactive-gate cancellation, the mean-gap argument, actual global
Haar integration and its all-dimension bound. The endpoint coverage includes
actual U(4) Pauli moments, tensor embeddings, product conditioning, the
frozen-gate covariance reset, universal endpoint propagation, the conditional
mean, actual finite-depth mean, and the final variance and many-gate influence
results. The simulation audit additionally covers the exact coherent sampler,
compressed update formulas, physical output-law equality, forward/backward
touching tails, actual conditional-mean bias, joint probability kernel,
concentration, generated arithmetic counts, and combined accuracy/subexponential
statement. Inspect the committed list for the exact declarations being checked.

Each report includes the declaration's transitive axiom dependencies, including
those reached through supporting lemmas. The
[audit checker](../../scripts/check-axioms.py) requires exactly the declared set of
reports and permits only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. It rejects `sorryAx`, any additional axiom, and missing or duplicate
reports. Explicit mathematical assumptions appear in the theorem statements;
they are not new global axioms.

The portable build checks the library through Lake. The offline helper
uses [module-order.py](../../scripts/module-order.py) to discover every
`Fluctuations/*.lean` module and compile them in topological import order,
then checks the root module and runs the same enforced audit. This includes
supporting modules beyond the final theorem's direct imports.

The axiom audit covers its listed declarations and their dependencies; it
does not automatically add future, unrelated declarations. Reviewing the assumptions and model against
the paper remains a separate mathematical check.

## Verification evidence

The [verification record](record.txt) records the latest complete local
build, enforced axiom audit, and source fingerprints. Local development uses
the same pinned Lean and Mathlib versions through `scripts/check-local.sh`.
The standard `scripts/check.sh` route uses Lake and is run independently by
GitHub Actions.

Inspect the [workflow results](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)
for the exact commit under review. A saved report or an older green run does
not certify later source changes. The source fingerprint list makes it possible
to distinguish mathematical source revisions from later documentation edits.

## Optional developer shortcut: reuse an existing installation

For development with an existing compatible installation, the offline helper
can reuse Lean 4.24.0 and already compiled Mathlib libraries:

```sh
SHARED_LEAN_PROJECT=/absolute/path/to/existing/lean-project \
  bash scripts/check-local.sh
```

The existing project must contain the Lean binary at
`.elan/toolchains/leanprover--lean4---v4.24.0/bin/lean` and compatible compiled
packages under `.lake/packages/`. The helper reads those files and writes only
this project's compiled modules. It compiles all local modules in dependency
order and finishes with the same enforced axiom check.

If `SHARED_LEAN_PROJECT` is unset, the helper looks for a neighboring directory
named `Single-copySTABLEARNING`. This is an optional development convenience;
the clone-and-check procedure above is the standard reproduction route.

## Common setup issues

- **`lake` is not found:** finish the Elan installation and reopen the terminal.
- **Missing Mathlib build files:** run `lake exe cache get` from the repository
  root with the committed toolchain and manifest, then rerun the check.
- **Clone or Actions access is denied:** while the repository is private, sign
  in with a GitHub account that has access. Repository visibility does not
  affect the verification commands after the source has been obtained.

---

**Related:** [Verification record](record.txt) · [Review guide](../../REVIEW.md) · [Contributing](../../CONTRIBUTING.md)

## Documentation reorganization

The recorded build above predates the reader-focused documentation layout.
The record is preserved verbatim, so document paths inside it refer to that
verified revision. Use the [reader guide](../README.md) to find current result
guides, the [reviewer guide](../../REVIEW.md) for review notes, and the
[paper-to-code map](../reference/paper-map.md) for manuscript correspondence.
The reorganization changes documentation only; Lean sources, build scripts,
and pinned dependencies retain the recorded hashes.
