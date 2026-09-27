# Reproduce the Lean verification

[Repository overview](../README.md) · [Mathematical guide](guide.md) ·
[Paper-to-code map](paper-mapping.md)

This guide checks the formal statements in the repository, including the
variance lower bound corresponding to Theorem VI.14 and its concrete Haar SU(4)
extension. The general theorem assumes mean change and local reverse variance.
The Haar-circuit theorem proves the local condition for its fixed-size independent
gate blocks and retains the endpoint-gap and width assumptions. The
[paper mapping](paper-mapping.md) records the precise scope of each route.

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
Axiom audit passed for all 24 declarations: only propext, Classical.choice, and Quot.sound are allowed.
```

To read the statements and axiom reports again after a successful build:

```sh
lake env lean scripts/Audit.lean
```

This last command displays the audit; `bash scripts/check.sh` is the command
that also enforces the allowlist.

## Pinned versions


| Component | Version or revision | Recorded in |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.24.0` | [`lean-toolchain`](../lean-toolchain) |
| Mathlib | `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` | [`lakefile.toml`](../lakefile.toml), [`lake-manifest.json`](../lake-manifest.json) |
| Transitive packages | Exact Git revisions | [`lake-manifest.json`](../lake-manifest.json) |

Keep the committed toolchain and manifest when reproducing a result. Updating
dependencies is a separate change that requires a fresh verification run.

## What the axiom audit checks

[`scripts/Audit.lean`](../scripts/Audit.lean) displays definitions and theorem
types, then uses `#print axioms` on all listed public declarations. The current
24-declaration audit covers the original probability/window results and the new
finite-dimensional bound, actual Haar sampling, matrix polynomial membership,
physical embeddings, product conditioning, local Haar inequalities, history
processes, and concrete circuit theorem.

Each report includes the declaration's transitive axiom dependencies, including
those reached through supporting lemmas. The
[audit checker](../scripts/check-axioms.py) requires exactly the declared set of
reports and permits only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. It rejects `sorryAx`, any additional axiom, and missing or duplicate
reports. Explicit mathematical assumptions appear in the theorem statements;
they are not new global axioms.

The build checks all imported library modules. The axiom audit covers the
listed declarations and their dependencies; it does not automatically add
future, unrelated declarations. Reviewing the assumptions and model against
the paper remains a separate mathematical check.

## Recorded verification and current status

The [Haar-extension GitHub Actions run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36327000675)
passed for revision `949e8226e28dd3c87b98cd9b123d5aa1c2ab95a3`, including the
concrete circuit theorem and the enforced 24-declaration axiom audit. Its
verification job took **4 minutes 55 seconds**; the full run took
**5 minutes 14 seconds**. This is evidence for that exact source revision.

The current [local verification record](verification.txt) reports a successful
full source rebuild on **2026-09-27**, using `bash scripts/check-local.sh`, with
no warnings or errors. All twelve library modules and the top-level import
compiled, and the enforced 24-declaration axiom audit passed. This record covers
the Haar extension, including `haarCircuit_theorem_VI_14`.

For historical reference, the earlier [GitHub Actions run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36316565231)
passed for commit `4d4a4d4a1ec88d9c3618e887b54ca2be8c10e175` in
3 minutes 28 seconds. That earlier run covers the abstract-only version.
Check the
[workflow results](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)
for the revision you are reviewing, or run the commands above. A saved report
or an earlier green badge is not evidence for later source changes.

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
this project's compiled modules. It finishes with the same enforced
axiom check.

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
