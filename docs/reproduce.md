# Reproduce the Lean verification

[Repository overview](../README.md) · [Mathematical guide](guide.md) ·
[Paper-to-code map](paper-mapping.md)

This guide checks the formal statements in the repository, including the
variance lower bound corresponding to Theorem VI.14. The mean change and local
reverse-variance condition remain explicit hypotheses. A successful build
certifies the Lean statements under their stated assumptions; the
[paper mapping](paper-mapping.md) explains their correspondence with the paper.

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
Axiom audit passed for all 9 declarations: only propext, Classical.choice, and Quot.sound are allowed.
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

[`scripts/Audit.lean`](../scripts/Audit.lean) displays the variance definition,
the local reverse-variance condition, and the four final theorem types. It
also uses `#print axioms` on nine public declarations, all in the
`Fluctuations` namespace:

1. `complex_total_variance`
2. `norm_mean_sq_le_secondMoment`
3. `slope_to_variance`
4. `forward_persistence`
5. `exists_large_increment`
6. `transition_window`
7. `theorem_VI_14`
8. `theorem_VI_14_interval`
9. `theorem_VI_14_family`

Each report includes the declaration's transitive axiom dependencies, including
those reached through supporting lemmas. The
[audit checker](../scripts/check-axioms.py) requires exactly these nine reports
and permits only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. It rejects `sorryAx`, any additional axiom, and missing or
duplicate reports. The two scientific inputs are theorem parameters, so they
are visible in the theorem statements rather than appearing as extra axioms.

The build checks the library modules; the axiom audit specifically covers the
nine selected declarations and their dependencies. It does not automatically
add future, unrelated declarations to the audited set. Reviewing the formal
assumptions against the paper remains a separate mathematical check.

## Recorded verification and current status

The [recorded GitHub Actions run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36316565231)
passed for commit `4d4a4d4a1ec88d9c3618e887b54ca2be8c10e175` in
3 minutes 28 seconds. This is evidence for that revision. The
[verification workflow](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)
shows later runs; check the result for the revision you are reviewing, or run
the commands above locally.

The original local theorem statements and audit output are preserved in
[`verification.txt`](verification.txt). That file is a historical record,
not a live report of the current checkout.

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
this project's compiled modules. It finishes with the same nine-declaration
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
