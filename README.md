# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

A Lean 4 formalization of the variance mechanism behind observable fluctuations
in local random quantum circuits.

When the ensemble mean of a fixed-order out-of-time-order correlator (OTOC)
changes over a transition window, a local reverse-variance condition forces a
variance lower bound. The fluctuation persists over consecutive later depths.
This repository formalizes that implication: Theorem VI.14 of
*Large fluctuations of OTOCs in random circuits* and the general mean-gap
version in Remark VI.15.

The mean change and local reverse-variance condition are explicit hypotheses.
The proof applies to complex random variables on arbitrary probability spaces,
including continuous distributions.

**Verified:** all project modules compile with Lean 4.24.0. The final theorem
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorry` or additional axioms. See `docs/verification.txt` for the checked
statements and full audit output.

## Main result

Write `F d` for the depth-`d` observable, `a = d_lc`, `b = d_mc`,
`W = b - a`, and `κ = η / (1 + η)`. Assume:

1. Every `F d` is square-integrable on a probability space.
2. `a < b`, and `‖E[F b] - E[F a]‖ ≥ Δ ≥ 0`.
3. At each depth, `G d` is a sub-sigma-algebra of the ambient sigma-algebra.
   With `M d = E[F (d+1) | G d]`, the following holds almost everywhere,
   with the **same** constant `η > 0`:
   `E[‖F (d+1) - M d‖² | G d] ≥ η * ‖M d - F d‖²`.

There is a depth `a < d_star ≤ b` such that, for every natural number `r`,

```text
Var(F (d_star + r)) ≥ η * κ^r * Δ² / W².
```

The variance here is the paper's **complex variance**
`E[‖F - E[F]‖²]`, not the square without complex conjugation.

Taking `Δ = 1/2`, `r ≤ R`, and `W ≤ P` gives the paper's uniform bound

```text
Var(F (d_star + r)) ≥ η * κ^R / (4 * P²).
```

The interval is contained in `{a+1, ..., b+R}` and has exactly `R+1`
consecutive depths. The family theorem takes an actual real polynomial `p`
and produces a positive constant independent of `n`, giving the explicit
inverse-polynomial bound `c / (p.eval n)²` for every sufficiently large `n`.

## What is proved and what is assumed

The formal proof includes complex total variance, the squared-mean Jensen bound,
telescoping and selection of a large mean increment, slope-to-variance,
completion of the square, forward persistence, iteration, the uniform interval
bound, and the polynomial-family quantifiers. In particular, **slope-to-variance
and forward persistence are proved; they are not additional assumptions**.

The physical construction of the circuit probability space and the matrix
formula for OTOCs are not formalized here. An observable is supplied as a complex
square-integrable process. The mean-change hypothesis replaces the
Haar/design/light-cone argument. The local reverse-variance hypothesis
is stated using mathlib's actual conditional expectation. Verifying that a
particular gate ensemble satisfies these hypotheses is outside this proof.

Square-integrability is the standard technical condition for these identities;
measurable bounded OTOCs satisfy it. The proof is stronger than the circuit
application in one respect: it does not need adaptation of `F d` or nesting of
`G d`, once the displayed conditional inequality is assumed.

The common `η` must be uniform across the relevant depths and, for the family
result, across system sizes. A different constant at each depth without a common
positive lower bound would not give the stated result. This is explicit in the
paper's Lemma VI.13 and is made explicit in the formal theorem.

## Files

- `Fluctuations/Probability.lean`: complex variance, total variance, Jensen,
  the precise local condition, and slope-to-variance.
- `Fluctuations/WeightedVariance.lean`: mean-square minimization, the weighted
  inequality, and forward persistence (Lemma VI.13).
- `Fluctuations/Window.lean`: deterministic telescoping and propagation.
- `Fluctuations/Main.lean`: `transition_window` (arbitrary mean gap),
  `theorem_VI_14` (the explicit uniform bound), `theorem_VI_14_interval`
  (the interval including its cardinality and location), and
  `theorem_VI_14_family` (the polynomial-family quantifiers).
- `scripts/Audit.lean`: displays theorem types and kernel axiom dependencies.
- `docs/paper-mapping.md`: correspondence with the paper and source fingerprints.

## Reproduce

The toolchain is Lean **4.24.0**, with mathlib **v4.24.0** at commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Dependencies are locked by
`lake-manifest.json`.

With Lean/Elan installed, from this directory:

```sh
lake exe cache get
bash scripts/check.sh
```

An existing installation in a neighboring `Single-copySTABLEARNING` project
can also be reused without changing it or downloading anything:

```sh
bash scripts/check-local.sh
```

`SHARED_LEAN_PROJECT=/path/to/another/project` overrides that location. The local
script invokes the pinned Lean binary directly and uses the existing mathlib
compiled libraries read-only. It writes only this project's compiled files.

The verification script builds the library and checks the nine audited theorem
dependencies against an allowlist containing only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. It fails on proof holes or additional axioms.
GitHub Actions runs the same verification on pushes and pull requests.

## Reading and contributing

Start with [the main theorem](Fluctuations/Main.lean) and the
[paper-to-code correspondence](docs/paper-mapping.md). For coauthor review,
[REVIEW.md](REVIEW.md) records the assumptions and suggested checks.

Changes to a theorem statement should update its paper mapping and the scope
notes above. Run `bash scripts/check.sh` before proposing a change. A successful
build certifies the formal statement; comparison with the intended physical
statement remains part of mathematical review.

The current formalization establishes an inverse-polynomial variance lower
bound conditional on the stated inputs. It does not establish a computational
quantum-advantage claim.

This is a private research repository. Sharing its URL does not grant access;
coauthors need a GitHub collaborator invitation.
