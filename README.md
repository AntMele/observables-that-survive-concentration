# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

[![Lean verification](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)

**Lean 4 companion to the paper: the variance lower bound in Theorem VI.14.**

This repository verifies the probabilistic argument that converts a change in
the ensemble mean of an observable into persistent circuit-to-circuit
fluctuations. The mean change and a uniform local reverse-variance condition
are explicit hypotheses. The proof covers complex-valued random variables on
arbitrary probability spaces.

## Start here

| If you want to… | Read |
| --- | --- |
| Understand the result without knowing Lean | [Mathematical guide](docs/guide.md) |
| Compare the formalization with the paper | [Paper-to-code map](docs/paper-mapping.md) |
| Find the exact theorem and its assumptions | [Main.lean](Fluctuations/Main.lean) and [review checklist](REVIEW.md) |
| Check the proof on your computer | [Reproduce the verification](docs/reproduce.md) |
| Extend the formalization | [Contributing](CONTRIBUTING.md) |

## The result

Let $F_d$ be the depth-$d$ observable, let $W=b-a>0$ be the transition width,
and suppose the endpoint means differ by at least $\Delta\geq0$. Under the
local reverse-variance condition with the same $\eta>0$ at every depth, there
is a depth $a<d_*\leq b$ such that

$$
\operatorname{Var}(F_{d_*+r})\;\geq\;
\eta\left(\frac{\eta}{1+\eta}\right)^r\frac{\Delta^2}{W^2}
\qquad(r\in\mathbb N).
$$

For the paper's mean gap $\Delta=1/2$ and width bound $W\leq p(n)$, every
depth in an interval of $R+1$ consecutive depths satisfies

$$
\operatorname{Var}(F_d)\;\geq\;\frac{c(\eta,R)}{p(n)^2},
\qquad c(\eta,R)=\frac{\eta}{4}
\left(\frac{\eta}{1+\eta}\right)^R>0.
$$

Here **$R$ is fixed as $n$ grows**, and **$\eta$ is uniform in depth and system
size**. The interval lies in $\{a+1,\ldots,b+R\}$. Variance means
$\mathbb E\lvert F-\mathbb EF\rvert^2$, including for complex observables.
See the [guide](docs/guide.md) for the precise assumptions and proof steps.

## Verification scope

| Proved in Lean | Explicit inputs or outside this formalization |
| --- | --- |
| Complex total variance, the squared-mean bound, and slope-to-variance | The endpoint mean gap |
| The weighted inequality and forward persistence | The local reverse-variance condition with a common positive constant |
| Selection of a large increment, iteration, interval size and location | Square-integrability and valid conditioning sigma-algebras |
| The inverse-polynomial family bound with a constant independent of $n$ | The circuit/OTOC construction and derivation of the two substantive inputs for an ensemble |

The final results contain no proof holes or additional axioms. The audit checks
their dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
This certifies the stated probabilistic implication; computational quantum
advantage and the paper's other results are outside its scope.

## Run the verification

With [Lean/Elan](https://lean-lang.org/install/) installed, together with Git,
Bash, and Python 3:

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

The project pins Lean **4.24.0** and mathlib **v4.24.0**, including transitive
dependency revisions. The check builds the library and audits nine key
declarations and their transitive axiom dependencies. See the
[reproduction guide](docs/reproduce.md) for expected output, verification
records, and troubleshooting.

## Source layout

| File | Role |
| --- | --- |
| [Fluctuations/Main.lean](Fluctuations/Main.lean) | Four final results: general mean gap, VI.14, its interval, and the polynomial family |
| [Fluctuations/Probability.lean](Fluctuations/Probability.lean) | Variance, conditional expectation, local condition, and slope-to-variance |
| [Fluctuations/WeightedVariance.lean](Fluctuations/WeightedVariance.lean) | Weighted comparison and one-step persistence |
| [Fluctuations/Window.lean](Fluctuations/Window.lean) | Deterministic telescoping, depth selection, and iteration |
| [scripts/Audit.lean](scripts/Audit.lean) | Printed definitions, theorem statements, and axiom dependencies |

To cite or compare a result, record the repository commit as well as the paper
version: theorem numbering can change. The [paper-to-code map](docs/paper-mapping.md)
identifies the theorem by its LaTeX label and records the manuscript fingerprints.
