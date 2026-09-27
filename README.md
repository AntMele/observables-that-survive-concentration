# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

[![Lean verification](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)

**Lean 4 companion to the variance lower bound in Theorem VI.14.**

The project has two results. The general theorem converts a mean change and a
local reverse-variance condition into persistent fluctuations. The Haar-circuit
extension constructs actual matrix out-of-time-order correlators (OTOCs) from
independent SU(4) gates and
**proves the local reverse-variance condition** for that model. Its final
variance theorem retains the mean-gap and transition-width assumptions.

## Start here

For a first reading alongside the paper, follow the
[paper-to-code map](docs/paper-mapping.md), the
[local reverse-variance argument](docs/guide.md#why-local-reverse-variance-follows),
and the [Haar-circuit theorem](Fluctuations/HaarCircuit.lean).
Then check the [scope limits](docs/guide.md#what-still-connects-this-model-to-the-paper)
and [reproduce the verification](docs/reproduce.md).

| If you want to… | Read |
| --- | --- |
| Understand the mathematics | [Guide](docs/guide.md) |
| Inspect the concrete Haar-circuit theorem | [HaarCircuit.lean](Fluctuations/HaarCircuit.lean) |
| Use the theorem for another ensemble | [Main.lean](Fluctuations/Main.lean) |
| Compare with the manuscript | [Paper-to-code map](docs/paper-mapping.md) and [review checklist](REVIEW.md) |
| Check or extend the proof | [Reproduction](docs/reproduce.md) and [contributing](CONTRIBUTING.md) |

## The Haar-circuit result

Fix the OTOC order $k$ and a number $m$ of new gates per step. Each step samples
$m$ independent normalized Haar SU(4) gates, embeds them by unital complex
star-algebra homomorphisms, and multiplies their ordered block onto the previous
circuit. The observable is the actual matrix trace

```math
F_d=\mathrm{Tr}\!\left[\rho\left(U_d^\dagger B U_d M\right)^{2k}\right].
```

`haarCircuit_theorem_VI_14` chooses **one $\eta(m,k)>0$ before the global matrix
dimension, gate embeddings, state/observable matrices, and depth interval**.
If $a<b$, the endpoint means differ by at least $1/2$, and $b-a\leq P$, then
for any chosen $R\in\mathbb N$, some $a<d_*\leq b$ satisfies

```math
\mathrm{Var}(F_{d_*+r})\geq
\frac{\eta}{4P^2}\left(\frac{\eta}{1+\eta}\right)^R
\qquad(0\leq r\leq R).
```

Variance means $\mathbb E|F-\mathbb EF|^2$. Taking $P=p(n)$ gives an
inverse-polynomial bound with a common prefactor when **$m,k,R$ are fixed**.
The proof establishes the existence of $\eta$; it does not establish the
paper's numerical choice $4^{-8km}$.

The general results in [Main.lean](Fluctuations/Main.lean) also cover arbitrary
complex square-integrable processes, arbitrary mean gaps, explicit interval
cardinality and location, and polynomial families. For those general ensembles,
local reverse variance remains a hypothesis.

## Scope

| Formalized | Inputs or remaining work |
| --- | --- |
| Actual compact SU(4), normalized Haar measure, and independent gate sampling | The endpoint mean gap and a transition-width bound |
| Raw gate-entry polynomial space containing the matrix OTOC, uniformly in system dimension | Deriving the gap from designs, mixing, or Haar-average convergence |
| A positive uniform local constant, including the conditional inequality | The sharper explicit constant $4^{-8km}$ |
| Independent circuit histories and the final Haar-circuit variance bound | Reducing a general spatial architecture to a fixed-size active block by light-cone cancellation |
| A genuine two-qubit tensor-with-identity embedding | Computational quantum advantage and other claims in the paper |

The concrete theorem models **exactly $m$ independent gates per step**. It does
not by itself identify those steps with layers of an arbitrary growing spatial
circuit. See the [guide](docs/guide.md) for this boundary and the proof route.

## Run the verification

With [Lean/Elan](https://lean-lang.org/install/), Git, Bash, and Python 3 installed:

```sh
git clone https://github.com/AntMele/observables-that-survive-concentration.git
cd observables-that-survive-concentration
lake exe cache get
bash scripts/check.sh
```

Lean **4.24.0** and mathlib **v4.24.0** are pinned. The check builds the library
and audits all listed declarations and their transitive dependencies against
`propext`, `Classical.choice`, and `Quot.sound`. The
[Haar-extension CI run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36327000675)
passed for revision `949e8226e28dd3c87b98cd9b123d5aa1c2ab95a3`.
See the [reproduction guide](docs/reproduce.md) for that verification record
and instructions to check another revision.

## Source route

- [HaarSU4.lean](Fluctuations/HaarSU4.lean): the actual gate group, measure, independence, and coordinates.
- [LocalPolynomial.lean](Fluctuations/LocalPolynomial.lean): finite feature spaces and matrix OTOC membership.
- [FiniteDimensionalVariance.lean](Fluctuations/FiniteDimensionalVariance.lean): reverse variance on a finite-dimensional continuous-function space under a full-support probability law.
- [HaarLocalVariance.lean](Fluctuations/HaarLocalVariance.lean): a uniform Haar constant and the local and conditional inequalities.
- [QubitEmbedding.lean](Fluctuations/QubitEmbedding.lean): $A\mapsto A\otimes I$ as a unital star-algebra homomorphism.
- [ProductVariance.lean](Fluctuations/ProductVariance.lean), [HaarProcess.lean](Fluctuations/HaarProcess.lean), and [HaarCircuit.lean](Fluctuations/HaarCircuit.lean): conditioning, independent histories, and the concrete circuit theorem.
- [Probability.lean](Fluctuations/Probability.lean), [WeightedVariance.lean](Fluctuations/WeightedVariance.lean), [Window.lean](Fluctuations/Window.lean), and [Main.lean](Fluctuations/Main.lean): the general fluctuation argument.

When citing the formalization, record the repository revision and the paper
version. The [paper map](docs/paper-mapping.md) records the manuscript fingerprints.
