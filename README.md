# Towards verifiable quantum advantage with random circuits: Observables that survive concentration

[![Lean verification](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)

**Lean 4 companion to the variance lower bound in Theorem VI.14.**

The strongest result treats full Haar-gate layers with a fixed number of active
gates and arbitrarily many inactive gates. It proves the local reverse-variance
bound, cancels inactive gates under explicit commutation certificates, and
derives the required half-unit mean gap from early-time commutation and two
quarter-unit mean estimates. The observable is the actual matrix
out-of-time-order correlator (OTOC).

The general probability theorem remains available for other ensembles, with
mean change and local reverse variance supplied as hypotheses.

## Start here

For a first reading alongside the paper, follow the
[paper-to-code map](docs/paper-mapping.md), the
[local reverse-variance argument](docs/guide.md#why-local-reverse-variance-follows),
and the [full-layer circuit theorem](Fluctuations/ActiveHaarCircuit.lean).
Then check the [scope limits](docs/guide.md#what-still-connects-this-model-to-the-paper)
and [reproduce the verification](docs/reproduce.md).

| If you want to… | Read |
| --- | --- |
| Understand the mathematics | [Guide](docs/guide.md) |
| Inspect the strongest circuit theorem | [ActiveHaarCircuit.lean](Fluctuations/ActiveHaarCircuit.lean) |
| Use the theorem for another ensemble | [Main.lean](Fluctuations/Main.lean) |
| Compare with the manuscript | [Paper-to-code map](docs/paper-mapping.md) and [review checklist](REVIEW.md) |
| Check or extend the proof | [Reproduction](docs/reproduce.md) and [contributing](CONTRIBUTING.md) |

## The full-layer result

Fix the OTOC order $k$ and $m$ active gates per layer. Each layer also contains
$q$ inactive gates, where $q$ may grow with system size. All new gates are
independent normalized Haar SU(4) gates inserted by unital complex star-algebra
homomorphisms. Write the layer as $W_d=J_dA_d$, with inactive block $J_d$ and
active block $A_d$, and set $U_{d+1}=W_dU_d$.
The counts $m,q$ are fixed across depths of a given process; the embeddings
may change with depth.

Every inactive gate must commute with $B$. This explicit certificate gives
$J_d^\dagger BJ_d=B$, so only the fresh active gates enter the local OTOC.
Inactive gates remain in the full circuit history and may matter at later depths.
The observable is

```math
F_d=\mathrm{Tr}\!\left[\rho\left(U_d^\dagger B U_d M\right)^{2k}\right].
```

`activeHaarCircuit_theorem_of_moment_control` uses **one $\eta(m,k)>0$,
independent of $q$, global dimension, embeddings, and observable matrices**. Its inputs
are the inactive-gate certificate, $a<b$, a width bound $b-a\leq P$, and:

- $\mathrm{Tr}(\rho)=1$, $B^2=M^2=I$;
- at depth $a$, $U_a^\dagger BU_a$ commutes with $M$ for every history;
- a reference mean $h$ satisfies $|\mathbb EF_b-h|\leq1/4$ and $|h|\leq1/4$.

Lean derives $\mathbb EF_a=1$ and $|\mathbb EF_b-\mathbb EF_a|\geq1/2$.
For any chosen $R\in\mathbb N$, some $a<d_*\leq b$ then satisfies

```math
\mathrm{Var}(F_{d_*+r})\geq
\frac{\eta}{4P^2}\left(\frac{\eta}{1+\eta}\right)^R
\qquad(0\leq r\leq R).
```

Variance means $\mathbb E|F-\mathbb EF|^2$. With $P=p(n)$ and fixed **$m,k,R$**,
the prefactor is independent of system size and the number of inactive gates.
The theorem `activeHaarCircuit_theorem_VI_14` gives the same conclusion when the
half-unit gap is supplied directly. [HaarCircuit.lean](Fluctuations/HaarCircuit.lean)
contains the earlier model with only active gates; [Main.lean](Fluctuations/Main.lean)
contains the general probability, interval, and polynomial-family results.

## Scope

| Proved in Lean | Inputs or remaining work |
| --- | --- |
| Actual SU(4), normalized product Haar sampling, matrix OTOCs, and a uniform local variance constant | The embeddings and the active/inactive decomposition |
| Inactive-unitary cancellation; regrouping interleaved lists under cross-commutation; commutation on separate tensor factors | Graph-based support propagation, a light-cone construction, and a bound on the active-gate count |
| Early OTOC equals one for commuting involutions; a half-gap follows from the two mean estimates | The early commutation certificate, moment-control error, reference-mean estimate, and width bound |
| Full-layer variance bound with a constant independent of $q$ and global dimension | The sharper numerical Haar constant $4^{-8km}$ and computational quantum advantage |

The reference mean can be chosen to be a Haar mean, but the theorem does not
calculate that mean or prove convergence to it. The [guide](docs/guide.md)
explains exactly how the algebraic certificates and statistical inputs enter.
Identifying an arbitrary architecture's gate coordinates with the grouped
product sampling law also remains an application step.

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
`propext`, `Classical.choice`, and `Quot.sound`. The full local check passed for
the new extension: all 15 library modules and the top-level import compiled,
and all 42 audited declarations passed with no warnings or errors. The
[earlier Haar-model CI run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36327000675)
passed for revision `949e8226e28dd3c87b98cd9b123d5aa1c2ab95a3`.
That run predates the active/inactive-layer and mean-change extensions. See the
[reproduction guide](docs/reproduce.md) for verification status and instructions
to check the current source.

## Source route

- [ActiveHaarCircuit.lean](Fluctuations/ActiveHaarCircuit.lean): full-layer theorem, with either a supplied gap or the moment-control inputs.
- [SpatialSupport.lean](Fluctuations/SpatialSupport.lean): cancellation, interleaved products, and tensor-factor commutation.
- [MeanChange.lean](Fluctuations/MeanChange.lean): commuting-involution OTOCs and the quantitative mean-gap argument.
- [HaarSU4.lean](Fluctuations/HaarSU4.lean): the actual gate group, measure, independence, and coordinates.
- [LocalPolynomial.lean](Fluctuations/LocalPolynomial.lean): finite feature spaces and matrix OTOC membership.
- [FiniteDimensionalVariance.lean](Fluctuations/FiniteDimensionalVariance.lean): reverse variance on a finite-dimensional continuous-function space under a full-support probability law.
- [HaarLocalVariance.lean](Fluctuations/HaarLocalVariance.lean): a uniform Haar constant and the local and conditional inequalities.
- [QubitEmbedding.lean](Fluctuations/QubitEmbedding.lean): $A\mapsto A\otimes I$ as a unital star-algebra homomorphism.
- [ProductVariance.lean](Fluctuations/ProductVariance.lean), [HaarProcess.lean](Fluctuations/HaarProcess.lean), and [HaarCircuit.lean](Fluctuations/HaarCircuit.lean): conditioning, independent histories, and the concrete circuit theorem.
- [Probability.lean](Fluctuations/Probability.lean), [WeightedVariance.lean](Fluctuations/WeightedVariance.lean), [Window.lean](Fluctuations/Window.lean), and [Main.lean](Fluctuations/Main.lean): the general fluctuation argument.

When citing the formalization, record the repository revision and the paper
version. The [paper map](docs/paper-mapping.md) records the manuscript fingerprints.
