# Classical simulation of the endpoint OTOC

[Home](../../README.md) / [Reader guide](../README.md) / Classical simulation

This page explains the formalization of the paper's theorem
`thm:endpoint-sim-otoc1-runtime`. The assembled statements are
[`otoc1_subexponential_simulation` and
`otoc1_subexponential_simulation_inversePolynomial`](../../Fluctuations/Simulation.lean).
See the [independent review](../reviews/simulation.md) for an English translation
and comparison with the manuscript, and the [verification record](../verification/record.txt)
for the checked source revision.

## The statement and its scope

Take a positive multiple of six qubits, $n=6(s+1)$, and depth
$d=5n/3=10(s+1)$. The circuit is the open nearest-neighbor brickwork circuit,
starting with an odd layer, with independent Haar U(4) gates. The target is
the **infinite-temperature** first-order endpoint OTOC

```math
F_\infty(U)=2^{-n}\mathrm{Tr}[(U^\dagger Z_1UZ_n)^2].
```

For $0<\epsilon,\delta<1$, the algorithm retains a diffusive region of gates,
averages the other gates over Haar measure, and estimates that conditional
mean with independent samples. Its parameter choices are

```math
R=10\sqrt{\log\frac{400n^2}{3\epsilon\delta}},\qquad
N=\left\lceil8\epsilon^{-2}\log\frac4\delta\right\rceil.
```

The success statement is

```math
\Pr_{U,\,\mathrm{sampler}}\bigl[|\widetilde F-F_\infty(U)|\le\epsilon\bigr]
\ge1-\delta.
```

This probability includes **both** the random circuit and the algorithm's
randomness. It is not a guarantee for every fixed circuit. The sampler is
unbiased for the conditional Haar mean for every fixed realization of the
retained gates; the error between that mean and the original circuit is
controlled in probability over the Haar circuit.

The work bound counts scalar arithmetic (real or complex) in the manuscript's
arithmetic-operation model, with exact sampling from explicitly computed finite distributions:

```math
O\!\left(n^2\,2^{O(\sqrt{n\log(n/(\epsilon\delta))})}
\epsilon^{-2}\log(2/\delta)\right).
```

For $\epsilon=n^{-a}$ and $\delta=n^{-b}$ with fixed positive natural
exponents $a,b$, the combined formal theorem proves both this accuracy
guarantee at every allowed size and $\log(\mathrm{work})/n\to0$. The work
is bounded by $\mathrm{poly}(n)2^{O(\sqrt{n\log n})}$.
This is an arithmetic-model verification, not a bit-complexity bound or a
benchmark of an executable numerical implementation. Arbitrary input states,
higher OTOC orders, and worst-case circuits are outside this simulation claim.

## What the sampler does

Expand the evolved butterfly in the actual tensor Pauli basis. It has real
coefficients $c(P)$ satisfying $\sum_P c(P)^2=1$. Orthogonality of that basis
and the infinite-temperature trace give the exact, pointwise identity

```math
F_\infty(U)=\sum_P c(P)^2 f(P),\qquad
f(P)=\begin{cases}+1,&P_n\in\{I,Z\},\\-1,&P_n\in\{X,Y\}.\end{cases}
```

The algorithm maintains one coherent amplitude vector and classical Pauli
labels outside its coherent support. A retained gate applies its actual real
Pauli transfer matrix. At an averaged gate it computes the input-pair
marginal $q(a)=\sum_\alpha\psi(a,\alpha)^2$, samples $a$, samples the output
pair $b$ from the derived local Haar kernel, and retains the normalized
spectator vector $\psi(a,\cdot)/\sqrt{q(a)}$. The identity pair stays the
identity; every nonidentity input is uniform over the fifteen nonidentity
outputs. A zero-weight input uses a specified normalized default vector.

The correctness invariant is the **full covariance matrix**, including
off-diagonal spectator entries. This is needed when retained coherent gates
follow averaged gates. The proof does not assume that all intermediate
covariances are diagonal. The final Pauli string is sampled from the squared
stored amplitudes and its sign is returned.

## Why the approximation is accurate

Replacing one gate changes the OTOC by at most four times the square root of
the Pauli mass touching that gate, using either the forward butterfly or the
backward probe. The backward proof uses the literal reversed, inverted gate
word and normalized-trace symmetry. Haar invariance then gives the same
finite endpoint process, with the exact boundary and parity conventions.

An exact finite-binomial comparison proves

```math
p(u,v)\le\frac52\exp\!\left[-\frac{(5v-3u)_+^2}{200u}\right].
```

This proof uses the finite reflecting endpoint chain. It does not assume a
Gaussian approximation to the mean front. Summing the influences outside the
retained region bounds the error of the literal partial Haar integral by

```math
\mathbb E|F_\infty-\widehat F_R|
\le\frac{100}{3}n^2e^{-R^2/100}.
```

Markov's inequality bounds the circuit-averaging failure probability by
$\delta/2$. Hoeffding's inequality gives
$2e^{-N\epsilon^2/8}\le\delta/2$ for the Monte Carlo error. A genuine
probability kernel for the conditional sampler combines the two experiments
into one joint probability space.

## Why the work is subexponential

Each layer has at most $W\le2R\sqrt n+1$ retained gates. Disjoint gates may be
processed in a different order without changing the circuit or conditional
output law. Processing averaged gates first leaves at most $2W+2$ coherent
sites at a layer boundary and at most $2W+4$ during an update.

The compressed vector therefore has at most $4^{2W+4}$ real entries. The work
model counts the local transfer, marginalization, normalization, and final
readout loops. The full-space semantic formulas are proved equal to the
corresponding computations on the compressed array, including normalization
of every positive-probability branch. Its support invariant is proved along
those trajectories. Indexing and memory access are free in this arithmetic
model; the counter does not separately charge eye construction or parameter
preprocessing, and is not an instruction count for a compiled program.
Repeating the counted sampling procedure $N$ times gives an explicit
bound of the form

```math
180002(N+1)n^2\,4^{2\lceil2R\sqrt n+1\rceil+4}.
```

## Reading the code

| Step | Main source |
| --- | --- |
| Complete accuracy/work theorem and combined subexponential corollary | [Simulation.lean](../../Fluctuations/Simulation.lean) |
| Actual trace equals a Pauli sign average | [SimulationTrace.lean](../../Fluctuations/SimulationTrace.lean) |
| Normalized sampler, including zero-weight branches | [SimulationSampler.lean](../../Fluctuations/SimulationSampler.lean) |
| Full local Haar covariance and mixed-circuit correctness | [SimulationSamplerCovariance.lean](../../Fluctuations/SimulationSamplerCovariance.lean), [SimulationMixedCircuit.lean](../../Fluctuations/SimulationMixedCircuit.lean) |
| Exact conditional sign expectation | [SimulationMixedCircuitOTOC.lean](../../Fluctuations/SimulationMixedCircuitOTOC.lean) |
| Forward and backward gate perturbations | [SimulationLocalCoordinate.lean](../../Fluctuations/SimulationLocalCoordinate.lean), [SimulationBackwardInfluence.lean](../../Fluctuations/SimulationBackwardInfluence.lean) |
| Exact finite binomial and reflecting-chain tails | [SimulationTailBinomial.lean](../../Fluctuations/SimulationTailBinomial.lean), [SimulationEndpointTail.lean](../../Fluctuations/SimulationEndpointTail.lean) |
| Physical prefix/suffix and Haar expected touching mass | [SimulationPrefixBridge.lean](../../Fluctuations/SimulationPrefixBridge.lean), [SimulationTailReflection.lean](../../Fluctuations/SimulationTailReflection.lean), [SimulationExpectedTouch.lean](../../Fluctuations/SimulationExpectedTouch.lean) |
| Actual partial integration and telescoping error | [SimulationAveraging.lean](../../Fluctuations/SimulationAveraging.lean), [SimulationCircuitAverage.lean](../../Fluctuations/SimulationCircuitAverage.lean) |
| Finite output law and joint probability space | [SimulationSamplingProbability.lean](../../Fluctuations/SimulationSamplingProbability.lean), [SimulationSamplingKernel.lean](../../Fluctuations/SimulationSamplingKernel.lean), [SimulationJointProbability.lean](../../Fluctuations/SimulationJointProbability.lean) |
| Physical outside-first law equals the accuracy kernel | [SimulationPhysicalLaw.lean](../../Fluctuations/SimulationPhysicalLaw.lean) |
| Exact small-array update formulas and entry counts | [SimulationCompressedOperations.lean](../../Fluctuations/SimulationCompressedOperations.lean) |
| Physical gate coordinates, causal exclusions and complete eye bias | [SimulationGateCoordinates.lean](../../Fluctuations/SimulationGateCoordinates.lean), [SimulationEyeError.lean](../../Fluctuations/SimulationEyeError.lean) |
| Width, generated operation counts, subexponential limit | [SimulationWidth.lean](../../Fluctuations/SimulationWidth.lean), [SimulationGeometryCost.lean](../../Fluctuations/SimulationGeometryCost.lean), [SimulationAsymptotics.lean](../../Fluctuations/SimulationAsymptotics.lean) |

All objects above are definitions or proved statements. Intermediate lemmas
may expose assumptions that later physical-circuit lemmas discharge; the
final theorem is the place to inspect the remaining scientific assumptions.

---

**Next:** [Independent simulation review](../reviews/simulation.md) · [Endpoint fluctuations](endpoint-fluctuations.md) · [Reproduce the checks](../verification/README.md)
