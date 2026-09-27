# Paper-to-code map

[Overview](../README.md) · [Mathematical guide](guide.md) · [Reproduction](reproduce.md)

Companion to *Towards verifiable quantum advantage with random circuits:
Observables that survive concentration*. The manuscript snapshot below contains
Theorem VI.14 on PDF pages 27–28 and persistence Lemma VI.13 on page 26. Its PDF
filename uses the earlier title *Large fluctuations of OTOCs in random circuits*.

The stable theorem label is `thm:fixed-k-transition-window-fluctuation-bound`.
Match labels and mathematical statements when the manuscript numbering changes.

## General fluctuation argument

| Paper statement | Formal component | Status |
| --- | --- | --- |
| Complex variance convention | `complexVariance` in [Probability.lean](../Fluctuations/Probability.lean) | Defined using the squared complex norm |
| Eq. (107), local reverse variance | `LocalReverseVariance` in [Probability.lean](../Fluctuations/Probability.lean) | Hypothesis for the general theorem; proved for the modeled Haar blocks below |
| Eqs. (109)–(110), total variance and integrated local estimate | `complex_total_variance`, `localReverseVariance_integrated` in [Probability.lean](../Fluctuations/Probability.lean) | Proved |
| Eq. (111), weighted inequality | `weighted_norm_sq`, `weighted_variance_comparison` in [WeightedVariance.lean](../Fluctuations/WeightedVariance.lean) | Proved |
| Lemma VI.13 / Eq. (108) | `forward_persistence` in [WeightedVariance.lean](../Fluctuations/WeightedVariance.lean) | Proved |
| Eq. (114), half-unit mean change | `hchange` in [Main.lean](../Fluctuations/Main.lean), endpoint-gap premise in [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Assumed in both routes |
| Eqs. (115)–(118), large increment and propagation | [Window.lean](../Fluctuations/Window.lean) and [Main.lean](../Fluctuations/Main.lean) | Proved |
| Eq. (119) and Theorem VI.14 | `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family` in [Main.lean](../Fluctuations/Main.lean) | General bound, interval, and polynomial family proved from the two inputs |
| Remark VI.15, arbitrary mean gap | `transition_window` in [Main.lean](../Fluctuations/Main.lean) | Proved |

## Haar-gate extension

| Manuscript ingredient | Formal component | Exact coverage |
| --- | --- | --- |
| Finite-dimensional reverse variance, label `lem:finite-dimensional-reverse-variance` | `finiteDimensional_reverseVariance` in [FiniteDimensionalVariance.lean](../Fluctuations/FiniteDimensionalVariance.lean) | Compact-space, full-support specialization; uniform over a finite-dimensional continuous-function space |
| Local matrix OTOC, label `eq:conditional-local-otoc-function` | `haarLocalOTOC_apply` in [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | Actual trace formula with arbitrary finite ambient matrices and linear gate embeddings |
| Finite local function space, labels `eq:FBk-definition`, `eq:fV-in-FBk` | `matrixBlockOTOC_mem` in [LocalPolynomial.lean](../Fluctuations/LocalPolynomial.lean) | Alternative raw gate-entry/conjugate span of total degree $4mk$, independent of ambient dimension and matrix coefficients |
| Independent Haar two-qubit gates | [HaarSU4.lean](../Fluctuations/HaarSU4.lean) | Actual compact SU(4), normalized product Haar law, and coordinate independence |
| Physical spectator insertion | `qubitEmbedding` in [QubitEmbedding.lean](../Fluctuations/QubitEmbedding.lean) | $A\mapsto A\otimes I$ is a unital complex star-algebra homomorphism and preserves gate unitarity |
| Desired local bound, label `eq:desired-local-reverse-variance` | `haarLocalOTOC_reverseVariance_identity` in [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | Positive constant depending only on $m,k$; the identity value is the previous OTOC |
| Conditional local inequality | `product_condExp`, `product_localReverseVariance` in [ProductVariance.lean](../Fluctuations/ProductVariance.lean); `haarLocalOTOC_conditional_reverseVariance` in [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | Proved under an independent Haar block and a continuous earlier circuit on a compact history space |
| Repeated independent blocks | [HaarProcess.lean](../Fluctuations/HaarProcess.lean) and [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Product histories and the actual recursion $U_{d+1}=W_dU_d$ |
| Theorem VI.14 for that model | `haarCircuit_theorem_VI_14` in [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Local reverse variance discharged; endpoint gap and width bound remain inputs |

The raw monomial space is deliberately larger than the refined representation
used for the paper's explicit estimate. The project proves existence of a
uniform positive constant; it does **not** prove the numerical value
$4^{-8km}$ from `eq:two-qubit-haar-explicit-constant`.

## Scope and remaining correspondence

The general theorem in `Main.lean` applies to arbitrary probability spaces and
complex square-integrable processes. Its mean-change and local reverse-variance
inputs are explicit theorem parameters. Slope-to-variance and persistence are
proved from the latter; neither is an additional assumption of the final result.

The Haar-circuit theorem instead constructs the observable and sampling law.
For fixed $m,k$, its positive constant is chosen before the global dimension,
embeddings, observable matrices, and depth window. Continuity, square-integrability,
feature membership, and the local inequality are derived for this model.
The usual physical matrix choices are included, although positivity or Pauli
conditions are not needed for the variance implication.

A modeled step contains exactly $m$ new independent gates. The reduction from a
general spatial circuit to a fixed-size active block, including light-cone and
inactive-gate cancellation arguments, remains outside the formalization. So do
design/mixing arguments for the endpoint mean gap and width, the full
stabilizing-element/open-support criteria for other ensembles, the sharper Haar
constant, and computational quantum advantage.

## Manuscript provenance

The following files identify the draft inspected. They were not modified and
are not distributed in this repository. A public paper URL or DOI can be added
when available.

```text
MAIN (24).tex
SHA-256: ef25202b80354f0142730e2e1dcb47661cf517dcb388f28e2e80630b324dbb6a

Large_fluctuations_of_OTOCs_in_random_circuits (79).pdf
SHA-256: 9f653514f023afd3ca37d2a05693fb8ca15749d7a870273852d772c4ea9f5a18
```

When discussing the mathematics, cite the paper. For the machine-checked proof,
also record the exact repository commit and declaration, such as
`Fluctuations.haarCircuit_theorem_VI_14` or
`Fluctuations.theorem_VI_14_family`. No publication identifier is inferred from
the draft filename.
