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
| Eq. (114), half-unit mean change | `mean_gap_one_half` in [MeanChange.lean](../Fluctuations/MeanChange.lean); assembled in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Derived from the early identity and two quarter-unit estimates in the strongest circuit theorem; supplied directly in the general theorem and gap-based circuit variants |
| Eqs. (115)–(118), large increment and propagation | [Window.lean](../Fluctuations/Window.lean) and [Main.lean](../Fluctuations/Main.lean) | Proved |
| Eq. (119) and Theorem VI.14 | `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family` in [Main.lean](../Fluctuations/Main.lean) | General bound, interval, and polynomial family proved from the two inputs |
| Remark VI.15, arbitrary mean gap | `transition_window` in [Main.lean](../Fluctuations/Main.lean) | Proved |

## Full-layer Haar extension

The strongest entry point is `activeHaarCircuit_theorem_of_moment_control` in
[ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean). The local Haar
lemma below supplies its variance input; the algebraic locality and mean-change
steps then connect that input to full circuit layers.

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
| Inactive-gate cancellation in the local function | `haarBlockMatrix_inactive_conjugation`, `embedded_su4_layer_eq_active` in [SpatialSupport.lean](../Fluctuations/SpatialSupport.lean) | Any number of inactive gates cancels under explicit commutation with $B$; an interleaved list additionally requires active/inactive cross-commutation |
| Disjoint-support commutation | `disjoint_tensor_factors_commute`, `qubitEmbedding_commutes_spectator` in [SpatialSupport.lean](../Fluctuations/SpatialSupport.lean) | Proved for separate tensor factors; graph support propagation and the active-gate count are not derived |
| Pre-light-cone identity, label `lem:pre-light-cone-identity` | `preLightCone_otoc_eq_one` in [MeanChange.lean](../Fluctuations/MeanChange.lean); `activeHaarCircuit_early_mean` in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Trace normalization, involutions, and early-time commutation imply the OTOC and early mean equal one; geometric commutation is an input |
| Late moment control, label `eq:otoc-test-moment-control`, and Haar mean estimate, label `prop:haar-otock-small` | `hcontrol`, `href` in `activeHaarCircuit_theorem_of_moment_control` | Scalar error and reference-mean bounds of $1/4$ are inputs; neither estimate nor design convergence is proved |
| Mean change, label `eq:fixed-k-proof-order-one-mean-change` | `mean_gap_one_half` in [MeanChange.lean](../Fluctuations/MeanChange.lean) | Derives the half-unit gap from early mean one and those two scalar bounds |
| Theorem VI.14 for full layers | `activeHaarCircuit_theorem_of_moment_control` in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Local reverse variance and the half-gap are derived; commutation certificates, scalar mean estimates, and width bound remain inputs |
| Variant with a supplied endpoint gap | `activeHaarCircuit_theorem_VI_14` in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Same full-layer variance bound without trace-normalization or involution assumptions |
| Earlier model with only active gates | `haarCircuit_theorem_VI_14` in [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Local reverse variance discharged; endpoint gap and width bound remain inputs |

The raw monomial space is deliberately larger than the refined representation
used for the paper's explicit estimate. The project proves existence of a
uniform positive constant; it does **not** prove the numerical value
$4^{-8km}$ from `eq:two-qubit-haar-explicit-constant`.

## Scope and remaining correspondence

The general theorem in `Main.lean` applies to arbitrary probability spaces and
complex square-integrable processes. Its mean-change and local reverse-variance
inputs are explicit theorem parameters. Slope-to-variance and persistence are
proved from the latter; neither is an additional assumption of the final result.

The full-layer Haar theorem constructs the observable and sampling law. Each
step contains $m$ active and $q$ inactive independent gates, ordered as inactive
times active; both counts are fixed across depths within each process.
The positive constant $\eta(m,k)$ is independent of $q$, global
dimension, embeddings, observable matrices, and depth. Inactive gates remain in
the full circuit history and may affect later depths. Continuity,
square-integrability, feature membership, and the local inequality are derived.

The strongest route also derives the early identity and half-gap. Its reference
mean is a supplied complex number: it can represent the paper's Haar mean, but
the theorem does not identify or compute a Haar average. The two scalar bounds,
early commutation, inactive-gate commutation, and transition width are explicit
inputs. Trace normalization and involutions are required for this route; the
supplied-gap variant allows arbitrary observable matrices.

The algebraic cancellation and tensor-factor commutation results do not supply
a graph light cone, support propagation, an active-gate cardinality bound, or
the geometric certificates for an arbitrary architecture. The number $q$ may
grow across system sizes while $m,k$ stay fixed. Design convergence, mixing
depths, the paper's Haar-mean estimate, full stabilizing-element/open-support
criteria for other ensembles, the sharper Haar constant, and computational
quantum advantage remain outside the proved claims.

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
`Fluctuations.activeHaarCircuit_theorem_of_moment_control` or
`Fluctuations.theorem_VI_14_family`. No publication identifier is inferred from
the draft filename.
