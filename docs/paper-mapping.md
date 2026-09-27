# Paper-to-code map

[Overview](../README.md) · [Guide](guide.md) · [Reproduction](reproduce.md)

Companion to *Towards verifiable quantum advantage with random circuits:
Observables that survive concentration*. The inspected draft's main general
variance statement is Theorem VI.14, label
`thm:fixed-k-transition-window-fluctuation-bound`, on PDF pages 27–28.
Match labels and mathematical statements if numbering changes. Start with
the [OTOC(1) guide](otoc1.md) and [OTOC1.lean](../Fluctuations/OTOC1.lean)
for the first-order macroscopic-origin result, and the
[simulation guide](simulation.md) and [Simulation.lean](../Fluctuations/Simulation.lean)
for the infinite-temperature classical estimator.

## First-order endpoint OTOC

| Manuscript statement or ingredient | Lean declaration and source | Status |
| --- | --- | --- |
| Main theorem `thm:main-otoc1-variance-front-window`; SM `thm:endpoint-otoc1-variance-front-window` | `otoc1_endpoint_variance_lower`, [OTOC1.lean](../Fluctuations/OTOC1.lean) | Proved for actual Haar U(4) brickwork, every fixed `C ≥ 0`, and explicit sufficiently-large-size threshold |
| Macroscopic gate contributions and `eq:otoc1-size-S-front-window` | `otoc1_many_influential_gates`, `otoc1_endpoint_gate_influence`, [OTOC1.lean](../Fluctuations/OTOC1.lean) | Actual eye has $\Theta(n^{3/2})$ gates, each with conditional variance $\Omega(n^{-2})$ |
| Physical Haar-to-Pauli reduction | [PauliCircuitBridge.lean](../Fluctuations/PauliCircuitBridge.lean), [PauliFrozenCircuit.lean](../Fluctuations/PauliFrozenCircuit.lean) | Actual embedded U(4) matrices, product Haar integrals, and proved covariance reset after a fixed gate |
| `lem:otoc1-conditional-mean-even-gate` | `brickworkEndpointOTOC_conditional_mean`, [BrickworkEndpointOTOC.lean](../Fluctuations/BrickworkEndpointOTOC.lean) | Exact deviation $-(16/15)PF(A-4/5)$ for all physical interior even gates |
| `lem:otoc1-conditional-mean-variance` | `brickworkEndpointOTOC_gate_variance`, [BrickworkEndpointOTOC.lean](../Fluctuations/BrickworkEndpointOTOC.lean) | Exact coefficient $256/225$ and strictly positive actual local Haar variance |
| `lem:otoc1-PF-exact-front-window` | `endpointEye_factors_lower`, [EndpointFrontLower.lean](../Fluctuations/EndpointFrontLower.lean) | Actual Q-power factors bounded below through proved binomial estimates and eye geometry |
| `eq:otoc1-total-variance-from-one-gate-conditional-means` | [GateInfluence.lean](../Fluctuations/GateInfluence.lean), [CoordinateAverages.lean](../Fluctuations/CoordinateAverages.lean) | Conditional projections and their variance sum derived from the genuine finite product measure |
| Exact finite-depth quantum mean | `brickworkEndpointOTOC_haar_mean`, `brickworkEndpointOTOC_haar_mean_images`, [BrickworkEndpointMean.lean](../Fluctuations/BrickworkEndpointMean.lean) | Proved reflecting-chain and finite binomial-image formulas, including zero-depth and two-qubit cases |
| Literal $\Psi_d$ display in `thm:endpoint-otoc1-exact-formula` | Separate regrouping of the exact image expression | Not formalized |
| Gaussian mean-front estimate and full outer variance-influence envelope | Separate results | Not formalized |

For $n=2(c+2)$ and $d=2T$, the final endpoint theorem assumes
$\sqrt n\ge12(C+2)$, $|d-5n/3|\le C\sqrt n$, and $\mathrm{Tr}\rho=1$.
It has no design, conditional-mean, propagation, or gate-count premise.
Only the selected central eye is counted; an upper bound on its cardinality
does not establish an outer influence envelope. See the
[earlier independent scope review](otoc1-review.md), which predates the
simulation extension below.

## Classical simulation of the infinite-temperature endpoint OTOC

The simulation uses $F_\infty=2^{-n}\mathrm{Tr}[(U^\dagger Z_1UZ_n)^2]$
at $n=6(s+1)$ and $d=10(s+1)$. The final accuracy theorem is about the
joint law of the Haar circuit and the estimator's independent samples.
It has no supplied bias, local perturbation, or mean-change assumption.
The fluctuation theorem above has the broader trace-one-state scope.

| Manuscript statement or ingredient | Lean declaration and source | Status |
| --- | --- | --- |
| `thm:endpoint-sim-otoc1-runtime`; algorithm in `tab:endpoint-otoc1-explicit-simulation` | `otoc1_subexponential_simulation`, [Simulation.lean](../Fluctuations/Simulation.lean) | Actual normalized trace, specified radius and sample count, joint success probability at least $1-\delta$ |
| `eq:endpoint-sim-conditional-distribution` | [SimulationTrace.lean](../Fluctuations/SimulationTrace.lean), [SimulationMixedCircuitOTOC.lean](../Fluctuations/SimulationMixedCircuitOTOC.lean) | Normalized matrix trace equals the Pauli-sign mean, including the actual retained-gate conditional law |
| `lem:endpoint-sim-local-gate` | [SimulationLocalInfluence.lean](../Fluctuations/SimulationLocalInfluence.lean), [SimulationLocalCoordinate.lean](../Fluctuations/SimulationLocalCoordinate.lean), [SimulationExpectedTouch.lean](../Fluctuations/SimulationExpectedTouch.lean) | Physical gate replacement controlled by forward/backward touching mass |
| `lem:endpoint-sim-touching-tail` | [SimulationEndpointTail.lean](../Fluctuations/SimulationEndpointTail.lean), [SimulationTouchingTail.lean](../Fluctuations/SimulationTouchingTail.lean), [SimulationTailReflection.lean](../Fluctuations/SimulationTailReflection.lean) | Derived finite endpoint tails and reflected backward process |
| `lem:endpoint-sim-eye-error` | [SimulationAveraging.lean](../Fluctuations/SimulationAveraging.lean), final physical assembly in [Simulation.lean](../Fluctuations/Simulation.lean) | Telescoping replacement under the actual product Haar law gives the enlarged-eye bias bound |
| `lem:endpoint-sim-conditional-sampler`; full second-moment invariant | [SimulationSampler.lean](../Fluctuations/SimulationSampler.lean), [SimulationSamplerCovariance.lean](../Fluctuations/SimulationSamplerCovariance.lean), [SimulationMixedCircuit.lean](../Fluctuations/SimulationMixedCircuit.lean) | Exact finite branching law preserves full covariance and samples the required conditional Pauli distribution |
| Same output law for the costed physical implementation | `simulationPhysicalSamplerKernel_eq`, [SimulationPhysicalLaw.lean](../Fluctuations/SimulationPhysicalLaw.lean) | Full covariance, output PMF and conditional probability kernel agree with the chronological mixed-circuit sampler for every realized input |
| Outside-first ordering and $O(W_R)$ coherent sites | [SimulationGeometryReorder.lean](../Fluctuations/SimulationGeometryReorder.lean), [SimulationGeometrySampler.lean](../Fluctuations/SimulationGeometrySampler.lean), [SimulationWidth.lean](../Fluctuations/SimulationWidth.lean) | Actual matching permutation, compressed-vector invariant, physical eye width, and at most $2W_R+4$ coherent sites during updates |
| Arithmetic-operation count | `simulationCritical_estimatorWork`, [SimulationGeometryCost.lean](../Fluctuations/SimulationGeometryCost.lean), [SimulationCost.lean](../Fluctuations/SimulationCost.lean) | Explicit $180002(N+1)n^2 4^{2\lceil2R\sqrt n+1\rceil+4}$ bound for generated local calls |
| Choices of $R,N$ and success probability | [SimulationParameters.lean](../Fluctuations/SimulationParameters.lean), [SimulationConcentration.lean](../Fluctuations/SimulationConcentration.lean), [SimulationJointProbability.lean](../Fluctuations/SimulationJointProbability.lean) | Exact parameter arithmetic, Hoeffding and Markov, and the genuine circuit/sampler joint probability measure |
| Inverse-polynomial subexponential specialization | `otoc1_subexponential_simulation_inversePolynomial`, [Simulation.lean](../Fluctuations/Simulation.lean); explicit majorant in [SimulationAsymptotics.lean](../Fluctuations/SimulationAsymptotics.lean) | Joint accuracy at every size and $\log(\mathrm{work})/n\to0$ for the same sampler, with $\varepsilon=n^{-a}$, $\delta=n^{-b}$ and fixed positive natural exponents |

The operation model is exact scalar arithmetic (real or complex) with sampling from explicitly
computed finite distributions, as assumed in the manuscript. The counter
covers sampling and readout arithmetic, including transfer-matrix construction;
it excludes indexing, stored-coefficient reads, and schedule and parameter
preprocessing. No extracted numerical executable, bit-complexity bound, or
finite-precision analysis is provided. These simulation tail estimates do not prove the separate Gaussian mean-front
approximation or full variance-influence envelope. See the
[simulation guide](simulation.md) for the precise parameter and cost scope.

## General variance argument

| Manuscript ingredient | Lean declaration and source | Status |
| --- | --- | --- |
| Complex variance | `complexVariance`, [Probability.lean](../Fluctuations/Probability.lean) | Defined as the integral of squared complex deviation |
| Eq. (107), local reverse variance | `LocalReverseVariance`, [Probability.lean](../Fluctuations/Probability.lean) | Input for general ensembles; proved for Haar below |
| Eqs. (109)–(110), total variance and slope estimate | `complex_total_variance`, `slope_to_variance`, [Probability.lean](../Fluctuations/Probability.lean) | Proved |
| Lemma VI.13, forward persistence | `forward_persistence`, [WeightedVariance.lean](../Fluctuations/WeightedVariance.lean) | Proved |
| Large increment and consecutive window | [Window.lean](../Fluctuations/Window.lean), [Main.lean](../Fluctuations/Main.lean) | Proved |
| Theorem VI.14 | `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family`, [Main.lean](../Fluctuations/Main.lean) | General bound, interval, and polynomial-family quantifiers, from the stated inputs |
| Arbitrary mean gap | `transition_window`, [Main.lean](../Fluctuations/Main.lean) | Proved |

## Haar local coefficient

| Manuscript ingredient | Lean declaration and source | Status |
| --- | --- | --- |
| Genuine Haar local gates | [HaarSU4.lean](../Fluctuations/HaarSU4.lean) | Actual normalized product Haar on SU(4); coordinate independence |
| Actual local matrix OTOC | `haarLocalOTOC_apply`, [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | Same trace and power `2*k` |
| Qualitative finite-dimensional bound | `finiteDimensional_reverseVariance`, [FiniteDimensionalVariance.lean](../Fluctuations/FiniteDimensionalVariance.lean) | Proved for compact full-support laws |
| Quantitative Haar evaluation estimate | `haar_subspace_reverseVariance`, [HaarEvaluationBound.lean](../Fluctuations/HaarEvaluationBound.lean) | Proved by a constant evaluation kernel and centering; alternative to the paper's Schur-orthogonality proof |
| Dimension bound for the balanced local space | `haarLocalOTOC_balanced_mem`, `balancedSU4_polynomial_finrank_le`, [BalancedHaarFeatures.lean](../Fluctuations/BalancedHaarFeatures.lean) | Actual OTOC membership and dimension at most $4^{8km}$ |
| Eq. `eq:two-qubit-haar-explicit-constant` | `haarLocalOTOC_explicit_reverseVariance_identity`, [ExplicitHaarVariance.lean](../Fluctuations/ExplicitHaarVariance.lean) | Exact coefficient $4^{-8km}$ proved |
| Conditional local inequality | `haarLocalOTOC_explicit_conditional_reverseVariance`, [ExplicitHaarVariance.lean](../Fluctuations/ExplicitHaarVariance.lean) | Same numerical coefficient for actual conditional variance |
| Full-layer propagation of the coefficient | [ExplicitHaarCircuit.lean](../Fluctuations/ExplicitHaarCircuit.lean) | Slope, persistence, and window with the numerical coefficient |

The numerical proof uses paired gate words, not the earlier raw homogeneous
feature count. Each gate contributes one entry and one conjugate to a paired
word; taking degree $2k$ gives $4^{8km}$ possible coefficient indices.

## Spatial architecture

| Manuscript ingredient | Lean declaration and source | Status |
| --- | --- | --- |
| Physical operator support | `Supported`, `Supported.commute`, [TensorSupport.lean](../Fluctuations/TensorSupport.lean) | Defined using actual tensor entries; disjoint supports imply commutation |
| Arbitrary pair of qubits | `twoQubitPatchEmbedding`, [PatchEmbedding.lean](../Fluctuations/PatchEmbedding.lean) | Actual unital star-algebra insertion with proved support and unitarity |
| Parallel disjoint gate patches | `LayerArchitecture`, [CircuitGeometry.lean](../Fluctuations/CircuitGeometry.lean) | Gate count and patches may vary between deterministic layers |
| Inactive cancellation | `LayerArchitecture.conjugate_eq_active` | Derived from physical support and patch disjointness |
| Backward cone and propagation | `supported_spatialCircuit`, `spatialCircuit_commute_of_disjoint` | Deterministic sufficient cone; no minimality claim |
| Bounded active count | `LayerArchitecture.card_active_le`, `backwardActiveGateCount_le` | At most $\lvert S\rvert$ gates per parallel layer; explicit bound for a fixed-depth block |
| Certificates for sampled Haar circuit | [SpatialHaarGeometry.lean](../Fluctuations/SpatialHaarGeometry.lean) | Actual circuit support, inactive/early commutation, and early mean one |
| VI.14 with a supplied mean change | `spatialHaarCircuit_variance_window`, [SpatialHaarTheorem.lean](../Fluctuations/SpatialHaarTheorem.lean) | Canonical patch embeddings and numerical coefficient $4^{-8k|S|}$; no separate local variance or commutation premise |

The general spatial probabilistic assembly uses fixed active and inactive counts
across depths. General varying-count Haar histories and their reindexing law
are not yet assembled. Graph-distance propagation speeds and architecture-
specific last-light-cone asymptotics are separate from the proved site-set
cone. The local SU(4)-to-U(4) phase/Haar-law bridge remains to be proved for
this general pipeline. The endpoint pipeline above samples U(4) directly.

## Global Haar mean and mean change

The manuscript proposition `prop:haar-otock-small` bounds the actual global
Haar OTOC mean uniformly over states at fixed positive order. The formalization
now proves the quantitative all-dimension estimate

```math
|h_{\rho,B,M,k}|\le \frac{2((2k)!)^3}{D^2},
\qquad D\ge1,\quad k>0.
```

The observables are arbitrary Hermitian traceless involutions, including the
nonidentity Pauli observables of the manuscript. Only trace normalization is
required of $\rho$. The large-dimension inverse-Gram estimate is extended to every dimension
using the actual unitary norm bound $|h|\le1$. This proves the manuscript
proposition and supplies the mean separation needed by VI.14.

| Ingredient | Lean declaration / source | Status |
| --- | --- | --- |
| Actual normalized global U($D$) Haar integral | `globalHaarOTOCMean`, [GlobalHaarMean.lean](../Fluctuations/GlobalHaarMean.lean) | Defined using the same matrix OTOC |
| Uniformity in the state | `globalHaarOTOCMean_state_independent_of_traceless_involution`, [GlobalHaarPauliMean.lean](../Fluctuations/GlobalHaarPauliMean.lean) | Proved by spectral reduction and signed-permutation symmetries |
| Tensor invariant space | [HaarTensorInvariants.lean](../Fluctuations/HaarTensorInvariants.lean), [TensorUnitaryExtension.lean](../Fluctuations/TensorUnitaryExtension.lean) | Unitary commutation implies permutation spanning for tensor order at most $D$ |
| Haar projection and inverse Gram formula | `globalHaarTensorMean_weingarten`, [HaarWeingartenProjection.lean](../Fluctuations/HaarWeingartenProjection.lean) | Proved for the actual integral |
| Cyclic OTOC trace | [HaarOTOCTraceIdentity.lean](../Fluctuations/HaarOTOCTraceIdentity.lean) | Actual matrix-power trace equals the tensor permutation contraction |
| Pauli cycle contractions | [TensorPermutationTrace.lean](../Fluctuations/TensorPermutationTrace.lean) | Odd cycles vanish; each even cycle contributes $D$ |
| Coefficient bounds and finite sum | [WeingartenGramBounds.lean](../Fluctuations/WeingartenGramBounds.lean), [HaarMeanCombinatorics.lean](../Fluctuations/HaarMeanCombinatorics.lean) | Proved from an explicit inverse Gram matrix and cycle/sign counting |
| Actual all-order mean bound | `globalHaarOTOCMean_norm_le`, [GlobalHaarMeanBound.lean](../Fluctuations/GlobalHaarMeanBound.lean) | No assumed integration identity, coefficient estimate, or state-independence premise |
| All-dimension bound and Haar quarter-bound | [GlobalHaarMeanAllDimensions.lean](../Fluctuations/GlobalHaarMeanAllDimensions.lean) | The inverse-square bound has no dimension restriction; $D^2\ge8((2k)!)^3$ gives the quarter-bound |
| Exact first-order mean | [GlobalHaarFirstOrderValue.lean](../Fluctuations/GlobalHaarFirstOrderValue.lean) | $-1/(D^2-1)$ for $D>1$ |
| Final spatial VI.14 deduction | `spatialHaarCircuit_allOrders_of_globalHaar_control`, [SpatialHaarFinal.lean](../Fluctuations/SpatialHaarFinal.lean) | Geometry, numerical local coefficient, and actual Haar smallness all discharged |

The final spatial theorem assumes the physical architecture, observable
support, trace/involution conditions, early cone separation, the displayed
dimension threshold, late moment error at most $1/4$ from the actual Haar
mean, and transition width. It derives the half-unit gap and the numerical
variance window. Design convergence and polynomial width remain intended
external inputs. The first-order specialization needs at least two qubits
for the quarter-bound and does not require Hermiticity.

The generic combinatorial transfer and intermediate spatial theorems remain
available with explicit hypotheses; these are reusable lemmas, not the final
assumption boundary. The one-dimensional front-window and central-eye
influence and infinite-temperature simulation results are proved separately
above. Computational quantum advantage remains outside the formalization.

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
`Fluctuations.otoc1_endpoint_variance_lower`,
`Fluctuations.otoc1_subexponential_simulation`,
`Fluctuations.spatialHaarCircuit_allOrders_of_globalHaar_control`, or
`Fluctuations.theorem_VI_14_family`. No publication identifier is inferred from
the draft filename.

