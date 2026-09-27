# Lean source guide

[← Repository overview](../README.md) · [Paper reader’s guide](../docs/README.md)

Follow the manuscript in three chapters: **general fixed-order OTOC variance → one-dimensional OTOC₁ → classical simulation**. The global Haar mean, local reverse variance, and spatial support results are ingredients of the first chapter. All **129 proof modules** are indexed below.

## Start in manuscript order

| Chapter | English guide | Formal entry points |
| :--- | :--- | :--- |
| **I. General OTOC(k) variance** | [Variance window · Theorem VI.14](../docs/results/01-general-otoc-variance.md) | [SpatialHaarFinal.lean](SpatialHaarFinal.lean) assembles the physical Haar circuit theorem; [Main.lean](Main.lean) gives the abstract variance-window theorem. |
| **II. One-dimensional OTOC₁** | [Exact mean, fluctuations, and influential gates](../docs/results/02-otoc1-fluctuations.md) | [BrickworkEndpointMean.lean](BrickworkEndpointMean.lean) gives the exact mean; [OTOC1.lean](OTOC1.lean) proves the variance and many-gate influence bounds. |
| **III. Classical simulation** | [Estimator, accuracy, and subexponential work](../docs/results/03-classical-simulation.md) | [Simulation.lean](Simulation.lean) assembles the infinite-temperature simulation theorem. |

For Chapter I, [SpatialHaarTheorem.lean](SpatialHaarTheorem.lean) connects physical geometry to the variance argument. [ExplicitHaarVariance.lean](ExplicitHaarVariance.lean) proves the local coefficient, and [GlobalHaarMeanAllDimensions.lean](GlobalHaarMeanAllDimensions.lean) proves the Haar mean bound. The [Haar mean guide](../docs/reference/haar-mean.md) explains this supporting result and its exact first-order specialization.

For Chapter II, [BrickworkEndpointOTOC.lean](BrickworkEndpointOTOC.lean) supplies the quantum observable and conditional-mean identities. For Chapter III, follow [SimulationEyeError.lean](SimulationEyeError.lean) for bias, [SimulationPhysicalLaw.lean](SimulationPhysicalLaw.lean) for sampler correctness, and [SimulationAsymptotics.lean](SimulationAsymptotics.lean) for the work limit.

Read each final declaration’s hypotheses and quantifiers before following its imports. Intermediate lemmas may take inputs that the final circuit theorem subsequently proves. The [paper-to-proof map](../docs/reference/paper-map.md) gives exact manuscript labels.

## Complete module catalog

[**I. General variance**](#chapter-i) · [**II. One-dimensional OTOC₁**](#chapter-ii) · [**III. Simulation**](#chapter-iii)

Each module appears once in the expandable catalog below. Chapters follow the manuscript; the families within each chapter organize its supporting arguments.

<a id="chapter-i"></a>

## I. General OTOC(k) variance

47 modules · [Read the theorem and assumptions](../docs/results/01-general-otoc-variance.md). The mean estimate, local Haar coefficient, and physical geometry support the same variance-window theorem.

[Variance bounds and local Haar estimates](#variance) · [Physical support and spatial circuit geometry](#geometry) · [Global Haar means and tensor integration](#global-haar)

<a id="variance"></a>

<details>
<summary><strong>Variance bounds and local Haar estimates</strong> · 19 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [Main.lean](Main.lean) | Abstract variance lower bound and transition-window theorem (VI.14). |
| [Probability.lean](Probability.lean) | Local reverse variance and the passage from mean slope to variance. |
| [WeightedVariance.lean](WeightedVariance.lean) | Weighted comparison and forward persistence of variance. |
| [ProductVariance.lean](ProductVariance.lean) | Local reverse variance for independent product experiments. |
| [GateInfluence.lean](GateInfluence.lean) | Single-gate conditional means on product probability spaces. |
| [CoordinateAverages.lean](CoordinateAverages.lean) | Identification of coordinate averaging with conditional expectation. |
| [Window.lean](Window.lean) | Deterministic depth-window argument. |
| [MeanChange.lean](MeanChange.lean) | Conversion of endpoint mean estimates into a mean gap. |
| [HaarProcess.lean](HaarProcess.lean) | Independent gate histories and the abstract Haar-process theorem. |
| [FiniteDimensionalVariance.lean](FiniteDimensionalVariance.lean) | Reverse variance on finite-dimensional function spaces. |
| [LocalPolynomial.lean](LocalPolynomial.lean) | Polynomial feature spaces for matrix products and trace powers. |
| [HaarSU4.lean](HaarSU4.lean) | Haar SU(4) blocks and their coordinate features. |
| [HaarLocalVariance.lean](HaarLocalVariance.lean) | Local reverse variance for Haar-polynomial OTOCs. |
| [HaarEvaluationBound.lean](HaarEvaluationBound.lean) | Evaluation estimates on translation-invariant Haar feature spaces. |
| [BalancedHaarFeatures.lean](BalancedHaarFeatures.lean) | Balanced polynomial features and their dimension bounds. |
| [ExplicitHaarVariance.lean](ExplicitHaarVariance.lean) | The explicit local coefficient 4⁻⁸ᵏᵐ. |
| [HaarCircuit.lean](HaarCircuit.lean) | Variance theorem for circuits of Haar SU(4) gates. |
| [ActiveHaarCircuit.lean](ActiveHaarCircuit.lean) | Circuit layers with active and inactive gates. |
| [ExplicitHaarCircuit.lean](ExplicitHaarCircuit.lean) | Circuit variance and persistence with the explicit coefficient. |

</details>

<a id="geometry"></a>

<details>
<summary><strong>Physical support and spatial circuit geometry</strong> · 9 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [SpatialHaarFinal.lean](SpatialHaarFinal.lean) | All-order spatial variance theorem with global-Haar moment control. |
| [SpatialHaarFirstOrder.lean](SpatialHaarFirstOrder.lean) | First-order spatial variance theorem with the exact Haar mean. |
| [SpatialHaarTheorem.lean](SpatialHaarTheorem.lean) | Assembly of spatial geometry, local variance, and mean control. |
| [SpatialHaarGeometry.lean](SpatialHaarGeometry.lean) | Physical architecture, light cones, and active-gate counts. |
| [CircuitGeometry.lean](CircuitGeometry.lean) | Support propagation and backward cones for layered architectures. |
| [SpatialSupport.lean](SpatialSupport.lean) | Removal of inactive gates from a local conjugation step. |
| [TensorSupport.lean](TensorSupport.lean) | Concrete operator support on finite sets of qubits. |
| [PatchEmbedding.lean](PatchEmbedding.lean) | Insertion of operators on arbitrary physical qubit patches. |
| [QubitEmbedding.lean](QubitEmbedding.lean) | Embedding local SU(4) gates with spectator qubits. |

</details>

<a id="global-haar"></a>

<details>
<summary><strong>Global Haar means and tensor integration</strong> · 19 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [GlobalHaarMean.lean](GlobalHaarMean.lean) | Global OTOC means, symmetries, and moment-control definitions. |
| [GlobalHaarStateIndependence.lean](GlobalHaarStateIndependence.lean) | State independence from signed-permutation symmetries. |
| [GlobalHaarFirstOrder.lean](GlobalHaarFirstOrder.lean) | First-order twirling identities and equivariance. |
| [UnitaryEquivariantClassification.lean](UnitaryEquivariantClassification.lean) | Classification of maps equivariant under unitary conjugation. |
| [GlobalHaarFirstOrderValue.lean](GlobalHaarFirstOrderValue.lean) | Exact first-order Haar mean and dimension bounds. |
| [GlobalHaarPauliMean.lean](GlobalHaarPauliMean.lean) | State independence for traceless involution probes. |
| [GlobalHaarUnitBound.lean](GlobalHaarUnitBound.lean) | Unit upper bound on the global Haar OTOC mean. |
| [GlobalHaarMeanBound.lean](GlobalHaarMeanBound.lean) | All-order global Haar mean and inverse-square dimension estimate. |
| [GlobalHaarMeanAllDimensions.lean](GlobalHaarMeanAllDimensions.lean) | Global Haar mean estimates valid in all dimensions. |
| [HaarConjugationCovariance.lean](HaarConjugationCovariance.lean) | Second moments of Haar conjugation and trace coefficients. |
| [HaarMixedCovariance.lean](HaarMixedCovariance.lean) | Mixed second moments of Haar trace coefficients. |
| [HaarTensorInvariants.lean](HaarTensorInvariants.lean) | Tensor-power commutants and permutation spans. |
| [TensorUnitaryExtension.lean](TensorUnitaryExtension.lean) | Extension from unitary commutation to the tensor commutant. |
| [HaarTensorProjection.lean](HaarTensorProjection.lean) | Haar averaging as a projection in tensor representations. |
| [TensorPermutationTrace.lean](TensorPermutationTrace.lean) | Permutation traces, cycle formulas, and Gram matrices. |
| [HaarWeingartenProjection.lean](HaarWeingartenProjection.lean) | Actual Haar tensor integrals from the inverse Gram matrix. |
| [HaarOTOCTraceIdentity.lean](HaarOTOCTraceIdentity.lean) | Conversion of OTOC trace powers into tensor contractions. |
| [HaarMeanCombinatorics.lean](HaarMeanCombinatorics.lean) | Finite permutation sums and their norm estimates. |
| [WeingartenGramBounds.lean](WeingartenGramBounds.lean) | Invertibility and quantitative inverse-Gram bounds. |

</details>

<a id="chapter-ii"></a>

## II. One-dimensional OTOC₁

40 modules · [Read the exact mean and fluctuation results](../docs/results/02-otoc1-fluctuations.md). The Pauli and brickwork modules connect the physical circuit to the endpoint process.

[Endpoint walk, exact means, and OTOC₁ fluctuations](#endpoint) · [Pauli representation and physical brickwork circuits](#pauli)

<a id="endpoint"></a>

<details>
<summary><strong>Endpoint walk, exact means, and OTOC₁ fluctuations</strong> · 18 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [BrickworkEndpointMean.lean](BrickworkEndpointMean.lean) | Exact physical-circuit Haar mean, image formulas, and light cone. |
| [OTOC1.lean](OTOC1.lean) | Final physical endpoint OTOC variance and gate-influence theorems. |
| [BrickworkEndpointOTOC.lean](BrickworkEndpointOTOC.lean) | Actual endpoint OTOC, conditional means, and gate variance. |
| [EndpointVarianceAssembly.lean](EndpointVarianceAssembly.lean) | Assembly of front estimates into a variance lower bound. |
| [EndpointPhysicalEye.lean](EndpointPhysicalEye.lean) | Diffusive eye as a set of actual finite gate coordinates. |
| [EndpointEye.lean](EndpointEye.lean) | Lattice eye and its quantitative gate count. |
| [EndpointFrontLower.lean](EndpointFrontLower.lean) | Lower bounds for past and future factors inside the eye. |
| [EndpointFrontMass.lean](EndpointFrontMass.lean) | Front-mass estimates from binomial probabilities. |
| [BinomialLocalBounds.lean](BinomialLocalBounds.lean) | Local binomial lower bounds from Stirling estimates. |
| [EndpointPropagation.lean](EndpointPropagation.lean) | Ballot and front-profile formulas for endpoint propagation. |
| [EndpointBinomial.lean](EndpointBinomial.lean) | Biased-binomial identities used by the endpoint walk. |
| [EndpointImages.lean](EndpointImages.lean) | Method-of-images formula for the killed endpoint kernel. |
| [EndpointMean.lean](EndpointMean.lean) | Exact endpoint-chain means, including boundary cases. |
| [EndpointMarkov.lean](EndpointMarkov.lean) | Endpoint transition matrices and intertwining identities. |
| [EndpointLumpability.lean](EndpointLumpability.lean) | Projection from Pauli-string evolution to the endpoint walk. |
| [EndpointPerturbation.lean](EndpointPerturbation.lean) | Propagation of endpoint perturbations through untouched bonds. |
| [UniversalEndpointObservable.lean](UniversalEndpointObservable.lean) | Endpoint Pauli-sign readout after the final odd Haar layer. |
| [BrickworkEvenRemainder.lean](BrickworkEvenRemainder.lean) | Even matching with a selected bond removed. |

</details>

<a id="pauli"></a>

<details>
<summary><strong>Pauli representation and physical brickwork circuits</strong> · 22 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [PauliBasis.lean](PauliBasis.lean) | One- and two-qubit Pauli matrices, orthogonality, and reconstruction. |
| [PauliLocalHaar.lean](PauliLocalHaar.lean) | Exact Haar moments of the two-qubit Pauli transfer matrix. |
| [LocalPauliBalance.lean](LocalPauliBalance.lean) | The local balance identity used in the endpoint variance bound. |
| [PauliString.lean](PauliString.lean) | Pauli strings, pair updates, and tensor matrix representations. |
| [PauliStringQuantum.lean](PauliStringQuantum.lean) | Physical gate conjugation in the Pauli-string basis. |
| [ProductKernelEvolution.lean](ProductKernelEvolution.lean) | Second moments of independent random linear gate evolution. |
| [PauliCircuitBridge.lean](PauliCircuitBridge.lean) | Connection between actual quantum circuits and Pauli evolution. |
| [PauliEndpointObservable.lean](PauliEndpointObservable.lean) | Endpoint OTOCs as Pauli-sign observables after Haar averaging. |
| [PauliShock.lean](PauliShock.lean) | Product-form Pauli shock distributions and local evolution. |
| [PauliBrickwork.lean](PauliBrickwork.lean) | Odd and even matching layers on physical Pauli strings. |
| [PauliBrickworkInitial.lean](PauliBrickworkInitial.lean) | Initial endpoint Z operator and its first Haar layer. |
| [PauliBrickworkCircuit.lean](PauliBrickworkCircuit.lean) | Chronological brickwork gate schedule and circuit indexing. |
| [PauliBrickworkScheduleSplit.lean](PauliBrickworkScheduleSplit.lean) | Decomposition of the schedule at a selected even gate. |
| [PauliPairCommutation.lean](PauliPairCommutation.lean) | Commutation of updates on disjoint pairs of sites. |
| [PauliFixedLocal.lean](PauliFixedLocal.lean) | Local Pauli kernels with one gate fixed. |
| [PauliFixedGate.lean](PauliFixedGate.lean) | Effect of a fixed gate on endpoint masses and shock mixtures. |
| [PauliFixedPropagation.lean](PauliFixedPropagation.lean) | Propagation of a fixed-gate perturbation to the final observable. |
| [PauliFrozenCircuit.lean](PauliFrozenCircuit.lean) | Quantum conditional OTOCs with one gate held fixed. |
| [PauliFrozenSchedule.lean](PauliFrozenSchedule.lean) | Past/fixed-gate/future decomposition of conditional evolution. |
| [PauliBrickworkConditional.lean](PauliBrickworkConditional.lean) | Explicit conditional-mean gap for a physical brickwork gate. |
| [PauliUntouchedObservable.lean](PauliUntouchedObservable.lean) | Preservation of observables on untouched sites. |
| [PauliKernelMass.lean](PauliKernelMass.lean) | Adjointness and total-mass preservation for local Pauli kernels. |

</details>

<a id="chapter-iii"></a>

## III. Classical simulation

42 modules · [Read the simulation theorem and cost model](../docs/results/03-classical-simulation.md). The sampler, error estimates, and coherent-support bounds are assembled for the same physical circuit.

[Exact sampler and compressed operations](#simulation-sampler) · [Influence, tails, and approximation error](#simulation-error) · [Success probability and subexponential work](#simulation-probability)

<a id="simulation-sampler"></a>

<details>
<summary><strong>Simulation · exact sampler and compressed operations</strong> · 12 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [Simulation.lean](Simulation.lean) | Final simulation accuracy, arithmetic-work, and subexponential theorems. |
| [SimulationSampler.lean](SimulationSampler.lean) | Normalized finite branching sampler and local update rules. |
| [SimulationSamplerCovariance.lean](SimulationSamplerCovariance.lean) | Exact Haar covariance reproduced by the sampler. |
| [SimulationMixedCircuit.lean](SimulationMixedCircuit.lean) | Sampler law for circuits mixing retained and averaged gates. |
| [SimulationMixedCircuitOTOC.lean](SimulationMixedCircuitOTOC.lean) | Sampler expectation equals the partially averaged OTOC. |
| [SimulationSamplerSupport.lean](SimulationSamplerSupport.lean) | Coherent support and compressed Pauli-amplitude arrays. |
| [SimulationCompressedOperations.lean](SimulationCompressedOperations.lean) | Exact array operations and their arithmetic work. |
| [SimulationSamplerReorder.lean](SimulationSamplerReorder.lean) | Reordering disjoint gates without changing evolution. |
| [SimulationMixedCircuitCommutation.lean](SimulationMixedCircuitCommutation.lean) | Covariance preservation under mixed-gate reorderings. |
| [SimulationMixedListIndex.lean](SimulationMixedListIndex.lean) | Agreement between list-based and indexed circuit evolution. |
| [SimulationPhysicalLaw.lean](SimulationPhysicalLaw.lean) | Equality of the inexpensive physical sampler and accuracy law. |
| [SimulationTrace.lean](SimulationTrace.lean) | Exact fixed-circuit infinite-temperature OTOC as a signed Pauli mass. |

</details>

<a id="simulation-error"></a>

<details>
<summary><strong>Simulation · influence, tails, and approximation error</strong> · 18 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [SimulationPerturbation.lean](SimulationPerturbation.lean) | Stability estimates for normalized Pauli-amplitude readouts. |
| [SimulationLocalInfluence.lean](SimulationLocalInfluence.lean) | Change in endpoint readout from replacing one local gate. |
| [SimulationLocalCoordinate.lean](SimulationLocalCoordinate.lean) | Single-coordinate influence in a chronological circuit. |
| [SimulationReverseCircuit.lean](SimulationReverseCircuit.lean) | Circuit reversal for the infinite-temperature endpoint OTOC. |
| [SimulationBackwardInfluence.lean](SimulationBackwardInfluence.lean) | Single-gate influence controlled from the circuit suffix. |
| [SimulationAveraging.lean](SimulationAveraging.lean) | Accumulated error when independent gate coordinates are averaged. |
| [SimulationCircuitAverage.lean](SimulationCircuitAverage.lean) | Physical OTOC, retained-gate mean, and forward averaging error. |
| [SimulationBackwardAverage.lean](SimulationBackwardAverage.lean) | Backward estimate for one-coordinate averaging error. |
| [SimulationTailBinomial.lean](SimulationTailBinomial.lean) | Binomial Chernoff and Hoeffding tail estimates. |
| [SimulationEndpointTail.lean](SimulationEndpointTail.lean) | Gaussian upper tails for the endpoint walk. |
| [SimulationTouchingTail.lean](SimulationTouchingTail.lean) | Gaussian bounds on the mass touching an odd or even gate. |
| [SimulationPrefixBridge.lean](SimulationPrefixBridge.lean) | Physical prefix schedules and local touching mass. |
| [SimulationTailReflection.lean](SimulationTailReflection.lean) | Reflection and reversal of physical suffix schedules. |
| [SimulationExpectedTouch.lean](SimulationExpectedTouch.lean) | Expected quantum touching mass equals Pauli-kernel mass. |
| [SimulationGateCoordinates.lean](SimulationGateCoordinates.lean) | Physical gate positions, times, and the retention schedule. |
| [SimulationTailPhysical.lean](SimulationTailPhysical.lean) | Forward and backward Gaussian tails for actual circuit gates. |
| [SimulationTailCausal.lean](SimulationTailCausal.lean) | Exact zeros outside the forward and backward causal cones. |
| [SimulationEyeError.lean](SimulationEyeError.lean) | Single-gate and total bias bounds outside the retained eye. |

</details>

<a id="simulation-probability"></a>

<details>
<summary><strong>Simulation · success probability and subexponential work</strong> · 12 modules</summary>

| Module | Role in the proof |
| :--- | :--- |
| [SimulationConcentration.lean](SimulationConcentration.lean) | Hoeffding sampling error and Markov bias estimates. |
| [SimulationSamplingProbability.lean](SimulationSamplingProbability.lean) | Actual output distributions and repeated-sampling tails. |
| [SimulationSamplingKernel.lean](SimulationSamplingKernel.lean) | Measurable conditional sampling law given the circuit. |
| [SimulationJointProbability.lean](SimulationJointProbability.lean) | Error under the genuine joint circuit-and-sampler measure. |
| [SimulationAccuracy.lean](SimulationAccuracy.lean) | Combination of circuit bias and sampling error. |
| [SimulationParameters.lean](SimulationParameters.lean) | Exact radius and sample-count choices for ε and δ. |
| [SimulationWidth.lean](SimulationWidth.lean) | Retained-eye geometry and coherent-support width. |
| [SimulationCost.lean](SimulationCost.lean) | Arithmetic model and explicit local and total operation counts. |
| [SimulationGeometryCost.lean](SimulationGeometryCost.lean) | Generation and size bounds of the physical operation schedule. |
| [SimulationGeometrySampler.lean](SimulationGeometrySampler.lean) | Physical sampler trajectories realize the costed support schedule. |
| [SimulationGeometryReorder.lean](SimulationGeometryReorder.lean) | Matching and permutation facts for processing outside gates first. |
| [SimulationAsymptotics.lean](SimulationAsymptotics.lean) | Explicit work envelope and the limit log(work)/n → 0. |

</details>

[Back to the repository overview](../README.md) · [Paper reader’s guide](../docs/README.md)
