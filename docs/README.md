# A reader’s guide to the formalization

[Home](../README.md) / Reader guide

Read the English statement first, check its assumptions, then open the named
Lean declaration. You can follow the mathematical argument without reading
every supporting module.

## From the paper to the proof

| You are reading about… | Begin here | Then open… |
| :--- | :--- | :--- |
| The OTOC₁ fluctuation lower bound and influential gates | [Endpoint fluctuations](results/endpoint-fluctuations.md) | [OTOC1.lean](../Fluctuations/OTOC1.lean) |
| The exact finite-depth endpoint mean | [Endpoint mean and scope](results/endpoint-fluctuations.md) | [BrickworkEndpointMean.lean](../Fluctuations/BrickworkEndpointMean.lean) |
| The classical conditional-sampling algorithm and subexponential cost | [Classical simulation](results/classical-simulation.md) | [Simulation.lean](../Fluctuations/Simulation.lean) |
| The general variance-window theorem VI.14 | [Spatial variance](results/spatial-variance.md) | [SpatialHaarFinal.lean](../Fluctuations/SpatialHaarFinal.lean) |
| Smallness of the global Haar mean | [Global Haar mean](results/haar-mean.md) | [GlobalHaarMeanAllDimensions.lean](../Fluctuations/GlobalHaarMeanAllDimensions.lean) |

For exact manuscript labels, intermediate lemmas, and draft provenance, use
the [complete paper-to-proof map](reference/paper-map.md). The
[Lean source index](../Fluctuations/README.md) groups every module by its role
in the argument.

## Three ways to use this companion

### Understand a result

1. Choose a result guide above.
2. Read **the statement and hypotheses**, including the circuit model and probability space.
3. Open the final Lean entry point. Its theorem signature specifies the exact quantifiers.
4. Follow the proof route in the guide, or the imports in the source, when you need a supporting ingredient.

### Review correctness and correspondence

Begin with the [reviewer guide](../REVIEW.md). It connects the
[assumption audit](reviews/assumptions.md), the
[endpoint review](reviews/endpoint.md), and the
[simulation review](reviews/simulation.md).
A compiled theorem and its correspondence to the paper are distinct checks;
the reviews explain the mathematical correspondence and its limits.

### Reproduce or extend the proof

Follow the [verification instructions](verification/README.md), consult the
[recorded build and axiom audit](verification/record.txt), and use the
[contribution guide](../CONTRIBUTING.md) for changes.

## Keep the theorem scopes separate

| Topic | Scope to keep in mind |
| :--- | :--- |
| Endpoint fluctuations | Actual Haar U(4) brickwork; every trace-one input matrix; explicit even-size, even-depth, and front-window conditions. No design-convergence assumption. |
| Classical simulation | Infinite-temperature endpoint OTOC; positive multiples of six at depth $5n/3$; joint circuit-and-sampler success probability; exact scalar arithmetic and finite-distribution draws. |
| General spatial variance | Actual Haar SU(4) gates; explicit architecture and support conditions; fixed active/inactive counts in the assembled process. Design mean control and transition width remain inputs. |
| Global Haar mean | Actual normalized U($D$) Haar integral; Hermitian traceless involutions and a trace-one state for the all-order estimate. This differs from the finite-depth circuit mean. |

The current results do not establish computational quantum advantage,
finite-precision simulation or bit complexity, the manuscript’s literal
$\Psi$ regrouping, its Gaussian mean-front approximation, or the full exterior
variance-influence envelope. The simulation’s proved Gaussian touching-tail
estimate is a separate statement. The general spatial pipeline’s SU(4)-to-U(4)
Haar-law correspondence is also outside its current formal assembly.

---

**Next:** [Choose a paper theorem](reference/paper-map.md) · [Browse the Lean modules](../Fluctuations/README.md) · [Reproduce verification](verification/README.md)
