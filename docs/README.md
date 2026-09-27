# Read the formalization alongside the paper

[Home](../README.md) / Reader guide

The paper develops one argument in three stages: **general fixed-order
fluctuations**, a **sharper one-dimensional OTOC₁ analysis**, and a
**classical simulation application**. Follow the same sequence here.
The section numbers below refer to the [inspected manuscript](reference/paper-map.md#manuscript-provenance).

## The manuscript route

| Order | In the manuscript | English guide | Final Lean entry points |
| :--- | :--- | :--- | :--- |
| **1. General OTOC⁽ᵏ⁾ variance** | Main §II; SM §VI, especially Theorem VI.14 | [General variance lower bound](results/01-general-otoc-variance.md) | [Main.lean](../Fluctuations/Main.lean), [SpatialHaarFinal.lean](../Fluctuations/SpatialHaarFinal.lean) |
| **2. One-dimensional OTOC₁** | Main §III and §III A; SM §VII | [Exact mean, fluctuations, and influential gates](results/02-otoc1-fluctuations.md) | [BrickworkEndpointMean.lean](../Fluctuations/BrickworkEndpointMean.lean), [OTOC1.lean](../Fluctuations/OTOC1.lean) |
| **3. Classical simulation** | Main §III B; SM §VIII | [Estimator, error, and subexponential work](results/03-classical-simulation.md) | [Simulation.lean](../Fluctuations/Simulation.lean) |

## 1. Begin with the general variance theorem

The central idea is that **a change in the mean forces fluctuations**.
Before the light cone reaches the probe, the OTOC is one. At a later depth,
control of the mean relative to its small Haar value certifies a constant
change. The proof finds a large one-layer mean increment, converts it into
variance, and propagates the lower bound to subsequent depths.

Read the [general result guide](results/01-general-otoc-variance.md) in this order:

1. **Statement:** what Theorem VI.14 concludes and how the polynomial scaling arises.
2. **Abstract argument:** `theorem_VI_14`, its interval form, and its family form in [Main.lean](../Fluctuations/Main.lean).
3. **Spatial Haar realization:** [SpatialHaarFinal.lean](../Fluctuations/SpatialHaarFinal.lean), where the local Haar and geometric ingredients are proved.
4. **Supporting ingredients:** light cones and support, the explicit local reverse-variance coefficient, and the [global Haar mean estimate](reference/haar-mean.md) from the preliminaries.

For the abstract theorem, mean change and local reverse variance are
hypotheses. The concrete spatial Haar theorem proves the local coefficient,
early identity, and Haar smallness; late moment control and transition width
remain inputs. Its SU(4) model and architecture restrictions are listed in
the guide. Hardware-ensemble applications and general graph-distance
asymptotics in the paper are not all covered by that concrete assembly.

## 2. Then read the one-dimensional refinement

The paper next asks which depths and gates produce the fluctuations.
In open Haar U(4) brickwork circuits, the endpoint analysis yields a much
stronger $\Omega(n^{-1/2})$ variance lower bound throughout a diffusive
window around $5n/3$, with a constructed set of $\Theta(n^{3/2})$
influential gates.

The [OTOC₁ guide](results/02-otoc1-fluctuations.md) follows SM §VII:
the exact finite-circuit mean, the status of the Gaussian approximation,
the variance lower bound, and individual gate contributions. These
fluctuation statements are uniform over trace-one states and require no
design-convergence assumption.

The exact mean is proved through a finite image formula. The manuscript’s
literal $\Psi$ regrouping, its Gaussian mean-front approximation, and the
full exterior influence envelope remain outside the formalization; their
status is marked where they appear in the paper’s route.

## 3. Finish with the classical simulation application

The [simulation guide](results/03-classical-simulation.md) follows the algorithm’s
argument: average gates outside an enlarged eye, sample the conditional Pauli
law, bound the error, and count the arithmetic work.

The final result concerns the **infinite-temperature** endpoint OTOC, for
positive multiples of six qubits at the critical depth $5n/3$. The probability
is over both the Haar circuit and the sampler. The proved subexponential
cost is in exact scalar arithmetic with finite-distribution draws; it is not
a finite-precision or bit-complexity result. Its Gaussian touching-tail
estimate is distinct from the unformalized mean-front approximation above.

## Find a declaration, review a claim, or run Lean

- **A theorem or lemma in the paper:** use the [paper-to-proof map](reference/paper-map.md), organized in the same three-part order.
- **A supporting module:** use the [Lean source index](../Fluctuations/README.md). All 129 modules are grouped under the three main parts.
- **Assumptions and correspondence:** begin with the [reviewer guide](../REVIEW.md); then read the [assumption audit](reviews/assumptions.md) and the independent [endpoint](reviews/endpoint.md) or [simulation](reviews/simulation.md) review.
- **Compilation and axiom checks:** follow [verification instructions](verification/README.md) and consult the [recorded evidence](verification/record.txt).
- **Development:** read [CONTRIBUTING.md](../CONTRIBUTING.md).

The repository formalizes the stated mathematical results. Computational
quantum advantage itself is not established by these proofs.

---

**Start here:** [1. General OTOC⁽ᵏ⁾ variance lower bound →](results/01-general-otoc-variance.md)
