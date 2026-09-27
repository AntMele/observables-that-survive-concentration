# Supporting ingredient: global Haar mean estimates

[Home](../../README.md) / [Reader guide](../README.md) / Global Haar mean

**Paper correspondence:** `prop:haar-otock-small` ·
**Final source:** [GlobalHaarMeanAllDimensions.lean](../../Fluctuations/GlobalHaarMeanAllDimensions.lean)

**Place in the paper:** preliminaries (§V), `prop:haar-otock-small`; used in
the general OTOC⁽ᵏ⁾ variance theorem of §II / SM §VI.

This result bounds the actual global Haar average of the OTOC. It supplies
the small reference mean used in the general spatial variance argument.
The finite-depth brickwork mean is a separate result in the
[endpoint guide](../results/02-otoc1-fluctuations.md).

## Statement

Let $D\ge1$, $k\ge1$, and let $B,M$ be Hermitian, traceless involutions on
$\mathbb C^D$. For any matrix $\rho$ with $\mathrm{Tr}\rho=1$, define the
normalized Haar integral

```math
h_{\rho,B,M,k}=\int_{U(D)}
\mathrm{Tr}\!\left[\rho\left(U^\dagger BU M\right)^{2k}\right]\,dU.
```

The theorem `globalHaarOTOCMean_norm_le_all_dimensions` proves

```math
\left|h_{\rho,B,M,k}\right|\le\frac{2((2k)!)^3}{D^2}.
```

The constant depends only on the OTOC order. This inverse-square estimate
holds in every nonzero dimension under the stated observable hypotheses.
The formalization also proves that this mean is independent of the choice of
trace-one state.

At first order, `globalHaarOTOCMean_one_exact` in
[GlobalHaarFirstOrderValue.lean](../../Fluctuations/GlobalHaarFirstOrderValue.lean)
gives the exact value

```math
h_{\rho,B,M,1}=-\frac{1}{D^2-1}\qquad(D>1).
```

The first-order identity requires traceless involutions and trace normalization;
its theorem does not require Hermiticity.

## How this enters the variance theorem

The all-order estimate implies $|h|\le1/4$ when

```math
D^2\ge8((2k)!)^3.
```

Geometry supplies an early mean equal to one. A later circuit mean within
$1/4$ of this actual Haar mean then differs from the early mean by at least
$1/2$. [SpatialHaarFinal.lean](../../Fluctuations/SpatialHaarFinal.lean)
uses this gap in the [general spatial variance theorem](../results/01-general-otoc-variance.md).
The late circuit-to-Haar moment error and the transition width remain inputs;
the Haar integral and its smallness are proved.

For first order, the exact formula gives the quarter-bound on at least two
qubits. The all-order dimension threshold is needed for the quarter-bound,
not for the inverse-square estimate itself.

## Follow the argument

| Step | Source | What is proved |
| :--- | :--- | :--- |
| Define the actual integral | [GlobalHaarMean.lean](../../Fluctuations/GlobalHaarMean.lean) | Normalized U($D$) Haar measure and the matrix OTOC mean. |
| Remove state dependence | [GlobalHaarPauliMean.lean](../../Fluctuations/GlobalHaarPauliMean.lean) | Symmetry and spectral reduction for traceless involution probes. |
| Establish Haar integration | [HaarWeingartenProjection.lean](../../Fluctuations/HaarWeingartenProjection.lean) | The actual Haar projection equals its inverse-Gram expansion. |
| Evaluate the OTOC contraction | [HaarOTOCTraceIdentity.lean](../../Fluctuations/HaarOTOCTraceIdentity.lean), [TensorPermutationTrace.lean](../../Fluctuations/TensorPermutationTrace.lean) | Tensor contraction and cycle traces for the observable. |
| Bound the finite sum | [WeingartenGramBounds.lean](../../Fluctuations/WeingartenGramBounds.lean), [GlobalHaarMeanBound.lean](../../Fluctuations/GlobalHaarMeanBound.lean) | Coefficient estimates and the large-dimension mean bound. |
| Cover every dimension | [GlobalHaarMeanAllDimensions.lean](../../Fluctuations/GlobalHaarMeanAllDimensions.lean) | Combine the inverse-Gram estimate with the unit bound in smaller dimensions. |
| Evaluate first order exactly | [GlobalHaarFirstOrderValue.lean](../../Fluctuations/GlobalHaarFirstOrderValue.lean) | The exact value and its dimension consequences. |

The final estimate assumes no integration formula, coefficient bound, or
state-independence identity. Intermediate reusable lemmas can have such
premises; the final declaration discharges them.

## Details of the integration argument

For $B,M$ Hermitian traceless involutions and $\mathrm{Tr}\rho=1$,
[GlobalHaarMeanAllDimensions.lean](../../Fluctuations/GlobalHaarMeanAllDimensions.lean) proves

```math
|h_{\rho,B,M,k}|\le\frac{2((2k)!)^3}{D^2},
\qquad k>0,\quad D\ge1.
```

The proof first establishes state independence using the spectral theorem and
explicit signed permutations. It then reduces the maximally mixed trace to
$2k$ tensor factors. An operator commuting with every tensor power is proved
to lie in the span of position permutations when the tensor order is at most
$D$: polynomial continuation passes
from unitaries to all complex matrices, and one injective tensor-basis column
determines the invariant operator.

Actual Haar averaging lies in this invariant space and preserves trace
pairings with its basis. The Gram entries are proved to be
$D^{\#(\sigma^{-1}\tau)}$. Inverting this matrix yields the Haar integration
formula. The coefficient bounds follow from a convergent inverse estimate
when $D\ge2(2k)!$. Pauli contractions eliminate odd cycles; the sign of the
full cycle supplies the extra inverse dimension in the maximal-cycle case.
Every link is proved for the actual integral. For smaller dimensions, the
unit bound $|h|\le1$ is proved from unitarity and state independence and
absorbed into the same explicit constant.

The extra condition $D^2\ge8((2k)!)^3$ gives $|h|\le1/4$.
This threshold depends only on the fixed order $k$. For $k=1$, a separate
classification of unitary-equivariant linear maps gives the exact value
$-1/(D^2-1)$, so two qubits suffice for the quarter-bound.


---

**Return to the main argument:** [1. General OTOC⁽ᵏ⁾ variance](../results/01-general-otoc-variance.md) · [Paper-to-proof map](paper-map.md) · [Global Haar source catalog](../../Fluctuations/README.md#global-haar)
