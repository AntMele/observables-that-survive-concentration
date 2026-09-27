# Global Haar mean estimates

[Home](../../README.md) / [Reader guide](../README.md) / Global Haar mean

**Paper correspondence:** `prop:haar-otock-small` ·
**Final source:** [GlobalHaarMeanAllDimensions.lean](../../Fluctuations/GlobalHaarMeanAllDimensions.lean)

This result bounds the actual global Haar average of the OTOC. It supplies
the small reference mean used in the general spatial variance argument.
The finite-depth brickwork mean is a separate result in the
[endpoint guide](endpoint-fluctuations.md).

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
uses this gap in the [general spatial variance theorem](spatial-variance.md).
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

---

**Next:** [General spatial variance](spatial-variance.md) · [Paper-to-proof map](../reference/paper-map.md) · [Global Haar source catalog](../../Fluctuations/README.md#global-haar)
