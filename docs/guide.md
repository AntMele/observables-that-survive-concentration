# Mathematical guide

[Overview](../README.md) · [Paper map](paper-mapping.md) · [Reproduction](reproduce.md)

The project separates the general fluctuation argument from a concrete Haar
model that supplies its local reverse-variance input.

## The concrete circuit model

Let $h_d=(h_{d,1},\ldots,h_{d,m})$ be a fresh block of independent normalized
Haar SU(4) gates at step $d$. Blocks at different steps are independent. For
unital complex star-algebra embeddings $E_{d,i}$ into a finite global matrix
space, define the ordered product $W_d$ of the $E_{d,i}(h_{d,i})$ and set

```math
U_0=I,\qquad U_{d+1}=W_dU_d,\qquad
F_d=\mathrm{Tr}\!\left[\rho(U_d^\dagger B U_dM)^{2k}\right].
```

[HaarSU4.lean](../Fluctuations/HaarSU4.lean) constructs the actual special
unitary matrix group, proves compactness, and defines the normalized product
Haar law. [HaarProcess.lean](../Fluctuations/HaarProcess.lean) constructs finite
histories recursively, adjoining a new independent block at every step.
[HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) defines the matrices and OTOC
on those histories. Different depths have their own finite history spaces;
product-measure identities relate consecutive depths.

The embeddings preserve multiplication, identity, complex scalars, and adjoint,
so they take SU(4) gates to global unitary matrices.
[QubitEmbedding.lean](../Fluctuations/QubitEmbedding.lean) supplies the concrete
example $A\mapsto A\otimes I_S$ for any finite spectator system $S$. The theorem
allows arbitrary finite global dimensions and such embeddings; the matrices
$\rho,B,M$ are unrestricted. Density matrices and Pauli observables are
particular choices, rather than extra assumptions needed by the inequality.

## Why local reverse variance follows

Fix an earlier circuit $V$ and vary only the next block $W(h)$. Its local
observable is

```math
f_V(h)=\mathrm{Tr}\!\left[
\rho\bigl(V^\dagger W(h)^\dagger B W(h)VM\bigr)^{2k}\right].
```

There are $32m$ raw continuous features: every entry of each $4\times4$ gate
and its complex conjugate. An embedded gate entry is a linear combination of
these features. The ordered block has degree $m$; $W^\dagger BW$ has degree
$2m$; the trace above has total degree $4mk$.
[LocalPolynomial.lean](../Fluctuations/LocalPolynomial.lean) proves this
membership for the actual matrix expression, including arbitrary embedding
coefficients and arbitrary spectator dimension. Its finite-dimensional span
$\mathcal S_{m,k}$ depends only on $m,k$. In particular, $B,\rho,V,M$ and the
global dimension affect coefficients, not the chosen function space.

For any finite-dimensional space of continuous functions on a compact space,
a full-support probability law gives a common constant $\eta>0$ with

```math
\mathrm{Var}(f)\geq\eta\,|\mathbb Ef-f(e)|^2.
```

[FiniteDimensionalVariance.lean](../Fluctuations/FiniteDimensionalVariance.lean)
proves this by centering the functions. Full support makes the embedding of
continuous centered functions into $L^2$ injective. Finite-dimensional norm
comparison then bounds evaluation at $e$ by the $L^2$ norm. This proves an
existence result, without computing its constant.

Applying it to $\mathcal S_{m,k}$ gives a positive $\eta(m,k)$ for every local
OTOC simultaneously. At the identity block, $f_V(e)$ is the previous OTOC,
because the embeddings preserve identity.
[HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) proves both the
local integral inequality and its genuine conditional-expectation version
under the independent product law. [ProductVariance.lean](../Fluctuations/ProductVariance.lean)
identifies conditioning on the first factor with averaging the fresh block.
Thus the concrete Haar theorem does not assume the local inequality,
square-integrability, continuity, or polynomial membership as additional premises.

The space used here is a larger total-degree space than the paper's more refined
representation. This proves uniform existence of $\eta(m,k)$, not the explicit
value $4^{-8km}$.

## From a mean change to a variance window

Write $m_d=\mathbb EF_d$ and $V_d=\mathbb E|F_d-m_d|^2$. For a general process,
the local assumption says that with $M_d=\mathbb E[F_{d+1}\mid\mathcal G_d]$,

```math
\mathbb E[|F_{d+1}-M_d|^2\mid\mathcal G_d]
\geq\eta|M_d-F_d|^2
```

almost everywhere, with one common $\eta>0$.

The remaining argument is the same for both routes:

1. An endpoint gap $|m_b-m_a|\geq\Delta$ with $a<b$ forces one increment of
   size at least $\Delta/(b-a)$.
2. Total variance and the squared-mean inequality imply
   $V_{d+1}\geq\eta|m_{d+1}-m_d|^2$.
3. A weighted square inequality proves persistence:
   $V_{d+1}\geq\kappa V_d$, where $\kappa=\eta/(1+\eta)\in(0,1)$.
4. At one selected $a<d_*\leq b$, iteration gives

   ```math
   V_{d_*+r}\geq\eta\kappa^r\frac{\Delta^2}{(b-a)^2}.
   ```

For $\Delta=1/2$, $b-a\leq P$, and $0\leq r\leq R$, this yields

```math
V_{d_*+r}\geq\frac{\eta\kappa^R}{4P^2}.
```

The consecutive interval has $R+1$ depths and lies between $a+1$ and $b+R$.
Slope-to-variance and persistence are proved lemmas, not assumptions of the
final probabilistic results.

## Which theorem to read

| Declaration | Scope |
| --- | --- |
| `haarCircuit_theorem_VI_14` in [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Actual independent Haar SU(4) circuit blocks; local reverse variance is proved. |
| `haarLocalOTOC_conditional_reverseVariance` in [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | The conditional local inequality for a continuous earlier circuit and an independent Haar block. |
| `history_transition_window` in [HaarProcess.lean](../Fluctuations/HaarProcess.lean) | Arbitrary nonnegative mean gap for continuous history observables in one fixed local feature space. |
| `transition_window` in [Main.lean](../Fluctuations/Main.lean) | General complex square-integrable processes with mean change and local reverse variance supplied. |
| `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family` in [Main.lean](../Fluctuations/Main.lean) | The uniform bound, explicit finite interval, and polynomial-family quantifiers for the general theorem. |

The Haar-circuit theorem chooses $\eta$ before the global matrix index type,
embeddings, and observable matrices. The same constant therefore applies as
system size varies while $m,k$ stay fixed. With $P=p(n)$ and fixed $R$, the
prefactor $c=\eta\kappa^R/4$ is positive and independent of $n$. Allowing $m$ or
$R$ to grow with $n$ does not give that uniform conclusion automatically.

## What still connects this model to the paper

The model adds exactly $m$ independent gates per step. Reducing a general
spatial architecture or a layer containing a growing number of gates to a
fixed-size active block requires light-cone and inactive-gate cancellation
arguments that are not formalized here. The mean gap and width bound are also
inputs: this project does not prove design convergence, mixing depths, or the
paper's Haar-average estimates that establish them.

The full stabilizing-element/open-support criteria for other ensembles, the
sharper numerical Haar constant, the paper's other results, and computational
quantum advantage remain outside the proved claims. The general theorem is
available for those ensembles once its stated hypotheses are supplied.
