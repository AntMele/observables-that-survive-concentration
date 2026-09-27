# Mathematical guide

[Overview](../README.md) · [Paper map](paper-mapping.md) · [Reproduction](reproduce.md)

The strongest result combines algebraic locality certificates, a proved local
Haar variance inequality, and explicit bounds controlling the endpoint means.
The general fluctuation theorem is retained for other ensembles.

## The concrete circuit model

At every depth, sample $m$ active and $q$ inactive independent normalized Haar
SU(4) gates. All gates in different layers are also independent. Their unital
complex star-algebra embeddings may depend on depth. Let $A_d$ and $J_d$ be the
ordered active and inactive products and define

```math
U_0=I,\qquad U_{d+1}=(J_dA_d)U_d,\qquad
F_d=\mathrm{Tr}\!\left[\rho(U_d^\dagger B U_dM)^{2k}\right].
```

[ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) retains both
blocks in the circuit matrix and its independent product history. The parameter
$q$ is fixed within a given model but may vary across system sizes; the variance
constant does not depend on it. The active count $m$ and order $k$ determine
that constant.

[HaarSU4.lean](../Fluctuations/HaarSU4.lean) constructs the actual compact special
unitary group and normalized product Haar law.
[HaarProcess.lean](../Fluctuations/HaarProcess.lean) constructs finite histories
recursively. Different depths have their own finite history spaces, related by
product-measure identities. The star-algebra embeddings preserve unitary gates;
[QubitEmbedding.lean](../Fluctuations/QubitEmbedding.lean) supplies
$C\mapsto C\otimes I_S$ on any finite spectator system.

## What the locality certificate proves

The full-layer theorem assumes that every possible embedded inactive gate
commutes with $B$. Unitarity then gives

```math
J_d^\dagger BJ_d=B,\qquad
(J_dA_d)^\dagger B(J_dA_d)=A_d^\dagger BA_d.
```

Thus, with earlier history fixed, fresh inactive gates do not affect the OTOC.
They are integrated out without weakening the active-block variance constant.
They are **not deleted from the circuit**: they remain in $U_{d+1}$ and can
influence later layers.

[SpatialSupport.lean](../Fluctuations/SpatialSupport.lean) also treats an
interleaved ordered gate list. If every active factor commutes with every
inactive factor, the factors can be regrouped as inactive times active while
preserving the internal order of each list. If the inactive factors are unitary
and commute with $B$, their conjugation cancels. The ordered model above does
not need this additional cross-commutation assumption because its order is
already specified.

Separate tensor factors provide a concrete commutation certificate:
$C\otimes I$ commutes with $I\otimes D$. These are algebraic support results.
The project does not construct a graph light cone, propagate support through an
arbitrary architecture, or prove that the number of active gates is bounded by
an architecture-dependent constant. Those certificates and the chosen count
must still be supplied for a geometric application.

## Why local reverse variance follows

Fix the earlier full circuit $V$. After the cancellation above, only the next
active block $W(h)$ remains in the local observable:

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
Thus the full-layer theorem does not assume the local inequality,
square-integrability, continuity, or polynomial membership as additional premises.

The space used here is a larger total-degree space than the paper's more refined
representation. This proves uniform existence of $\eta(m,k)$, not the explicit
value $4^{-8km}$.

## How the half-unit mean gap is obtained

[MeanChange.lean](../Fluctuations/MeanChange.lean) proves the algebra behind the
early-time identity. Assume $\mathrm{Tr}(\rho)=1$, $B^2=M^2=I$, and at depth $a$
the evolved observable $U_a^\dagger BU_a$ commutes with $M$ for every history.
Unitary conjugation preserves the involution relation. The product of two
commuting involutions has every even power equal to $I$, so $F_a=1$ pointwise
and $\mathbb EF_a=1$.

Now provide a complex reference mean $h$ satisfying

```math
|\mathbb EF_b-h|\leq\frac14,\qquad |h|\leq\frac14.
```

The triangle inequality gives $|\mathbb EF_b|\leq1/2$, hence
$|\mathbb EF_b-\mathbb EF_a|\geq1/2$.
`activeHaarCircuit_theorem_of_moment_control` assembles this derivation with the
local Haar bound and the variance-window argument below. Trace normalization
and the involution relations are needed for this route; the theorem with a
supplied endpoint gap permits arbitrary $\rho,B,M$.

The reference is a supplied complex number. In the paper it is chosen as the
Haar mean. The theorem does not compute that mean, prove its smallness, or
derive the approximation bound from a unitary-design distance. It proves the
half-gap once those scalar estimates and early commutation are certified.

## From a mean change to a variance window

Write $m_d=\mathbb EF_d$ and $V_d=\mathbb E|F_d-m_d|^2$. For a general process,
the local assumption says that with $M_d=\mathbb E[F_{d+1}\mid\mathcal G_d]$,

```math
\mathbb E[|F_{d+1}-M_d|^2\mid\mathcal G_d]
\geq\eta|M_d-F_d|^2
```

almost everywhere, with one common $\eta>0$.

The following argument is shared by the circuit and general-process results:

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
| `activeHaarCircuit_theorem_of_moment_control` in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Full layers; derives the half-gap from early commutation, trace normalization, involutions, and the two quarter-unit mean bounds. |
| `activeHaarCircuit_theorem_VI_14` in [ActiveHaarCircuit.lean](../Fluctuations/ActiveHaarCircuit.lean) | Full layers with inactive-gate commutation certificates and a supplied half-unit gap. |
| `haarCircuit_theorem_VI_14` in [HaarCircuit.lean](../Fluctuations/HaarCircuit.lean) | Actual independent Haar SU(4) circuit blocks; local reverse variance is proved. |
| `haarLocalOTOC_conditional_reverseVariance` in [HaarLocalVariance.lean](../Fluctuations/HaarLocalVariance.lean) | The conditional local inequality for a continuous earlier circuit and an independent Haar block. |
| `history_transition_window` in [HaarProcess.lean](../Fluctuations/HaarProcess.lean) | Arbitrary nonnegative mean gap for continuous history observables in one fixed local feature space. |
| `transition_window` in [Main.lean](../Fluctuations/Main.lean) | General complex square-integrable processes with mean change and local reverse variance supplied. |
| `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family` in [Main.lean](../Fluctuations/Main.lean) | The uniform bound, explicit finite interval, and polynomial-family quantifiers for the general theorem. |

The full-layer theorem chooses $\eta$ before $q$, the global matrix index type,
embeddings, and observable matrices. The same constant therefore applies as
system size and the inactive-gate count vary while $m,k$ stay fixed. With $P=p(n)$ and fixed $R$, the
prefactor $c=\eta\kappa^R/4$ is positive and independent of $n$. Allowing $m$ or
$R$ to grow with $n$ does not give that uniform conclusion automatically.

## What still connects this model to the paper

The algebraic cancellation and mean-gap deduction are formalized. Applying them
to a particular spatial architecture still requires the inactive-gate and
early-time commutation certificates, a suitable active/inactive decomposition,
and a system-size-independent active count. Tensor-factor commutation and the
interleaved-list theorem supply useful pieces, but there is no general graph
support-propagation or light-cone cardinality theorem here.
The identification of an architecture's gate coordinates with the grouped
product sampling law also remains to be supplied for that architecture.

The late-time moment error, reference-mean bound, and transition-width bound
are inputs. The project does not prove design convergence, mixing depths, or
the paper's Haar-average estimates. The full stabilizing-element/open-support
criteria for other ensembles, the sharper numerical Haar constant, the paper's
other results, and computational quantum advantage also remain outside the
proved claims.
