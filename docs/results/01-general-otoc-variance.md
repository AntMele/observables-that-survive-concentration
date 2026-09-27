# 1. General variance lower bound for OTOC⁽ᵏ⁾

[Home](../../README.md) / [Reader guide](../README.md) / 1. General variance

**Paper:** main text §II (`thm:informalOTOCk`) → SM §VI, Theorem VI.14
(`thm:fixed-k-transition-window-fluctuation-bound`).

This is the paper’s central result. For every fixed positive OTOC order,
a constant change of the ensemble mean over a polynomial depth interval
forces inverse-polynomial circuit-to-circuit fluctuations. The sharper
one-dimensional OTOC₁ analysis comes [next](02-otoc1-fluctuations.md).

**Read:** [Statement](#the-variance-lower-bound) · [Proof mechanism](#the-proof-in-four-steps) · [Lean entry points](#which-theorem-to-read) · [Scope](#scope-relative-to-the-manuscript)

## The variance lower bound

Write

```math
F_d=\mathrm{Tr}\!\left[\rho(U_d^\dagger B U_dM)^{2k}\right],
\qquad \mu_d=\mathbb E F_d,\qquad k\ge1.
```

Suppose a common local reverse-variance constant $\eta>0$ applies at all
depths, and the mean changes by at least $1/2$ between $a<b$, with
$b-a\le P$. Lean proves that, for every chosen $R\ge0$, there exists
$a<d_*\le b$ such that

```math
\mathrm{Var}(F_{d_*+r})\ge\frac{\eta\kappa^R}{4P^2},
\qquad 0\le r\le R,\qquad \kappa=\frac{\eta}{1+\eta}.
```

Thus an interval of $R+1$ consecutive depths lies inside
$\{a+1,\ldots,b+R\}$ and satisfies this lower bound. If $R$ is fixed,
$\eta$ is independent of system size, and $P\le p(n)$ for a fixed
polynomial, the lower bound is inverse-polynomial in $n$.
`theorem_VI_14_family` proves these family quantifiers explicitly.
The quantitative bound accepts arbitrary supplied $R$; the named
asymptotic family theorem takes $R$ fixed.

The final spatial Haar realization proves the uniform local coefficient
$\eta=4^{-8k|S|}$, where $S$ supports $B$. The coefficient is independent
of ambient dimension and inactive-gate count when $k$ and $|S|$ are fixed.

## The proof in four steps

| Step | Mathematical role | Formal source |
| :--- | :--- | :--- |
| **1. Certify mean change** | Spatial separation gives an early mean of one. The proved small Haar mean and supplied late moment control give a gap of at least $1/2$. | [SpatialHaarFinal.lean](../../Fluctuations/SpatialHaarFinal.lean); [Haar mean guide](../reference/haar-mean.md) |
| **2. Bound local reverse variance** | Only a bounded active patch changes the observable; for Haar gates its explicit coefficient is proved. | [CircuitGeometry.lean](../../Fluctuations/CircuitGeometry.lean), [ExplicitHaarVariance.lean](../../Fluctuations/ExplicitHaarVariance.lean) |
| **3. Turn slope into variance** | Some layer changes the mean by at least $1/(2P)$; total variance gives a lower bound $\eta/(4P^2)$. | [Probability.lean](../../Fluctuations/Probability.lean), [Window.lean](../../Fluctuations/Window.lean) |
| **4. Propagate forward** | Each additional depth retains at least a factor $\kappa$ of the variance. | [WeightedVariance.lean](../../Fluctuations/WeightedVariance.lean), [Main.lean](../../Fluctuations/Main.lean) |

The abstract theorem in `Main.lean` assumes mean change and local reverse
variance. The concrete theorem in `SpatialHaarFinal.lean` proves geometry,
the Haar coefficient, the early identity, and global Haar smallness. Its
remaining analytic inputs are late design mean control and transition width;
its architecture and observable conditions remain explicit.

## Which theorem to read

| Declaration | Scope |
| --- | --- |
| `theorem_VI_14`, `theorem_VI_14_interval`, `theorem_VI_14_family` in [Main.lean](../../Fluctuations/Main.lean) | Abstract lower bound, consecutive interval, and polynomial-family quantifiers, assuming mean change and local reverse variance. |
| `spatialHaarCircuit_allOrders_of_globalHaar_control` in [SpatialHaarFinal.lean](../../Fluctuations/SpatialHaarFinal.lean) | Final theorem: geometry, explicit local coefficient, and actual Haar smallness are proved; design control and width remain inputs. |
| `spatialHaarCircuit_firstOrder_of_globalHaar_control` in [SpatialHaarFirstOrder.lean](../../Fluctuations/SpatialHaarFirstOrder.lean) | First-order refinement using the exact Haar mean, for at least two qubits. |
| `spatialHaarCircuit_of_globalHaar_control` in [SpatialHaarTheorem.lean](../../Fluctuations/SpatialHaarTheorem.lean) | Intermediate theorem retaining both quarter-unit estimates as inputs. |
| `spatialHaarCircuit_variance_window` in [SpatialHaarTheorem.lean](../../Fluctuations/SpatialHaarTheorem.lean) | The same spatial numerical window with a supplied half-unit endpoint gap. |
| `activeHaarCircuit_explicit_variance_window` in [ExplicitHaarCircuit.lean](../../Fluctuations/ExplicitHaarCircuit.lean) | Arbitrary unital star-algebra embeddings with inactive commutation and endpoint gap supplied; coefficient $4^{-8km}$. |
| `haarLocalOTOC_explicit_conditional_reverseVariance` in [ExplicitHaarVariance.lean](../../Fluctuations/ExplicitHaarVariance.lean) | The genuine conditional local inequality for a continuous earlier circuit and an independent Haar block. |
| `backwardActiveGateCount_le` in [CircuitGeometry.lean](../../Fluctuations/CircuitGeometry.lean) | Architecture-only bound on total active gates in a finite block, allowing varying layer counts. |

## The general spatial circuit and its observable

For a finite set of sites, the computational basis is `Site → Fin 2`, so the
global matrix dimension is $2^{|\mathrm{Site}|}$.
[TensorSupport.lean](../../Fluctuations/TensorSupport.lean) defines a tensor matrix
by its entries:

```math
T(Q)_{x,y}=\prod_{s\in\mathrm{Site}}Q_s(x_s,y_s).
```

`Supported S B` means that $B$ belongs to the complex algebra generated by
these tensors with $Q_s=I$ outside $S$. This is a definition using actual
matrix entries. The theorem that disjoint supports commute is proved from
tensor multiplication, rather than included in the definition.

[PatchEmbedding.lean](../../Fluctuations/PatchEmbedding.lean) constructs the
canonical insertion of an arbitrary patch matrix: tensor with the spectator
identity and reindex to the global computational basis. The insertion is an
injective unital complex star-algebra homomorphism and has the claimed support.
A patch containing two sites has four basis states and therefore accepts an
actual SU(4) gate through `twoQubitPatchEmbedding`.

At depth $d$, the spatial model has $m$ active and $q$ inactive two-site patches.
All patches in that layer are pairwise disjoint. Active patches meet a fixed
support bound $S$ for $B$; inactive patches are disjoint from $S$. Patch
positions may vary with depth. Every gate is sampled independently from
normalized Haar SU(4), independently also of earlier layers.

Write $A_d$ and $J_d$ for the ordered active and inactive products. The full
circuit and observable are

```math
U_0=I,\qquad U_{d+1}=(J_dA_d)U_d,\qquad
F_d=\mathrm{Tr}\!\left[\rho(U_d^\dagger B U_dM)^{2k}\right].
```

[ActiveHaarCircuit.lean](../../Fluctuations/ActiveHaarCircuit.lean) retains both
products in the circuit and its independent product history. Different depths
have their own finite history spaces; [HaarProcess.lean](../../Fluctuations/HaarProcess.lean)
relates successive spaces by product-measure identities.

The general spatial Haar theorem fixes $m,q$ within a circuit model. They may vary
between system sizes. The more general finite-layer geometry below also allows
the number of gates to vary between layers; this generality should not be
confused with a depth-dependent sampling model in the integrated theorem.

## Geometry supplies the local certificates

Since each inactive patch is disjoint from $S$, its embedded gate commutes
with $B$. Unitarity gives

```math
J_d^\dagger BJ_d=B,\qquad
(J_dA_d)^\dagger B(J_dA_d)=A_d^\dagger BA_d.
```

Thus fresh inactive gates do not affect $F_{d+1}$ when the earlier circuit is
fixed, and integrating them out leaves the active-block constant unchanged.
They remain in $U_{d+1}$ and can influence later layers.
[SpatialSupport.lean](../../Fluctuations/SpatialSupport.lean) also proves that an
interleaved layer can be regrouped while preserving each sublist's order.
For spatially disjoint patches, support supplies its cross-commutation premise.

[CircuitGeometry.lean](../../Fluctuations/CircuitGeometry.lean) defines the active
patches relative to a support $S$ as those meeting $S$, and defines the
one-layer pullback by

```math
\mathcal P_L(S)=S\cup\bigcup_{i:\,P_i\cap S\ne\varnothing}P_i.
```

It proves that conjugating any observable supported in $S$ through the full
layer gives an observable supported in $\mathcal P_L(S)$. Every active patch
contains a different site of $S$, so the number of active gates is at most
$|S|$. If each patch has at most $r$ sites, a block of $\ell$ layers obeys

```math
|\mathsf{LC}_{\ell}(S)|\leq(r+1)^{\ell}|S|,\qquad
N_{\rm active}\leq\ell(r+1)^{\ell}|S|.
```

These bounds are deliberately simple. For fixed depth, patch size, and initial
support size, they are independent of the total number of qubits.

[SpatialHaarGeometry.lean](../../Fluctuations/SpatialHaarGeometry.lean) connects
this propagation theorem to the actual sampled `activeHaarCircuitMatrix`.
Its recursion is

```math
\mathsf{LC}_0(S)=S,\qquad
\mathsf{LC}_{d+1}(S)=\mathsf{LC}_d(\mathcal P_{L_d}(S)).
```

The newest layer acts first in Heisenberg evolution, matching the circuit
ordering above. These cones are monotone in support and depth. If
$\mathsf{LC}_a(S)$ is disjoint from a support $T$ of $M$, the evolved $B$
commutes with $M$ for every sampled history.

The general cone is a proved support bound, without a minimality or universal
graph-distance claim. Separately, the specialized endpoint pipeline proves
its finite one-dimensional walk and the exact pre-light-cone mean.

## Why the constant is exactly $4^{-8km}$

Fix the earlier full circuit $V$, and let $W(h)$ be the ordered product of the
$m$ fresh active gates. The local function is

```math
f_V(h)=\mathrm{Tr}\!\left[
\rho\bigl(V^\dagger W(h)^\dagger B W(h)VM\bigr)^{2k}\right].
```

[BalancedHaarFeatures.lean](../../Fluctuations/BalancedHaarFeatures.lean) tracks
the degree separately in every gate. A word contributing to an entry of $W$
chooses one of $16$ matrix entries from each gate, giving $16^m$ word indices.
Pairing a word with a conjugated word gives $16^{2m}$ balanced feature indices.
The actual OTOC lies in their degree-$2k$ span, whose dimension is at most

```math
(16^{2m})^{2k}=4^{8km}.
```

All observable matrices, embedding coefficients, and spectator dimensions
affect coefficients in this span, rather than its dimension bound. The space
is invariant under left translation on the product group SU(4)$^m$.

[HaarEvaluationBound.lean](../../Fluctuations/HaarEvaluationBound.lean) proves
that a finite-dimensional translation-invariant space $\mathcal S$ of
continuous functions under normalized Haar measure satisfies

```math
|f(x)|^2\leq\dim(\mathcal S)\int|f|^2.
```

The proof uses the constant diagonal of the evaluation kernel. Applying it to
the centered image of $\mathcal S$, whose dimension cannot increase, bounds
$|\mathbb Ef-f(e)|^2$ by $\dim(\mathcal S)\mathrm{Var}(f)$.
[ExplicitHaarVariance.lean](../../Fluctuations/ExplicitHaarVariance.lean) therefore
proves

```math
\mathrm{Var}(f_V)\geq
\underbrace{4^{-8km}}_{\eta(m,k)}
\left|\mathbb Ef_V-f_V(e)\right|^2.
```

The embeddings preserve identity, so $f_V(e)$ is the earlier OTOC. The same
inequality is proved for genuine conditional variance under the independent
product law. Continuity, integrability, function-space membership, and the
evaluation bound are proved ingredients, rather than additional assumptions
of the circuit theorem.

This obtains the manuscript's numerical coefficient by invariant evaluation;
it does not formalize the manuscript's decomposition into irreducible
representations. The older unspecified positive-constant result in
[FiniteDimensionalVariance.lean](../../Fluctuations/FiniteDimensionalVariance.lean)
remains useful for more general full-support measures.

## From mean control to a variance window

Assume $\mathrm{Tr}\rho=1$, $B^2=M^2=I$, and spatial separation of the
cone and probe at depth $a$. Unitary conjugation preserves the involution
relation. The product of the two commuting involutions has every even power
equal to $I$, so $F_a=1$ pointwise and $\mathbb EF_a=1$.

[GlobalHaarMean.lean](../../Fluctuations/GlobalHaarMean.lean) defines the genuine
normalized Haar law on the full global unitary group and the reference

```math
h_{\rho,B,M,k}=\int_{U(2^{|\mathrm{Site}|})}
\mathrm{Tr}\!\left[\rho(U^\dagger BUM)^{2k}\right]\,dU.
```

The general spatial wrapper assumes the first bound below and proves the second:

```math
|\mathbb EF_b-h_{\rho,B,M,k}|\leq\frac14,\qquad
|h_{\rho,B,M,k}|\leq\frac14.
```

The triangle inequality then proves
$|\mathbb EF_b-\mathbb EF_a|\geq1/2$. The first bound is observable-specific
moment control. The second follows from the all-orders Haar calculation described below.
No Haar-smallness hypothesis remains in the final wrapper.

[ExplicitHaarCircuit.lean](../../Fluctuations/ExplicitHaarCircuit.lean) combines
the local result with total variance and the weighted-square inequality. For
$\mu_d=\mathbb EF_d$ and $V_d=\mathrm{Var}(F_d)$, it proves

```math
V_{d+1}\geq\eta|\mu_{d+1}-\mu_d|^2,\qquad
V_{d+1}\geq\kappa V_d,\qquad \kappa=\frac{\eta}{1+\eta}.
```

An endpoint gap forces one sufficiently large mean increment. Consequently,
if $a<b$ and $b-a\leq P$, there is $a<d_*\leq b$ such that for every
$0\leq j\leq R$,

```math
V_{d_*+j}\geq\frac{\eta\kappa^R}{4P^2}.
```

The interval has $R+1$ consecutive depths and lies between $a+1$ and $b+R$.
Since spatial disjointness proves $m\leq|S|$, the final spatial theorem uses
the common coefficient $\eta_S=4^{-8k|S|}$. This coefficient is independent of
the total qubit count and $q$. For uniformly bounded $|S|$, fixed $k,R$, and a
polynomial width bound, the displayed result gives an inverse-polynomial
lower bound. This conclusion requires those uniformity conditions.

## The actual global-Haar calculation

The [supporting Haar mean guide](../reference/haar-mean.md) explains the actual U($D$)
integral, state independence, inverse-Gram expansion, all-dimension estimate,
and exact first-order value. This is the ingredient corresponding to
`prop:haar-otock-small` in the manuscript’s preliminaries. Its proved
quarter-bound supplies mean separation in the argument above.

## Scope relative to the manuscript

The local numerical Haar inequality, physical embeddings, geometric
commutation, active-count bounds, early identity, actual Haar smallness in the
full dimension range, and variance-window deduction are proved. The final
spatial theorem retains design control and transition width as intended
external inputs. Its physical, support, and separation assumptions are visible
in the statement. The Haar estimate is uniform in both the state and the
dimension, with a constant depending only on the fixed order.

The general spatial local law is SU(4); equivalence with the manuscript's
U(4) sampling for phase-insensitive OTOCs has not been separately formalized
for that pipeline. Its circuit fixes active and inactive counts across depth,
while the deterministic geometry permits variable counts. The endpoint
pipeline uses U(4) directly and represents the actual alternating gate counts.

The next [OTOC₁ guide](02-otoc1-fluctuations.md) records the sharper
one-dimensional results and the exact limits of that formalization.
General graph-distance asymptotics, non-Haar ensemble criteria, and
computational quantum advantage also remain separate claims.

---

**Continue with the paper:** [2. One-dimensional OTOC₁ →](02-otoc1-fluctuations.md)

**Supporting reference:** [Global Haar mean](../reference/haar-mean.md) · [Assumptions](../reviews/assumptions.md) · [Paper map](../reference/paper-map.md)
