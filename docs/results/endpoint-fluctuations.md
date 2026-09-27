# Endpoint OTOC fluctuations

[Home](../../README.md) / [Reader guide](../README.md) / Endpoint fluctuations

The entry point is [OTOC1.lean](../../Fluctuations/OTOC1.lean). It formalizes the
paper's **macroscopic origin of OTOC fluctuations** theorem: the variance
lower bound throughout a diffusive front window, and the many individual
gate contributions that produce it. The actual finite-circuit Haar mean is
proved in [BrickworkEndpointMean.lean](../../Fluctuations/BrickworkEndpointMean.lean).
See the [earlier independent scope review](../reviews/endpoint.md) for these
fluctuation and mean results. It predates the subsequent
[classical simulation extension](classical-simulation.md).

## The precise mathematical statement

Take an open chain of even length $n$ and an even depth $d$. Odd layers act
on $(1,2),(3,4),\ldots$; even layers act on $(2,3),(4,5),\ldots$. Every
gate is independently sampled from normalized Haar measure on U(4).
The chronological product is $U_d=L_1\cdots L_d$, and

```math
X_\rho(U_d)=\mathrm{Tr}\!\left[\rho(U_d^\dagger Z_1U_dZ_n)^2\right].
```

For any fixed $C\ge0$, assume

```math
\left|d-\frac{5n}{3}\right|\le C\sqrt n,
\qquad \sqrt n\ge12(C+2),\qquad \mathrm{Tr}\rho=1.
```

Define the fixed two-qubit Haar variance $\sigma_A^2=\mathrm{Var}(A)$,
where $A$ is exactly the local observable in the manuscript. Lean proves
$\sigma_A^2>0$ and $\mathbb EA=4/5$. Put

```math
q_C=\frac{\exp[-2-25(C+2)^2]}6,
\qquad b_C=\frac{256}{225}\sigma_A^2q_C^4>0.
```

Then `otoc1_endpoint_variance_lower` proves

```math
\mathrm{Var}(X_\rho)\ge\frac{b_C}{24\sqrt n}.
```

The variance convention is $\mathbb E|X-\mathbb EX|^2$, allowing a complex
OTOC. The theorem holds for every trace-one matrix $\rho$, hence in
particular for every density matrix. The constants above are deliberately
not optimized. There is **no mean-change or design-convergence hypothesis**
in this endpoint theorem.

## Which gates contribute

Write $\Delta=d-5n/3$. The selected even gates satisfy

```math
\frac n3\le\ell\le\frac{2n}3,
\qquad\left|t-\frac{5\ell}3-\frac\Delta2\right|\le\sqrt n.
```

`otoc1_many_influential_gates` constructs their actual finite circuit
indices and proves

```math
\frac{n\sqrt n}{24}\le |\mathcal S|\le\frac{2n\sqrt n}{3},
\qquad
\mathrm{Var}_{G_z}\!\left(\mathbb E_{\ne z}X_\rho\right)
\ge\frac{b_C}{n^2}\quad(z\in\mathcal S).
```

Here $\mathbb E_{\ne z}$ literally integrates every gate other than $z$
under its independent Haar law. The connection to conditional expectation
and the inequality that sums these influences are proved, not hypotheses.
The cardinality upper bound applies to the constructed set; it does not bound
the influence of gates outside that set.

## How the proof is connected

| Step | What is proved | Source |
| --- | --- | --- |
| Physical observable | Actual tensor embeddings, chronological matrix product, and endpoint OTOC | [BrickworkEndpointOTOC.lean](../../Fluctuations/BrickworkEndpointOTOC.lean) |
| Local Haar integration | Full mixed Pauli covariance, uniform nonidentity mixing, $\mathbb EA=4/5$, $\sigma_A^2>0$ | [PauliLocalHaar.lean](../../Fluctuations/PauliLocalHaar.lean), [LocalPauliBalance.lean](../../Fluctuations/LocalPauliBalance.lean) |
| Quantum to classical | Actual Haar integrals and fixed-gate conditional integrals equal their derived Pauli recurrences | [PauliCircuitBridge.lean](../../Fluctuations/PauliCircuitBridge.lean), [PauliFrozenCircuit.lean](../../Fluctuations/PauliFrozenCircuit.lean) |
| Endpoint walk | Forward shock law and universal endpoint evolution, including correlated distributions after a fixed gate | [PauliBrickwork.lean](../../Fluctuations/PauliBrickwork.lean), [EndpointLumpability.lean](../../Fluctuations/EndpointLumpability.lean) |
| Conditional mean | Exact $-(16/15)PF(A-4/5)$ deviation from the full mean, with the entire physical schedule included | [PauliBrickworkConditional.lean](../../Fluctuations/PauliBrickworkConditional.lean), [BrickworkEndpointOTOC.lean](../../Fluctuations/BrickworkEndpointOTOC.lean) |
| Propagation | Exact finite-walk ballot formulas and positive binomial lower bounds derived from Stirling | [EndpointPropagation.lean](../../Fluctuations/EndpointPropagation.lean), [BinomialLocalBounds.lean](../../Fluctuations/BinomialLocalBounds.lean), [EndpointFrontLower.lean](../../Fluctuations/EndpointFrontLower.lean) |
| Count and sum | Actual eye cardinality and the independent-coordinate variance sum | [EndpointPhysicalEye.lean](../../Fluctuations/EndpointPhysicalEye.lean), [CoordinateAverages.lean](../../Fluctuations/CoordinateAverages.lean) |
| Actual mean | Exact quantum Haar mean equals the finite endpoint-chain and binomial-image expressions | [BrickworkEndpointMean.lean](../../Fluctuations/BrickworkEndpointMean.lean) |
| Final theorem | Explicit uniform variance and individual-influence lower bounds | [OTOC1.lean](../../Fluctuations/OTOC1.lean) |

The conditional quantum proof retains off-diagonal Pauli moments created
by the fixed gate. A later complete odd Haar layer removes them. The
classical proof does not assume that the full shock distribution is restored
after a fixed gate: it proves endpoint closure for arbitrary distributions.

## Reading the indices

`BrickworkSite r = Fin (r+1) × Fin 2` describes $r+1$ two-qubit cells.
The basic circuit therefore has $n=2(r+1)$ qubits, $d=2T$ layers, and
$T(2r+1)$ independently sampled gates. The final variance theorem uses
$r=c+1$, so its Lean parameter `c` gives $n=2(c+2)$. This `c : Nat` is a
size index; the real front-window parameter is named `C`.

An even gate `(s,a)` in zero-based Lean coordinates is the manuscript gate
$(\ell,t)=(2(a+1),2(s+1))$. Its independent sample coordinate is
$s(2r+1)+(r+1)+a$. The eye conditions prove that a complete odd layer lies
after every selected gate.

## The actual finite-circuit mean

[BrickworkEndpointMean.lean](../../Fluctuations/BrickworkEndpointMean.lean)
identifies the quantum Haar integral with the finite reflecting endpoint walk.
For $n=2(r+1)$ and positive even depth $d=2T$,

```math
\mathbb E X_\rho=1-\frac{16}{15}(Q_r^{T-1})_{r,0}.
```

Here `endpointMarkov r` is the proved matrix on the $r+1$ endpoint cells,
including both reflecting boundaries. The depth-zero mean is $1$; for two
qubits, every positive even depth has mean $-1/15$. These are actual
quantum-circuit identities, uniform over trace-one $\rho$.

`brickworkEndpointOTOC_haar_mean_images` expands the mean into an exact
finite binomial-image sum, using [EndpointMean.lean](../../Fluctuations/EndpointMean.lean).
The actual pre-light-cone mean is also proved equal to $1$. The image formula
is an alternative exact expression; its algebraic regrouping into the
manuscript's compressed $\Psi_d$ display is not formalized.

## Classical simulation at infinite temperature

[Simulation.lean](../../Fluctuations/Simulation.lean) additionally formalizes
the paper's classical estimator at $n=6(s+1)$ and $d=10(s+1)=5n/3$.
Here the state is fixed to $I/2^n$, giving the normalized trace
$F_\infty=2^{-n}\mathrm{Tr}[(U^\dagger Z_1UZ_n)^2]$.
The algorithm retains an enlarged eye of realized gates and samples the
conditional Pauli distribution while storing a single compressed coherent
vector. Its success probability is at least $1-\delta$ at additive error
$\varepsilon$, over both the Haar circuit and the algorithmic randomness.

The error estimate, exact sampler law, and support and operation counts are
proved. The chosen radius and sample count give subexponential arithmetic
cost. For $\varepsilon=n^{-a}$ and $\delta=n^{-b}$ with fixed positive
natural exponents, `otoc1_subexponential_simulation_inversePolynomial`
combines accuracy at every size with $\log(\mathrm{work})/n\to0$ for the
same sampler. The exact scalar-arithmetic count (real or complex) covers sampling and readout,
including transfer-matrix construction, with exact finite-distribution draws.
It excludes indexing, stored-coefficient reads, and schedule and parameter
preprocessing; an extracted numerical executable and finite-precision or
bit-complexity analyses are not supplied. Read the
[simulation guide](classical-simulation.md) for the precise theorem and operation
model. The simulation guarantee is specifically infinite-temperature; the
fluctuation theorem on this page holds for every trace-one state.

## Scope of the endpoint formalization

The Gaussian mean approximation with error $5/\sqrt n$ and the full spatial
Gaussian variance-influence envelope outside the central eye remain
separate unformalized statements. The simulation uses its own proved
endpoint touching-tail and local-replacement estimates, which are different
from that full influence-envelope claim. The literal $\Psi_d$ regrouping
also remains outside the formalization, as described above.

The higher-order spatial theorem and its design-convergence input remain
documented separately in the [general mathematical guide](spatial-variance.md).

---

**Next:** [Classical simulation](classical-simulation.md) · [Independent endpoint review](../reviews/endpoint.md) · [Paper map](../reference/paper-map.md)
