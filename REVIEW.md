# Reviewing the formalization

[Overview](README.md) · [Guide](docs/guide.md) · [Paper map](docs/paper-mapping.md)

Start with the [OTOC(1) guide](docs/otoc1.md),
[OTOC1.lean](Fluctuations/OTOC1.lean), and its
[earlier independent scope review](docs/otoc1-review.md). That review covers
the fluctuation and mean results and predates the simulation extension.
For the latter, start with [Simulation.lean](Fluctuations/Simulation.lean)
and the [simulation guide](docs/simulation.md). The general spatial result
remains in [SpatialHaarFinal.lean](Fluctuations/SpatialHaarFinal.lean).
Review mathematical assumptions separately from successful compilation.

## Main statements

| Declaration | Assumptions that remain |
| --- | --- |
| `otoc1_subexponential_simulation` | Actual open Haar U(4) brickwork, `n = 6(s+1)`, `d = 10(s+1)`, infinite-temperature normalized trace, and `epsilon, delta` in `(0,1)`. The bias, sampler law and joint success bound are proved. |
| `otoc1_subexponential_simulation_inversePolynomial` | Fixed positive natural exponents `a,b`, with `epsilon = n^-a`, `delta = n^-b`: joint accuracy at every size and `log(work)/n -> 0` for the same physical sampler. Exact arithmetic and finite-distribution sampling are the operation model. |
| `otoc1_endpoint_variance_lower` | Concrete open 1D brickwork circuit, fixed front width `C ≥ 0`, explicit largeness and front-window inequalities, and `trace ρ = 1` |
| `otoc1_endpoint_gate_influence`, `otoc1_many_influential_gates` | Same hypotheses; the first theorem specifies a gate in the actual central eye. Conditional means, eye count and influence bounds are proved. |
| `brickworkEndpointOTOC_conditional_mean` | Trace normalization and an interior even gate with a later odd layer; the exact actual Haar conditional formula is proved. |
| `brickworkEndpointOTOC_haar_mean` | Trace normalization; all even sizes and depths, including boundary cases |
| `spatialHaarCircuit_variance_window` | A parallel architecture of disjoint two-site patches, observable support, correct active/inactive classification, half-unit endpoint mean change, and transition width |
| `spatialHaarCircuit_allOrders_of_globalHaar_control` | Same geometry, Hermitian traceless involutions, trace normalization, early cone separation, explicit dimension threshold, late moment error at most $1/4$, and width; Haar smallness is proved |
| `spatialHaarCircuit_firstOrder_of_globalHaar_control` | First-order specialization with traceless involutions and at least two qubits; no Hermiticity premise is required |
| `spatialHaarCircuit_of_globalHaar_control` | Reusable intermediate theorem that intentionally accepts a Haar quarter-bound |
| `haarLocalOTOC_explicit_reverseVariance_identity` | Linear gate insertions preserving identity; arbitrary finite ambient matrices. The exact local coefficient is proved, not supplied. |
| `haarLocalOTOC_explicit_conditional_reverseVariance` | Independent Haar block and continuous earlier circuit; proves the actual conditional inequality |
| `theorem_VI_14_family` | General probability model with a supplied common local constant, mean change, and polynomial width |

## Endpoint circuit correspondence

The endpoint observable is exactly $\mathrm{Tr}[\rho(U^\dagger Z_1UZ_n)^2]$.
`BrickworkSite r` has $n=2(r+1)$ sites; `T` periods give $d=2T$ layers and
$T(2r+1)$ independent Haar U(4) coordinates. The chronological recursion is
$U_{j+1}=U_jG_j$, matching the manuscript's $L_1\cdots L_d$ convention.
The final theorem uses `r=c+1` and the explicit threshold
$\sqrt n\ge12(C+2)$. Its positive constant depends only on `C`.

Inspect `PauliCircuitBridge` and `PauliFrozenCircuit`: the Pauli expansion is
an operator identity, mixed Haar moments are derived, and the frozen-gate
covariance retains off-diagonal terms until a later full odd layer removes
them. `EndpointLumpability` proves endpoint closure for arbitrary correlated
weights. It does not assume that the fixed gate restores the full shock law.
The final even layer, the other gates in the fixed matching, and the exact
$-16/15$ conditional coefficient are included.

`CoordinateAverages` identifies the actual integral over all other gate
coordinates with conditional expectation. `GateInfluence` derives the
variance-sum inequality from the product law. No conditional-mean,
independence, propagation, gate-count, or design-convergence premise remains
in the final endpoint theorem. The cardinality upper bound concerns the
constructed gate set, not all potentially influential gates.

## Simulation correspondence and cost model

The simulation target is the actual normalized matrix trace
$F_\infty=2^{-n}\mathrm{Tr}[(U^\dagger Z_1UZ_n)^2]$, so it specializes
to the maximally mixed state. Its probability guarantee averages over both
the realized Haar circuit and the conditional algorithmic randomness. It is
not a worst-case guarantee for every fixed gate realization.

The local replacement proof uses the squared Pauli mass touching a gate,
from either the forward butterfly or the backward probe. The proved endpoint
tail bound controls the enlarged eye's discarded gates. A telescoping
product-average argument gives the bias estimate, and the exact choices of
`R,N` allocate at most `delta/2` to each error. The final probability is
measured under the actual composition-product law `mu ⊗ₘ kappa`; it is not
an informal sum of conditional failure probabilities.

Inspect the full-covariance sampler invariant. Averaged gates sample an
input pair and an output pair from the Haar Pauli kernel, while retaining
the conditional coherent vector on the spectator sites. Subsequent retained
gates therefore receive the necessary off-diagonal moments. Zero-probability
branches have a normalized fallback; support statements concern branches
with nonzero weight. The exponentially large finite ensemble is a semantic
law, not an array that the implementation constructs.

[SimulationPhysicalLaw.lean](Fluctuations/SimulationPhysicalLaw.lean) identifies
the output PMF of the outside-first implementation with the chronological
mixed-circuit law for every realized input. Its `simulationPhysicalSamplerKernel`
is the actual Markov kernel used in the final joint probability statement.
This connects correctness and resource bounds for the same sampler.

The physical outside-first ordering is justified by disjoint gate
commutation. The support and cost modules track those same gate lists:
there are at most `2W+2` coherent sites at a layer end and `2W+4` during a
local update. Each actual call has at least two sites, and
`16 * 4^(m-2) = 4^m` is proved. Costs count local matrix multiplication,
marginals, branch normalization, and the final finite draw on this dense
vector, including transfer-matrix construction.

`otoc1_subexponential_simulation_inversePolynomial` combines the accuracy
guarantee at every size with the limit `log(work)/n -> 0` for the same
physical sampler, using fixed positive natural exponents.
`SimulationAsymptotics.lean` supplies the explicit majorant and limit;
the parameter-dependent bound in `R,N` is available separately.

The counter covers sampling and readout arithmetic, including local
transfer-matrix construction. Indexing, reads of stored coefficients, and
preprocessing to construct the schedule or compute its parameters are not
counted. Exact scalar arithmetic (real or complex) and exact finite sampling are assumed as in the
paper. The formalization does not supply an extracted numerical executable,
a finite-precision analysis, or a bit-complexity bound.

## General spatial geometry and physical meaning

`QubitState Site` is the computational basis `Site → Fin 2`. `Supported S A`
is defined by the algebra generated by actual tensor matrices that are identity
off $S$; commutation is a theorem. `patchEmbedding` is an injective unital
star-algebra homomorphism. `twoQubitPatchEmbedding` identifies a two-site
patch's four basis states with a genuine SU(4) matrix.

Check the recursion $U_{d+1}=(J_dA_d)U_d$. Inactive gates remain in the full
history. Disjoint supports prove their commutation with $B$ and the cross
commutation needed to regroup a layer. The deterministic cone processes the
newest layer first, matching Heisenberg conjugation. Disjointness of that cone
from $M$ supplies early commutation for every sampled history.

Pairwise disjoint patches meeting $S$ have count at most $|S|$. A block of $t$
layers with patches of at most $r$ sites has cone size at most
$(r+1)^t|S|$ and active count at most $t(r+1)^t|S|$. These deliberately coarse
bounds are uniform in the ambient system size.

The general spatial Haar process fixes $m,q$ across depths. The deterministic
geometry admits variable counts, but a general varying-count Haar history and
its measure reindexing are not yet assembled. The SU(4)-to-U(4) phase/Haar-law
bridge and general graph-distance/lattice estimates also remain correspondence
work for this pipeline. The endpoint pipeline samples U(4) directly.

## The numerical constant

`haar_subspace_reverseVariance` bounds centered evaluation by `finrank` times
variance for a finite-dimensional translation-invariant continuous-function
space under Haar probability. Centering is handled by a linear image, without
assuming that the original space contains constants.

`BalancedHaarFeatures.lean` proves actual OTOC membership, translation stability,
and the bound `finrank ≤ 4^(8*k*m)`. It does not use the older, larger raw
feature count. `ExplicitHaarVariance.lean` therefore proves
$\eta=4^{-8km}$, including the identity-value and conditional forms.
The spatial theorem weakens this to $4^{-8k|S|}$ using the proved active count.

## The mean assumption boundary

`globalHaarOTOCMean` is the actual normalized U($D$) Haar integral of the same
matrix OTOC. The final theorem proves, for every $k>0$ and $D\ge1$,

```math
|h_{\rho,B,M,k}|\le\frac{2((2k)!)^3}{D^2}.
```

Here $B,M$ are Hermitian traceless involutions and $\mathrm{Tr}\rho=1$.
The result is uniform in the state; positivity of $\rho$ is not needed.
The additional threshold $D^2\ge8((2k)!)^3$ gives the quarter-bound.
For $D<2(2k)!$, a proved unit bound absorbs the smaller dimensions into
the same constant. At $k=1$ a separate exact proof gives $-1/(D^2-1)$.

Inspect the complete chain: tensor-power commutants are spanned by permutation
operators; actual Haar averaging preserves the relevant trace pairings; the
permutation Gram matrix is inverted; the cyclic OTOC trace is contracted; and
the finite sum is bounded. No integration formula, coefficient bound, or
state-independence conclusion is a premise of the final mean theorem.

The permutation matrices use an anti-representation convention:
$P_\sigma P_\tau=P_{\tau\sigma}$. The final sum explicitly reindexes this
to the paper's coefficient argument; check `weingarten_contraction_sum_eq`.

The earlier generic combinatorial transfer lemmas intentionally retain
coefficient/identity hypotheses. The final concrete theorem discharges them.
Likewise `hsmall` remains in a reusable intermediate spatial theorem but is
absent from the all-orders wrapper.

Design convergence and the width bound remain external inputs of the general
spatial theorem. They are absent from the proved endpoint fluctuation theorem.
The exact endpoint mean is proved in matrix-power and finite binomial-image
forms. Literal manuscript $\Psi$ regrouping, its Gaussian mean-front error
estimate and the full outer variance-influence envelope remain outside the
formalized results. The simulation uses separate endpoint touching-tail and
local-replacement bounds; these do not prove those omitted Gaussian
statements. Computational quantum advantage is also a separate claim.

## Verification

Run `bash scripts/check.sh` after obtaining the pinned dependencies. The audit
checks the listed endpoint variance, influence, conditional-mean, actual
mean and simulation results, the general spatial/Haar results, and their
transitive dependencies; only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. It rejects missing
reports and additional axioms. See [the reproduction guide](docs/reproduce.md).
Match the checked revision to the source being reviewed.

