# Independent review · Classical simulation

[Home](../../README.md) / [Reader guide](../README.md) / Simulation review

This review compares the statements in [`Simulation.lean`](../../Fluctuations/Simulation.lean) with the manuscript theorem `thm:endpoint-sim-otoc1-runtime` and its conditional-sampling algorithm. The mathematical scope agrees: an infinite-temperature first-order endpoint OTOC, independent Haar U(4) gates, an open one-dimensional brickwork circuit, and the critical depth. The probability includes both the random input circuit and the sampler's randomness.

## The verified statement in English

For every integer `s ≥ 0`, set `n = 6(s+1)` and `d = 10(s+1) = 5n/3`. Thus every positive multiple of six is included. Draw each actual two-qubit gate independently from normalized Haar measure on U(4), and form the circuit in the manuscript's chronological convention. For this realized circuit, the target is the literal normalized quantum trace

```math
F_\infty(U)=2^{-n}\mathrm{Tr}[(U^\dagger Z_1 U Z_n)^2].
```

For any real `0 < ε < 1` and `0 < δ < 1`, choose exactly

```math
R=10\sqrt{\log\frac{400n^2}{3\varepsilon\delta}},\qquad
N=\left\lceil\frac8{\varepsilon^2}\log\frac4\delta\right\rceil.
```

Keep the gates in the manuscript's causal, parity-respecting diffusive eye and average all other gates. The proved sampler processes the outside gates first within each layer, uses conditional Pauli amplitudes, and draws `N` independent final Pauli strings. It returns the average of their endpoint signs: `+1` for I or Z at the last qubit, and `−1` for X or Y.

The theorem `otoc1_subexponential_simulation` proves that this estimator differs from the actual quantum trace by at most `ε` with joint probability at least `1−δ`. For the same physical schedule, its formal arithmetic counter is at most

```math
180002(N+1)n^2\,4^{2W+4},\qquad
W=\left\lceil 2R\sqrt n+1\right\rceil.
```

No mean-change, reverse-variance, tail, approximation-error, or coherent-width estimate is supplied as an assumption of this theorem.

The second final theorem, `otoc1_subexponential_simulation_inversePolynomial`, fixes any positive natural exponents `a,b`, sets `ε=n^{-a}` and `δ=n^{-b}`, and combines the success statement at every allowed size with

```math
\lim_{s\to\infty}\frac{\log(\mathrm{work}(s))}{6(s+1)}=0.
```

This is an explicit subexponential assertion about the generated schedule's arithmetic counter. The separate explicit envelope in [`SimulationAsymptotics.lean`](../../Fluctuations/SimulationAsymptotics.lean) is a polynomial times an exponential of a constant times `√(n log n)`. The general ceiling-dependent bound above also implies the manuscript's displayed dependence on `ε` and `δ`; the final theorem uses that explicit bound rather than big-O notation.

## Correspondence checks

| Manuscript ingredient | Checked Lean correspondence |
| --- | --- |
| Actual endpoint OTOC | `simulationCriticalOTOC` uses the normalized complex quantum trace and the actual embedded-gate circuit. `simulationCircuitOTOC_eq_trace` proves equality with the real Pauli-sign readout. |
| Joint probability | `simulationCriticalSuccessProbability` is the full product Haar measure followed by the actual physical sampler kernel. Samples are conditionally independent given the circuit. |
| Retained eye | `simulationRetainedGate` and `simulationRetainedSchedule` use exactly `simulationEyePositions`, including physical gate parity, both causal inequalities, and exclusion of the last layer. The runtime and accuracy results use this same eye. |
| Endpoint upper tail | `simulationEndpointTail_binomial` derives the binomial-CDF upper comparison for the finite reflecting chain, including both boundaries. `simulationBinomialCDF_odd_center` proves the left-boundary comparison. |
| Forward and backward touching | `simulationForwardTouch_gaussian` and `simulationBackwardTouch_gaussian` give the `5/2`, `200` Gaussian bound for the actual physical prefixes. Haar coordinate extraction and inversion are proved measure preserving. |
| Reverse-time convention | The strictly later gates are reversed and inverted. The final even layer is proved idle for the endpoint probe; the physical virtual time is exactly `d−t` and the reflected position is `n−ℓ`. Same-layer disjoint gates are explicitly accounted for. |
| Averaging error | `simulationEye_bias` proves the actual full-circuit integral `E|F−F̂_R| ≤ (100/3)n² exp(−R²/100)`. Exact causal zeros and the Gaussian estimate imply the per-erased-gate bound, and product averaging supplies the telescope. |
| Exact conditional sampler | The full coefficient covariance is preserved, including off-diagonal terms required by later retained gates. The sampler's output law equals the conditional Haar-averaged Pauli law. |
| Outside-first implementation | `simulationPhysicalSamplerKernel_eq` identifies the reordered physical implementation with the kernel used in the accuracy proof. Disjoint-gate covariance commutation justifies the reordering. |
| Coherent width | Every realizable branch has the stated classical/coherent representation. At a layer boundary there are at most `2W+2` coherent sites; every generated local call has at most `2W+4`. Each local call contains both distinct gate sites, so the spectator exponent `m−2` is justified. |
| Concentration and parameter choice | Markov's inequality controls the circuit-averaging error, bounded independent-sign concentration controls sampling error, and the stated `R,N` make their sum at most `δ`. |

The critical-depth and infinite-temperature restrictions are substantive. This theorem does not state a simulator at arbitrary depth or for arbitrary input density matrices, and its success guarantee is averaged over Haar input circuits rather than a worst-case guarantee for every fixed circuit. These restrictions agree with the reviewed manuscript theorem.

## Arithmetic model and verification boundary

The cost model charges scalar additions, multiplications, divisions, square roots, local transfer-matrix construction, and exact draws from explicitly computed finite distributions. A complex scalar operation in transfer-matrix construction costs one unit; the stored Pauli amplitudes and their vector updates are real. Expressing every complex operation using only real primitives changes constant factors, not the asymptotic bound. Indexing and reading coefficients are free in this arithmetic model. This agrees with the paper's finite-distribution-sampling assumption. It is not a claim about bit complexity, numerical stability, finite precision, or the runtime of a compiled executable.

The formal cost is a symbolic counter for the exact local formulas and the generated coherent-support schedule. Retained gates apply a 16-by-16 transform to each spectator slice. Outside gates compute the 16 input marginals, draw the local input and output labels, and normalize the chosen spectator vector. These operations do not construct a mixed density matrix or enumerate the classical coordinates in their arithmetic loops. The explicit cost formulas count `31·16·spectators` operations for a retained vector update and `33·spectators+3` for an averaged update, in addition to the fixed transfer-construction cost where applicable.

The separate one-time construction of the eye and evaluation of the parameter formulas are not represented in `simulationCriticalWork`. That polynomial overhead does not affect the subexponential asymptotic conclusion; the displayed explicit counter should be read with its stated scope. The repository provides mathematical Lean definitions and proofs, not an extracted practical simulator.

## Validation status

The final simulation module has compiled locally. The tail, Haar-expectation, causal-zero, outside-eye, and full-bias theorem audit reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. For the repository-wide build and validation record, see [verification record](../verification/record.txt). This independent review records the statements and theorem audits rather than duplicating that build status.

The independent source review of [`SimulationCompressedOperations.lean`](../../Fluctuations/SimulationCompressedOperations.lean), [`SimulationGeometrySampler.lean`](../../Fluctuations/SimulationGeometrySampler.lean), and [`SimulationGeometryCost.lean`](../../Fluctuations/SimulationGeometryCost.lean) found no discrepancy in the compressed-operation correspondence. The fixed update, input marginals, branch weights, and positive-marginal normalized branch all inflate to the exact full-space formulas. Adding classical sites is an explicit indexing-and-zero operation. The spectator cardinal is exactly `4^(m−2)`, with two distinct included gate sites, and the final squared array gives the correct categorical output. Zero-marginal fallbacks have zero branch probability and are not charged as realizable trajectories.

The final accuracy, combined accuracy/work, inverse-polynomial subexponential, physical-law, support-width, and cost declarations were also independently loaded and audited. All reported only `propext`, `Classical.choice`, and `Quot.sound`. The ten principal compressed-operation identities were also independently loaded and audited, with the same three standard axioms and no additional assumptions. No correspondence defect was found in the reviewed statements or operation formulas.

---

**Related:** [Simulation result guide](../results/03-classical-simulation.md) · [All assumptions](assumptions.md) · [Reproduce the checks](../verification/README.md)
