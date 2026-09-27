# Independent review · Endpoint OTOC fluctuations

[Home](../../README.md) / [Reader guide](../README.md) / Endpoint review

**Scope of this review:** endpoint fluctuations and the exact finite-circuit
mean. It records the review completed before the classical-simulation extension.
See the [separate simulation review](simulation.md) for that theorem and the
[verification record](../verification/record.txt) for repository-wide checks.

The final declarations in [OTOC1.lean](../../Fluctuations/OTOC1.lean) prove the manuscript’s macroscopic-origin variance statement for the actual one-dimensional Haar circuit. No correspondence defect or remaining conditional premise was found in these declarations.

For fixed C ≥ 0, let n = 2(c+2), d = 2T, assume √n ≥ 12(C+2) and |d−5n/3| ≤ C√n. Every gate is independently Haar distributed in U(4), embedded on its stated neighboring qubits. For every matrix ρ with Tr ρ = 1, define X = Tr[ρ(U†Z₁UZₙ)²]. The proved conclusions are:

- Var(X) ≥ K(C)/(24√n).
- The explicitly constructed set of physical even gates has cardinality between n√n/24 and 2n√n/3.
- Each gate G in that set satisfies Var_G(E[X | G]) ≥ K(C)/n².

Here K(C) = (256/225) Var_Haar(A) [exp(−2−25(C+2)²)/6]⁴ is proved strictly positive. It depends only on C, independently of n, d and ρ. Taking C=1 yields the supplementary-material front window, with the sufficient explicit threshold n ≥ 1296. The trace-one hypothesis includes every density matrix and is stronger in scope than the paper requires. Variance means expected squared complex modulus about the mean.

The selected gate set is exactly the central even-coordinate eye n/3 ≤ ℓ ≤ 2n/3 and |t−5ℓ/3−(d−5n/3)/2| ≤ √n, mapped injectively to the actual independent gate coordinates. Its cardinality is proved, as is the existence of a later complete odd layer for every selected gate. The upper cardinality bound concerns this constructed set; it does not assert that all other gates have negligible influence.

The conditional identity is proved for the actual circuit integral, with coefficient −16/15 and past/future powers Q^s and Q^(T−s−2), where the physical gate is at layer 2(s+1). Its exact variance prefactor is 256/225. The proof derives local Haar mixed moments, physical tensor embeddings, finite product integration, the covariance reset after the fixed gate, endpoint propagation for arbitrary correlated Pauli weights, and final-site label averaging. It never assumes that fixing a gate preserves a full shock distribution. The sum of gate conditional variances is bounded by full variance using independence of the actual product coordinates.

The chronological product U_old G_new matches the manuscript convention U_d = L₁…L_d. There is no extra normalized trace, reversed conjugation, or extra OTOC power. The final even layer is included and proved to preserve the last-site readout.

`BrickworkEndpointMean.lean` additionally proves the exact actual Haar mean as a finite reflecting-chain matrix element, an explicit binomial image sum, the pre-light-cone value 1, and the n=2 and depth-zero boundary cases. The literal regrouping into the manuscript’s Ψ_d expression and its Gaussian approximation with error 5/√n are not proved by the reviewed modules. The front-window lower estimates used for the variance theorem are proved independently and do not require that Gaussian approximation. The simulation algorithm and Gaussian influence-tail bounds are also outside these final declarations.

Validation: the final variance, gate-influence, gate-count, conditional-mean, mean, and positive-constant declarations compile and their axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The lower bounds do not claim matching variance upper bounds or higher-order macroscopic gate influence.

---

**Related:** [Endpoint result guide](../results/02-otoc1-fluctuations.md) · [Simulation review](simulation.md) · [All assumptions](assumptions.md)
