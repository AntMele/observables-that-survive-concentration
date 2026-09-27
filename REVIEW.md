# Reviewing the formalization

[Overview](README.md) · [Guide](docs/guide.md) · [Paper map](docs/paper-mapping.md)

Review the formal statement and its physical interpretation as separate checks.
Start with [ActiveHaarCircuit.lean](Fluctuations/ActiveHaarCircuit.lean) for the
strongest full-layer Haar theorem, or [Main.lean](Fluctuations/Main.lean) for the
general probability theorem. Use the [paper map](docs/paper-mapping.md) to check
which manuscript inputs are proved and which remain hypotheses.

## Results and assumption boundaries

| Declaration | Main boundary |
| --- | --- |
| `activeHaarCircuit_theorem_of_moment_control` | Full layers with $m$ active and arbitrary $q$ inactive gates. Derives the half-gap from trace normalization, involutions, early commutation, and two scalar quarter-unit estimates; inactive commutation and width are also inputs. |
| `activeHaarCircuit_theorem_VI_14` | Same full-layer model with a supplied half-unit gap; the positive constant is chosen before $q$, global dimension, and matrix data. |
| `haarCircuit_theorem_VI_14` | Fixed $m$ independent Haar SU(4) gates per step, actual matrix OTOCs, unital star-algebra embeddings; mean gap and width assumed. |
| `haarLocalOTOC_conditional_reverseVariance` | Proves the local conditional inequality for an independent Haar block and continuous earlier circuit. |
| `transition_window` | Arbitrary nonnegative mean gap; local reverse variance and standard probability/integrability structure supplied. |
| `theorem_VI_14` and `theorem_VI_14_interval` | The general uniform bound, plus explicit interval cardinality and location. |
| `theorem_VI_14_family` | General polynomial-family statement with one positive constant chosen before system size. |

## Review the Haar construction

- [HaarSU4.lean](Fluctuations/HaarSU4.lean) uses actual $4\times4$ special
  unitary matrices and normalized product Haar measure. Independence is proved.
- [QubitEmbedding.lean](Fluctuations/QubitEmbedding.lean) proves the genuine
  tensor-with-identity insertion is a unital complex star-algebra homomorphism.
- [LocalPolynomial.lean](Fluctuations/LocalPolynomial.lean) proves actual OTOC
  trace membership in the raw entry/conjugate space of total degree $4mk$.
  Check that the space contains no ambient dimension, embedding, or $\rho,B,V,M$
  parameter; these appear only in coefficients.
- [FiniteDimensionalVariance.lean](Fluctuations/FiniteDimensionalVariance.lean)
  uses compactness and full support to obtain a common positive constant.
- [HaarLocalVariance.lean](Fluctuations/HaarLocalVariance.lean) supplies the local
  and conditional inequalities; unitality identifies the all-identity block
  with the previous observable.
- [HaarProcess.lean](Fluctuations/HaarProcess.lean) and
  [ActiveHaarCircuit.lean](Fluctuations/ActiveHaarCircuit.lean) retain both active
  and inactive blocks in independent histories and use $U_{d+1}=(J_dA_d)U_d$.
  Check the ordering and adjoints against the paper.
- [SpatialSupport.lean](Fluctuations/SpatialSupport.lean) cancels $J_d$ from
  conjugation of $B$ using unitarity and commutation. The full-layer theorem
  requires every possible embedded inactive gate to commute with $B$, at every
  depth. Its interleaved-list companion additionally requires every active
  factor to commute with every inactive factor; this is not an assumption of
  the already ordered model.
- [MeanChange.lean](Fluctuations/MeanChange.lean) and the final circuit wrapper
  prove the early mean equals one from $\mathrm{Tr}(\rho)=1$, $B^2=M^2=I$, and
  commutation of $U_a^\dagger BU_a$ with $M$ for every early history. Check that
  the later mean is within $1/4$ of the supplied reference and that the
  reference has norm at most $1/4$. These estimates are hypotheses, even when
  the reference is interpreted as the Haar mean.

The final Haar constant is `haarLocalConstant m k`. It is independent of the
inactive count $q$, dimension, embeddings, state and observable matrices, and
depth. The supplied-gap theorem makes this quantifier order explicit; the
moment-control theorem uses the same defined constant. Holding $m,k$ fixed is
essential for a system-size-independent conclusion. The proof gives no numerical
value and does not certify $4^{-8km}$.

## Review the variance conclusion

Complex variance is $\mathbb E|F-\mathbb EF|^2$. Check the endpoint definitions,
the gap $1/2$, positive transition width, width bound, and the requested range
$0\leq r\leq R$. The prefactor is uniform in system size for fixed $m,k,R$ in
the Haar model; the general theorem instead requires a supplied common $\eta$.
Both slope-to-variance and forward persistence are proved.

A physical application must supply a suitable active/inactive decomposition,
the commutation certificates, and a system-size-independent active count.
The tensor-factor and cancellation lemmas prove useful algebraic steps; they
do not construct a graph light cone or propagate support through a general
architecture. The moment-control error, reference-mean estimate, and width
bound also need separate justification. Design convergence and computational
quantum advantage are not consequences of the Lean result alone.

## Verification evidence

Follow the [reproduction guide](docs/reproduce.md), then run:

```sh
lake exe cache get
bash scripts/check.sh
```

The build and audit should succeed for the revision being reviewed. All listed
axiom reports must use only `propext`, `Classical.choice`, and `Quot.sound`.
Check [scripts/Audit.lean](scripts/Audit.lean) for the selected declarations and
[docs/verification.txt](docs/verification.txt) for the recorded output.
The full local check of the new extension passed: all 15 library modules and
the top-level import compiled, and the enforced 42-declaration audit passed
with no warnings or errors.

The [earlier Haar-model CI run](https://github.com/AntMele/observables-that-survive-concentration/actions/runs/36327000675)
passed for revision `949e8226e28dd3c87b98cd9b123d5aa1c2ab95a3`; its verification
job took 4 minutes 55 seconds (5 minutes 14 seconds for the full run).
That revision predates the active/inactive-layer and mean-change extensions.
Their local check is complete; their publication CI result is pending. Use the
[workflow history](https://github.com/AntMele/observables-that-survive-concentration/actions/workflows/lean.yml)
or a fresh check for the source under review and record its revision; an earlier
successful run does not certify later changes.
