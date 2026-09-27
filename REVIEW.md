# Reviewing the formalization

[Overview](README.md) · [Guide](docs/guide.md) · [Paper map](docs/paper-mapping.md)

Review the formal statement and its physical interpretation as separate checks.
Start with [HaarCircuit.lean](Fluctuations/HaarCircuit.lean) for the concrete Haar
model, or [Main.lean](Fluctuations/Main.lean) for the general probability theorem.

## Results and assumption boundaries

| Declaration | Main boundary |
| --- | --- |
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
  [HaarCircuit.lean](Fluctuations/HaarCircuit.lean) sample fresh blocks independently
  and use $U_{d+1}=W_dU_d$. Check the ordering and adjoints against the paper.

The final Haar constant is quantified before dimension, embeddings, state and
observable matrices, and depth. It depends on $m,k$, so holding these fixed is
essential for a system-size-independent conclusion. The proof gives no numerical
value and does not certify $4^{-8km}$.

## Review the variance conclusion

Complex variance is $\mathbb E|F-\mathbb EF|^2$. Check the endpoint definitions,
the gap $1/2$, positive transition width, width bound, and the requested range
$0\leq r\leq R$. The prefactor is uniform in system size for fixed $m,k,R$ in
the Haar model; the general theorem instead requires a supplied common $\eta$.
Both slope-to-variance and forward persistence are proved.

A physical application must still justify how its architecture reduces to the
modeled fixed-size block and establish the endpoint mean gap and width.
Light-cone reduction, design convergence, and computational quantum advantage
are not consequences of the Lean result alone.

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
The earlier successful CI run of the abstract-only version does not verify the
new Haar extension; use a fresh check and record its revision.
