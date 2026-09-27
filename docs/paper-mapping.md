# Paper-to-code map

[Repository overview](../README.md) · [Mathematical guide](guide.md) ·
[Run the verification](reproduce.md)

Companion to *Towards verifiable quantum advantage with random circuits:
Observables that survive concentration*. This map refers to the manuscript
snapshot identified below: Theorem VI.14 on PDF pages 27–28 and the persistence
lemma VI.13 on page 26. The source PDF has the older filename
*Large fluctuations of OTOCs in random circuits*.

The stable LaTeX label is `thm:fixed-k-transition-window-fluctuation-bound`
(source line 2991). Match this label and the mathematical statement when
working with a manuscript whose numbering has changed.

| Paper statement | Formal component | Status |
| --- | --- | --- |
| Complex variance convention, appendix V | [`complexVariance`](../Fluctuations/Probability.lean) | Definition |
| Eq. (107), local reverse variance | [`LocalReverseVariance`](../Fluctuations/Probability.lean#L109) | Hypothesis |
| Eq. (109), law of total variance | [`complex_total_variance`](../Fluctuations/Probability.lean#L56) | Proved |
| Eq. (110), integrated local estimate | [`localReverseVariance_integrated`](../Fluctuations/Probability.lean#L115) | Proved |
| Eq. (111), weighted square inequality | [`weighted_norm_sq` and `weighted_variance_comparison`](../Fluctuations/WeightedVariance.lean) | Proved |
| Lemma VI.13 / Eq. (108) | [`forward_persistence`](../Fluctuations/WeightedVariance.lean#L63) | Proved |
| Eq. (114), half-unit mean change | `hchange` in [`theorem_VI_14`](../Fluctuations/Main.lean#L39) | Hypothesis |
| Eqs. (115)–(116), telescoping and large increment | [`exists_large_increment`](../Fluctuations/Window.lean#L15) | Proved |
| Eq. (117), variance from a mean increment | [`slope_to_variance`](../Fluctuations/Probability.lean#L130) | Proved |
| Eq. (118), persistence over later depths | [`window_of_step_bounds`](../Fluctuations/Window.lean#L38), assembled in `Main.lean` | Proved |
| Eq. (119), uniform bound and polynomial width | [`theorem_VI_14`](../Fluctuations/Main.lean#L39), [`theorem_VI_14_family`](../Fluctuations/Main.lean#L107) | Proved |
| Theorem VI.14, interval size and location | [`theorem_VI_14_interval`](../Fluctuations/Main.lean#L78) | Proved |
| Remark VI.15, arbitrary mean gap | [`transition_window`](../Fluctuations/Main.lean#L18) | Proved |

## Exact scope

This proves the conclusion from two explicit mathematical inputs:
mean change and local reverse variance. These are hypotheses of theorems, not
new global axioms. The physical derivation of those inputs is not certified by
this project. Probability, square-integrability, a valid conditioning
sigma-algebra, positive uniform `η`, and positive window width are explicit
standard structural hypotheses.

The scalar lemmas in `Window.lean` use intermediate slope and persistence bounds
as inputs. The final theorem obtains both bounds from the local condition using
the proved probability lemmas; they are not premises of the final theorem.

The sequence-level proof assumes the local inequality at every depth, as in
Lemma VI.13. For a chosen finite window and length `R+1`, only transitions up to
`b+R-1` after the starting depth can contribute to the proof.

For the application to the original OTOC statement, instantiate the abstract
process with the paper's observable, and the conditioning sigma-algebra with the
information in the depth-`d` circuit. The theorem holds for every process with
these inputs; it does not assume real-valued OTOCs or a finite sample space.

## Manuscript provenance

The following source files identify the draft used for the formalization.
They were inspected without editing them and are not distributed in this
repository. A public paper URL or DOI can be added when available.

```text
MAIN (24).tex
SHA-256: ef25202b80354f0142730e2e1dcb47661cf517dcb388f28e2e80630b324dbb6a

Large_fluctuations_of_OTOCs_in_random_circuits (79).pdf
SHA-256: 9f653514f023afd3ca37d2a05693fb8ca15749d7a870273852d772c4ea9f5a18
```

## Referencing the formalization

When discussing the mathematical result, cite the paper. When discussing the
machine-checked proof, also give the repository URL, the exact commit used,
and the relevant declaration (for example, `Fluctuations.theorem_VI_14_family`).
This distinguishes the reviewed source snapshot from later changes and avoids
depending on theorem numbering alone. No publication identifier is inferred
from the draft filename.
