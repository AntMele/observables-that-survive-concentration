# Correspondence with the supplied paper

Source: Theorem VI.14 on PDF pages 27–28; its persistence lemma VI.13 is on page 26.
The corresponding LaTeX label is
`thm:fixed-k-transition-window-fluctuation-bound`, beginning at line 2990
in the supplied source.

| Paper statement | Formal component |
| --- | --- |
| Complex variance convention, appendix V | `complexVariance` |
| Eq. (107), local reverse variance | Hypothesis `LocalReverseVariance` |
| Eq. (109), law of total variance | `complex_total_variance` |
| Eq. (110), integrated local estimate | `localReverseVariance_integrated` |
| Eq. (111), weighted square inequality | `weighted_norm_sq`, `weighted_variance_comparison` |
| Lemma VI.13 / Eq. (108) | `forward_persistence` |
| Eq. (114), half-unit mean change | Assumed in the VI.14 specialization |
| Eqs. (115)–(116), telescoping and large increment | `Window.lean` |
| Eq. (117), variance from a mean increment | `slope_to_variance`, assembled in `Main.lean` |
| Eq. (118), persistence over later depths | `Window.lean`, assembled in `Main.lean` |
| Eq. (119), uniform bound and polynomial width | VI.14 and polynomial-family results in `Main.lean` |
| Remark VI.15, arbitrary mean gap | General transition-window theorem in `Main.lean` |

## Exact scope

This proves the conclusion from the two mathematical inputs the user allowed:
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

## Supplied sources

Files were inspected without editing them.

```text
MAIN (24).tex
SHA-256: ef25202b80354f0142730e2e1dcb47661cf517dcb388f28e2e80630b324dbb6a

Large_fluctuations_of_OTOCs_in_random_circuits (79).pdf
SHA-256: 9f653514f023afd3ca37d2a05693fb8ca15749d7a870273852d772c4ea9f5a18
```
