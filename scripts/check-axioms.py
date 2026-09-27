#!/usr/bin/env python3
"""Require every audited declaration and only Lean's standard axioms.

The general-ensemble theorem has explicit scientific hypotheses; the Haar
extension proves local reverse variance. Neither adds global axioms.
In particular, sorryAx and any user-defined axiom fail this check.
"""

import re
import sys
from pathlib import Path


EXPECTED = {
    "Fluctuations.complex_total_variance",
    "Fluctuations.norm_mean_sq_le_secondMoment",
    "Fluctuations.slope_to_variance",
    "Fluctuations.forward_persistence",
    "Fluctuations.exists_large_increment",
    "Fluctuations.transition_window",
    "Fluctuations.theorem_VI_14",
    "Fluctuations.theorem_VI_14_interval",
    "Fluctuations.theorem_VI_14_family",
    "Fluctuations.finiteDimensional_reverseVariance",
    "Fluctuations.su4Haar_independent",
    "Fluctuations.matrixBlockOTOC_mem",
    "Fluctuations.matrixBlockOTOC_apply",
    "Fluctuations.qubitEmbedding",
    "Fluctuations.qubitEmbedding_injective",
    "Fluctuations.starAlgHom_su4_mem_unitary",
    "Fluctuations.product_condExp",
    "Fluctuations.product_localReverseVariance",
    "Fluctuations.haarLocalConstant_pos",
    "Fluctuations.haarLocalOTOC_reverseVariance_identity",
    "Fluctuations.haarLocalOTOC_conditional_reverseVariance",
    "Fluctuations.history_transition_window",
    "Fluctuations.history_theorem_VI_14",
    "Fluctuations.haarCircuit_theorem_VI_14",
    "Fluctuations.theorem_VI_14_of_step_bounds",
    "Fluctuations.ordered_product_inactive_mul_active",
    "Fluctuations.haarBlockMatrix_mem_unitary",
    "Fluctuations.haarBlockMatrix_inactive_conjugation",
    "Fluctuations.matrix_conjugate_layer_eq_active",
    "Fluctuations.embedded_su4_layer_eq_active",
    "Fluctuations.disjoint_tensor_factors_commute",
    "Fluctuations.preLightCone_otoc_eq_one",
    "Fluctuations.integral_preLightCone_otoc_eq_one",
    "Fluctuations.mean_gap_of_error_budget",
    "Fluctuations.mean_gap_one_half",
    "Fluctuations.activeHaarCircuitMatrix_mem_unitary",
    "Fluctuations.activeHaarCircuitOTOC_section",
    "Fluctuations.activeHaarCircuit_localReverseVariance",
    "Fluctuations.activeHaarCircuit_step_bounds",
    "Fluctuations.activeHaarCircuit_early_mean",
    "Fluctuations.activeHaarCircuit_theorem_VI_14",
    "Fluctuations.activeHaarCircuit_theorem_of_moment_control",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]"
    r"|does not depend on any axioms)\s*$",
    re.MULTILINE,
)


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: check-axioms.py LEAN_AUDIT_LOG", file=sys.stderr)
        return 2
    reports = REPORT.findall(Path(sys.argv[1]).read_text(encoding="utf-8"))
    seen = set()
    errors = []
    for name, raw_axioms in reports:
        if name in seen:
            errors.append(f"Duplicate audit entry: {name}")
        seen.add(name)
        axioms = {axiom.strip() for axiom in raw_axioms.split(",") if axiom.strip()}
        forbidden = axioms - ALLOWED_AXIOMS
        if forbidden:
            errors.append(f"{name} uses forbidden axioms: {', '.join(sorted(forbidden))}")
    for name in sorted(EXPECTED - seen):
        errors.append(f"Missing audit entry: {name}")
    for name in sorted(seen - EXPECTED):
        errors.append(f"Unexpected audit entry: {name}")
    if errors:
        print("Axiom audit failed:\n" + "\n".join(errors), file=sys.stderr)
        return 1
    print(
        f"Axiom audit passed for all {len(EXPECTED)} declarations: "
        "only propext, Classical.choice, and Quot.sound are allowed."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
