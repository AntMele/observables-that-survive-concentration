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
    "Fluctuations.globalHaarOTOCMean_norm_le_one",
    "Fluctuations.globalHaarOTOCMean_norm_le_all_dimensions",
    "Fluctuations.globalHaarOTOCMean_norm_le_quarter_all_dimensions",

    "Fluctuations.globalHaarOTOCMean_eq_weingarten",
    "Fluctuations.globalHaarOTOCMean_norm_le",
    "Fluctuations.globalHaarOTOCMean_norm_le_quarter",
    "Fluctuations.spatialHaarCircuit_allOrders_of_globalHaar_control",

    "Fluctuations.unitaryConjugationEquivariant_classification",
    "Fluctuations.globalHaarOTOCMean_one_exact",
    "Fluctuations.globalHaarOTOCMean_one_norm_le_quarter",
    "Fluctuations.globalHaarOTOCMatrixMean_scalar_of_traceless_involution",
    "Fluctuations.globalHaarOTOCMean_state_independent_of_traceless_involution",
    "Fluctuations.globalHaarOTOCMean_traceless_involution_eq_normalized_trace",
    "Fluctuations.tensorPower_commutant_eq_permutation_sum",
    "Fluctuations.tensorPower_commutant_mem_span",
    "Fluctuations.matrixPolynomialEval_zero_of_unitary",
    "Fluctuations.tensorPower_commute_all_of_unitary",
    "Fluctuations.tensorPower_unitary_commutant_eq_permutation_sum",
    "Fluctuations.tensorPower_unitary_commutant_mem_span",
    "Fluctuations.globalHaarRepresentationMean_commute",
    "Fluctuations.globalHaarRepresentationMean_trace_pairing",
    "Fluctuations.globalHaarTensorMean_eq_permutation_sum",
    "Fluctuations.globalHaarTensorMean_mem_span",
    "Fluctuations.matrix_expansion_of_gram",
    "Fluctuations.tensorPositionPermutation_gram",
    "Fluctuations.tensorPowerMatrix_diagonal_trace_permutation",
    "Fluctuations.tensorPowerMatrix_traceless_involution_trace_permutation",
    "Fluctuations.globalHaarTensorMean_weingarten",
    "Fluctuations.trace_power_eq_tensor_cycle",
    "Fluctuations.globalHaarOTOCMean_maximallyMixed_eq_tensor",
    "Fluctuations.qubit_globalHaarOTOCMean_one_norm_le_quarter",
    "Fluctuations.spatialHaarCircuit_firstOrder_of_globalHaar_control",

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
    "Fluctuations.tensorMatrix_mul",
    "Fluctuations.Supported.commute",
    "Fluctuations.supported_patchMatrix",
    "Fluctuations.supported_patchEmbedding",
    "Fluctuations.patchEmbedding_injective",
    "Fluctuations.supported_twoQubitPatchEmbedding",
    "Fluctuations.twoQubitPatchEmbedding_mem_unitary",
    "Fluctuations.LayerArchitecture.card_active_le",
    "Fluctuations.LayerArchitecture.conjugate_eq_active",
    "Fluctuations.LayerArchitecture.supported_conjugate",
    "Fluctuations.supported_spatialCircuit",
    "Fluctuations.spatialCircuit_commute_of_disjoint",
    "Fluctuations.card_backwardCone_le",
    "Fluctuations.backwardActiveGateCount_le",
    "Fluctuations.HaarSpatialArchitecture.active_count_le",
    "Fluctuations.HaarSpatialArchitecture.card_lightCone_le",
    "Fluctuations.HaarSpatialArchitecture.circuit_supported",
    "Fluctuations.HaarSpatialArchitecture.early_commute",
    "Fluctuations.HaarSpatialArchitecture.inactive_commute",
    "Fluctuations.HaarSpatialArchitecture.early_mean",
    "Fluctuations.haar_subspace_reverseVariance",
    "Fluctuations.haarLocalOTOC_balanced_mem",
    "Fluctuations.balancedSU4_polynomial_translate_mem",
    "Fluctuations.balancedSU4_polynomial_finrank_le",
    "Fluctuations.explicitHaarConstant_pos",
    "Fluctuations.haarLocalOTOC_explicit_reverseVariance_identity",
    "Fluctuations.haarLocalOTOC_explicit_conditional_reverseVariance",
    "Fluctuations.activeHaarCircuit_explicit_step_bounds",
    "Fluctuations.activeHaarCircuit_explicit_variance_window",
    "Fluctuations.activeHaarCircuit_explicit_theorem_of_moment_control",
    "Fluctuations.explicitHaarWindowConstant_antitone",
    "Fluctuations.globalHaarOTOCMean_eq_trace_matrixMean",
    "Fluctuations.globalHaarOTOCMatrixMean_conjugation",
    "Fluctuations.globalHaarOTOCMatrixMean_commute",
    "Fluctuations.spatialHaarCircuit_variance_window",
    "Fluctuations.spatialHaarCircuit_of_globalHaar_control",
    "Fluctuations.globalHaarOTOCMatrixMean_conjugateProbe",
    "Fluctuations.globalHaarOTOCMatrixMean_conjugateButterfly",
    "Fluctuations.globalMaximallyMixedState_trace",
    "Fluctuations.globalHaarOTOCMean_balancedZ_state_independent",
    "Fluctuations.globalHaarOTOCMean_conjugateBalancedZ_state_independent",
    "Fluctuations.globalHaarOTOCMean_balancedZ_eq_normalized_trace",
    "Fluctuations.maximal_cycles_weingarten_argument_ne_one",
    "Fluctuations.weingartenOTOCSum_norm_le_factorial",
    "Fluctuations.norm_le_of_weingartenHaarIdentity",
    "Fluctuations.quarter_bound_of_weingartenHaarIdentity",
    "Fluctuations.globalHaarTwirl_one",
    "Fluctuations.globalHaarTwirl_trace",
    "Fluctuations.globalHaarTwirl_equivariant",
    "Fluctuations.globalHaarTwirl_superTrace",
    "Fluctuations.globalHaarOTOCMatrixMean_one_eq_twirl",
    "Fluctuations.normalizedPermutationGram_isUnit",
    "Fluctuations.normalizedPermutationGram_inverse_bounds",
    "Fluctuations.gramWeingarten_inverse_identity",
    "Fluctuations.gramWeingartenCoefficient_bounds",
    "Fluctuations.gramWeingartenOTOCSum_norm_le",
    "Fluctuations.norm_le_of_gramWeingartenHaarIdentity",
    "Fluctuations.quarter_bound_of_gramWeingartenHaarIdentity",
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
