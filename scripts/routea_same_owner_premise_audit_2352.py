"""2352: exact captured-owner premise audit, without a gate scan or numerical integration."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import routea_moment_matrix_exact_check_2351 as moment

ROOT = Path(__file__).resolve().parents[1]
WITNESS = ROOT / "results/2351_moment_matrix_witness.json"


def decode_point(value):
    components = moment.complex_interval(value)
    if any(lower != upper for lower, upper in components):
        raise ValueError("nonpoint owner coordinate or target")
    return tuple(lower for lower, _ in components)


def validate_mandatory_targets(nodes, targets):
    if len(nodes) < 8 or len(nodes) != len(targets):
        raise ValueError("missing mandatory node/target data")
    real, imag = nodes[0]
    expected_nodes = [(real, imag), (1 - real, imag), (real, -imag),
                      (1 - real, -imag), (real + Fraction(1, 2), imag),
                      (Fraction(1, 2), Fraction(0)), (Fraction(1), Fraction(0)),
                      (Fraction(3, 2), Fraction(0))]
    if not Fraction(1, 2) < real < 1 or imag == 0 or nodes[:8] != expected_nodes:
        raise ValueError("mandatory source orbit/shift/moment coordinates do not match")
    expected_targets = [(Fraction(value), Fraction(0)) for value in (1, -1, 0, 0, -1, 0, 0, 0)]
    if targets[:8] != expected_targets:
        raise ValueError("mandatory healthy raw target values do not match")
    if len(set(nodes)) != len(nodes):
        raise ValueError("duplicate captured nodes")
    square_values = []
    for real_node, imag_node in nodes[:4]:
        index = nodes.index((real_node, imag_node))
        companion = nodes.index((1 - real_node, imag_node))
        real_value, imag_value = targets[index]
        real_companion, imag_companion = targets[companion]
        square_values.append((real_companion * real_value + imag_companion * imag_value,
                              real_companion * imag_value - imag_companion * real_value))
    return {"rho_real_exact": str(real), "rho_imag_exact": str(imag),
            "mandatory_node_indices": list(range(8)),
            "mandatory_raw_targets_match": True,
            "raw_moment_indices": [5, 6, 7],
            "marked_square_real_values_exact": [str(value[0]) for value in square_values],
            "marked_square_imag_values_exact": [str(value[1]) for value in square_values],
            "marked_orbit_sum_exact": str(sum(value[0] for value in square_values)),
            "interpretation": "exact prescribed values; realization conditional on actual matrix invertibility"}


def get_contraction_obstruction(nodes, base_targets, threshold, bound):
    threshold, bound = Fraction(threshold), Fraction(bound)
    if len(nodes) != len(base_targets):
        raise ValueError("node/base-target dimension mismatch")
    indices = [index for index, ((real, imag), target) in enumerate(zip(nodes, base_targets))
               if 0 <= real <= 1 and target == (Fraction(1), Fraction(0))
               and threshold <= abs(imag) and bound < 1]
    return {"threshold_exact": str(threshold), "bound_exact": str(bound),
            "excluded_conditional_on_exact_base_realization": bool(indices),
            "forced_unit_value_node_indices": indices,
            "not_excluded_does_not_certify_contraction": True}


def get_contraction_floor(nodes, base_targets):
    if len(nodes) != len(base_targets):
        raise ValueError("node/base-target dimension mismatch")
    heights = [(abs(imag), index) for index, ((real, imag), target)
               in enumerate(zip(nodes, base_targets))
               if 0 <= real <= 1 and target == (Fraction(1), Fraction(0))]
    if not heights:
        raise ValueError("no forced unit-value nodes in the source slab")
    floor = max(height for height, _ in heights)
    shell = 0
    while Fraction(2**(shell + 1)) <= floor:
        shell += 1
    return {"threshold_strictly_greater_than_exact": str(floor),
            "attaining_node_indices": [index for height, index in heights if height == floor],
            "minimum_height_shell_index_for_threshold_le_two_pow_succ": shell,
            "shell_ceiling_exact": str(2**(shell + 1)),
            "scope": "necessary condition for the uniform base contraction supplier, not for every possible tail proof",
            "conditional_on_exact_base_realization": True}


def get_support_cover(radii, iterate):
    if not radii or any(radius <= 0 for radius in radii):
        raise ValueError("nonpositive family radius")
    if not isinstance(iterate, int) or isinstance(iterate, bool) or iterate < 0:
        raise ValueError("invalid convolution iterate")
    radius = max(radii)
    return {"iterate": iterate, "factor_radius_exact": str(radius),
            "source_radius_cover_exact": str((iterate + 2) * radius),
            "square_radius_cover_exact": str(2 * (iterate + 2) * radius),
            "single_factor_square_radius_exact": str(2 * radius),
            "exact_nonzero_prime_set_identified": False,
            "complete_covering_prime_book_enumerated": False,
            "larger_cover_does_not_prove_missing_nonzero_terms": True}


def get_height_shell_floor(contraction_floor, rho_height):
    contraction_floor, rho_height = Fraction(contraction_floor), abs(Fraction(rho_height))
    shell = 0
    while Fraction(2**(shell + 1)) <= contraction_floor or 2**(shell + 1) < 2 * rho_height:
        shell += 1
    return {"minimum_shell_index": shell, "ceiling_exact": str(2**(shell + 1)),
            "rho_double_height_exact": str(2 * rho_height),
            "conditions": "T > forced-node floor, T <= 2^(N+1), 2*abs(Im rho) <= 2^(N+1)",
            "necessary_only": True}


def run(witness_path=WITNESS):
    exact_check = moment.run(witness_path)
    if not exact_check["neumann_pass"] or not exact_check["coefficient_boxes_invariant"]:
        raise ValueError("original moment witness is not certified")
    payload = json.loads(witness_path.read_text())
    nodes = [decode_point(value) for value in payload["nodes"]]
    base_targets, correction_targets = [[decode_point(value) for value in row]
                                       for row in payload["right_hand_sides"]]
    if base_targets != [(Fraction(1), Fraction(0))] * len(nodes):
        raise ValueError("unexpected captured all-node base targets")
    mandatory = validate_mandatory_targets(nodes, correction_targets)
    floor = get_contraction_floor(nodes, base_targets)
    mandatory_floor = get_contraction_floor(nodes[:8], base_targets[:8])
    probes = [get_contraction_obstruction(nodes, base_targets, threshold, bound)
              for threshold, bound in ((28, Fraction(1, 2**14)),
                                       (64, Fraction(1, 2)),
                                       (Fraction(floor["threshold_strictly_greater_than_exact"]), Fraction(1, 2)),
                                       (128, Fraction(1, 2)))]
    sources = ["scripts/routea_same_owner_premise_audit_2352.py",
               "scripts/routea_moment_matrix_exact_check_2351.py",
               "scripts/routea_same_owner_premise_selftest_2352.py",
               "ConnesWeilRH/Dev/C1RouteAAnalyticMomentSystem.lean",
               "ConnesWeilRH/Dev/C1RouteAContractionCutoff.lean",
               "ConnesWeilRH/Dev/C1RouteAContractionCutoffAudit.lean",
               "ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean",
               "ConnesWeilRH/Dev/C1FourPointHighShellTail.lean",
               "ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean"]
    return {"record": 2352, "status": "EXACT_PREMISE_AUDIT_CONDITIONAL_CUTOFF_OBSTRUCTION",
            "arithmetic": "Python Fraction; no new quadrature, float solve, gate scan or kernel pricing",
            "input_sha256": {witness_path.relative_to(ROOT).as_posix():
                             hashlib.sha256(witness_path.read_bytes()).hexdigest()},
            "source_sha256": {relative: hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                              for relative in sources},
            "parent_witness_rechecked_in_same_run": True,
            "original_coefficient_boxes_unchanged": True,
            "mandatory_targets": mandatory,
            "captured_node_count": len(nodes),
            "extra_base_unit_constraints_beyond_mandatory_indices": list(range(8, len(nodes))),
            "extra_node_source_zero_semantics_proved": False,
            "contraction_floor": floor, "cutoff_controls": probes,
            "mandatory_target_only_contraction_floor": mandatory_floor,
            "height_shell_floor_all_nodes": get_height_shell_floor(
                floor["threshold_strictly_greater_than_exact"], nodes[0][1]),
            "height_shell_floor_mandatory_targets_only": get_height_shell_floor(
                mandatory_floor["threshold_strictly_greater_than_exact"], nodes[0][1]),
            "removing_extra_base_constraints_improves_first_healthy_height_shell": False,
            "support_covers": [get_support_cover([Fraction(value) for value in payload["support_radii_exact"]],
                                                  iterate) for iterate in (0, 1, 2)],
            "open_obligations": ["actual analytic matrix integral enclosure import",
                                 "actual numeric matrix invertibility and solution-box import",
                                 "complete required source-zero prefix identification or parametric construction",
                                 "same-owner uniform tail constants and accepted tail budget",
                                 "complete-support signed physical-kernel budget"],
            "all_node_base_interpolation_required_by_healthy_target_api": False,
            "removing_extra_constraints_changes_owner": True,
            "legacy_T28_q_bound_transferred": False,
            "uniform_tail_at_T128_certified": False,
            "actual_numeric_invertibility_instantiated_in_lean": False,
            "healthy_detector_instantiated": False, "complete_signed_kernel_priced": False,
            "map103_reopened": False, "global_tail_impossibility_claim": False,
            "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2352_same_owner_premise_audit.json")
    arguments = parser.parse_args()
    result = run()
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "T >", result["contraction_floor"]["threshold_strictly_greater_than_exact"],
          "minimum shell", result["contraction_floor"]["minimum_height_shell_index_for_threshold_le_two_pow_succ"])
