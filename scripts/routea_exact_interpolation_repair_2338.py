"""2338: certified exact analytic interpolation repair in the captured family.

The ideal coefficient vectors are defined by the exact analytic moment matrix.
Arb balls enclose that unique solve. They are not stored floating coefficients.
This establishes finite-node realization only, not source-zero completeness.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

from flint import acb, acb_mat, arb, ctx
import flint

import routea_marked_sign_arb_certificate_2337 as certificate

ROOT = Path(__file__).resolve().parents[1]


def get_matrix_infinity_bound(matrix):
    return max(sum((abs(matrix[row, column]).upper()
                    for column in range(matrix.ncols())), arb(0)).upper()
               for row in range(matrix.nrows()))


def run_repair():
    ctx.prec = 320
    start = time.monotonic()
    capture, families, stored_coefficients, _, _ = certificate.load_capture()
    nodes = [certificate.decode_complex(pair) for pair in capture["nodes_hex"]]
    targets = [certificate.decode_complex(pair) for pair in capture["values_hex"]]
    count = len(nodes)
    if count != 30 or len(targets) != count or len(families) != count:
        raise ValueError("expected exact captured 30 by 30 moment system")
    matrix_rows = []
    maximum_radius = arb(0)
    matrix_payload = []
    for node_index, node in enumerate(nodes):
        row = []
        for family in families:
            value, _ = certificate.integrate_family(*family, node, panels=16)
            row.append(value)
            for component in (value.real, value.imag):
                maximum_radius = max(maximum_radius, component.rad())
                matrix_payload.append(certificate.serialize_real(component))
        matrix_rows.append(row)
        print("certified analytic matrix row", node_index, flush=True)
    matrix = acb_mat(matrix_rows)
    right_hand_side = acb_mat([[1, target] for target in targets])
    solution = matrix.solve(right_hand_side, algorithm="precond")
    approximate_inverse = matrix.inv().mid()
    identity = acb_mat([[int(row == column) for column in range(count)]
                        for row in range(count)])
    defect = identity - approximate_inverse * matrix
    defect_bound = get_matrix_infinity_bound(defect)
    if not defect_bound < arb("1/2"):
        raise RuntimeError("independent Neumann invertibility gate failed")
    residual = matrix * solution - right_hand_side
    if not all(residual[row, channel].contains(0)
               for row in range(count) for channel in range(2)):
        raise RuntimeError("interval solve residual excludes zero")
    inverse_bound = get_matrix_infinity_bound(approximate_inverse) / (1 - defect_bound)
    stored = acb_mat([[stored_coefficients[0][index], stored_coefficients[1][index]]
                      for index in range(count)])
    stored_residual = right_hand_side - matrix * stored
    stored_residual_bound = get_matrix_infinity_bound(stored_residual)
    global_repair_bound = inverse_bound * stored_residual_bound
    coefficient_rows = []
    base_change_charge, correction_change_charge = arb(0), arb(0)
    for index, (width, _) in enumerate(families):
        base_delta = solution[index, 0] - stored_coefficients[0][index]
        correction_delta = solution[index, 1] - stored_coefficients[1][index]
        radius = width * width
        strip_mass_bound = 2 * radius * (-30 + radius).exp()
        base_change_charge += abs(base_delta) * strip_mass_bound
        correction_change_charge += abs(correction_delta) * strip_mass_bound
        coefficient_rows.append({
            "index": index,
            "ideal_base_coefficient": certificate.serialize_complex(solution[index, 0]),
            "ideal_correction_coefficient": certificate.serialize_complex(solution[index, 1]),
            "base_delta_abs": certificate.serialize_real(abs(base_delta)),
            "correction_delta_abs": certificate.serialize_real(abs(correction_delta)),
        })
    if not all(solution[row, channel].is_finite()
               for row in range(count) for channel in range(2)):
        raise RuntimeError("nonfinite ideal coefficient enclosure")
    return {
        "record": 2338, "status": "EXACT_FINITE_NODE_REPAIR_ENCLOSED_ONLY",
        "python_flint_version": flint.__version__, "precision_bits": ctx.prec,
        "matrix_dimension": count, "solve_algorithm": "precond", "panels": 16,
        "edge_delta_exact": str(certificate.EDGE_DELTA),
        "capture_sha256": hashlib.sha256(certificate.CAPTURE.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "integrator_source_sha256": hashlib.sha256(Path(certificate.__file__).read_bytes()).hexdigest(),
        "matrix_entry_bounds_sha256": hashlib.sha256(json.dumps(
            matrix_payload, sort_keys=True).encode()).hexdigest(),
        "maximum_matrix_component_radius": certificate.serialize_real(maximum_radius),
        "neumann_defect_infinity_upper": certificate.serialize_real(defect_bound),
        "inverse_infinity_upper": certificate.serialize_real(inverse_bound),
        "stored_residual_infinity_upper": certificate.serialize_real(stored_residual_bound),
        "global_coefficient_repair_upper": certificate.serialize_real(global_repair_bound),
        "finite_node_realization_scope": "unique coefficients of the exact analytic moment matrix",
        "solution_interval_residual_contains_zero": True,
        "ideal_coefficients_cast_to_float": False,
        "coefficient_rows": coefficient_rows,
        "base_transform_change_strip_upper": certificate.serialize_real(base_change_charge),
        "correction_transform_change_strip_upper": certificate.serialize_real(correction_change_charge),
        "transform_change_scope": "all Im(z), 0 <= Re(z) <= 1; coefficient triangle bound",
        "signed_kernel_repair_charge_priced": False,
        "owner_transfer_to_live_consumer": False,
        "healthy_detector_instantiated": False, "finite_zero_node_completeness_proved": False,
        "rho_is_source_zero_proved": False, "lean_imported_certificate": False,
        "producer_go": False, "rh_claim": False,
        "elapsed_seconds": time.monotonic() - start,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2338_exact_interpolation_repair.json")
    args = parser.parse_args()
    result = run_repair()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("artifact", args.output, "status", result["status"], flush=True)
