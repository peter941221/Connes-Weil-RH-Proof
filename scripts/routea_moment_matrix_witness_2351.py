"""2351: export the actual 2338 matrix and rational inverse witness unchanged."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb_mat
import routea_exact_interpolation_repair_2338 as repair

ROOT = Path(__file__).resolve().parents[1]


def run():
    parent_path = ROOT / "results/2338_exact_interpolation_repair.json"
    parent = json.loads(parent_path.read_text())
    if parent.get("record") != 2338 or parent.get("matrix_dimension") != 30:
        raise ValueError("unexpected repaired-source record")
    for key, path in (("source_sha256", Path(repair.__file__)),
                      ("integrator_source_sha256", Path(repair.certificate.__file__)),
                      ("capture_sha256", repair.certificate.CAPTURE)):
        if hashlib.sha256(path.read_bytes()).hexdigest() != parent[key]:
            raise ValueError("parent source mismatch: " + key)
    capture, families, _, _, _ = repair.certificate.load_capture()
    nodes = [repair.certificate.decode_complex(pair) for pair in capture["nodes_hex"]]
    original = repair.certificate.integrate_family
    entries = []

    def record_integral(width, modulation, node, panels=16):
        index = len(entries)
        if index >= 900:
            raise ValueError("too many parent matrix evaluations")
        row, column = divmod(index, 30)
        expected_width, expected_modulation = families[column]
        if width != expected_width or modulation != expected_modulation or node != nodes[row] or panels != 16:
            raise ValueError("parent matrix evaluation owner/order mismatch")
        value, edge = original(width, modulation, node, panels=panels)
        entries.append(value)
        return value, edge

    repair.certificate.integrate_family = record_integral
    try:
        reproduced = repair.run_repair()
    finally:
        repair.certificate.integrate_family = original
    if len(entries) != 900:
        raise ValueError("incomplete matrix capture")
    for key in parent:
        if key != "elapsed_seconds" and parent[key] != reproduced[key]:
            raise ValueError("same-run parent reproduction failed: " + key)
    matrix = acb_mat([entries[index:index + 30] for index in range(0, 900, 30)])
    candidate = matrix.inv().mid()
    serialize = repair.certificate.serialize_complex
    inverse = [[serialize(candidate[row, column]) for column in range(30)] for row in range(30)]
    for row in inverse:
        for value in row:
            for component in ("real", "imag"):
                if value[component]["lower_exact"] != value[component]["upper_exact"]:
                    raise ValueError("candidate inverse is not an exact rational point")
    coefficients = [[row[key] for row in parent["coefficient_rows"]]
                    for key in ("ideal_base_coefficient", "ideal_correction_coefficient")]
    targets = [repair.certificate.decode_complex(pair) for pair in capture["values_hex"]]
    return {
        "record": 2351, "status": "EXPORTED_ACTUAL_MOMENT_MATRIX_WITNESS",
        "dimension": 30, "precision_bits": reproduced["precision_bits"],
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "parent_sha256": hashlib.sha256(parent_path.read_bytes()).hexdigest(),
        "parent_input_sha256": {key: parent[key] for key in
                                ("source_sha256", "integrator_source_sha256", "capture_sha256")},
        "same_run_parent_reproduced_except_elapsed": True,
        "matrix_order": "row=node, column=family; capture order retained",
        "support_radii_exact": [str(Fraction(float.fromhex(pair[0]))**2)
                                for pair in capture["families_hex"]],
        "modulations_exact": [str(Fraction(float.fromhex(pair[1])))
                              for pair in capture["families_hex"]],
        "nodes": [serialize(value) for value in nodes],
        "matrix": [[serialize(matrix[row, column]) for column in range(30)] for row in range(30)],
        "candidate_inverse": inverse,
        "right_hand_sides": [[serialize(repair.certificate.acb(1)) for _ in range(30)],
                             [serialize(value) for value in targets]],
        "coefficient_rectangles": coefficients,
        "analytic_matrix_enclosures_imported_in_lean": False,
        "coefficient_realization_imported_in_lean": False,
        "healthy_detector_instantiated": False, "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2351_moment_matrix_witness.json")
    arguments = parser.parse_args()
    result = run()
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "900 matrix rectangles and 900 inverse points exported", flush=True)
