"""2351: exact rational interval Neumann and fixed-box verification, without Arb."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def real_interval(value):
    lower, upper = (Fraction(value[key]) for key in ("lower_exact", "upper_exact"))
    if lower > upper:
        raise ValueError("inverted rational interval")
    return lower, upper


def complex_interval(value):
    return real_interval(value["real"]), real_interval(value["imag"])


def real_add(left, right):
    return left[0] + right[0], left[1] + right[1]


def real_neg(value):
    return -value[1], -value[0]


def real_mul(left, right):
    products = [first * second for first in left for second in right]
    return min(products), max(products)


def complex_add(left, right):
    return real_add(left[0], right[0]), real_add(left[1], right[1])


def complex_neg(value):
    return real_neg(value[0]), real_neg(value[1])


def complex_mul(left, right):
    return (real_add(real_mul(left[0], right[0]), real_neg(real_mul(left[1], right[1]))),
            real_add(real_mul(left[0], right[1]), real_mul(left[1], right[0])))


def point(real=0, imag=0):
    return ((Fraction(real), Fraction(real)), (Fraction(imag), Fraction(imag)))


def hex_fraction(text):
    sign = -1 if text.startswith("-") else 1
    unsigned = text.lstrip("+-")
    significand, exponent = unsigned.split("p")
    if not significand.startswith("0x"):
        raise ValueError("nonhexadecimal captured operand")
    digits = significand[2:].split(".")
    if len(digits) != 2:
        raise ValueError("missing hexadecimal fractional part")
    power = int(exponent)
    result = Fraction(sign * int("".join(digits), 16), 16**len(digits[1]))
    return result * 2**power if power >= 0 else result / 2**(-power)


def validate_owner(payload):
    parent_path = ROOT / "results/2338_exact_interpolation_repair.json"
    parent = json.loads(parent_path.read_text())
    if hashlib.sha256(parent_path.read_bytes()).hexdigest() != payload["parent_sha256"]:
        raise ValueError("parent artifact hash mismatch")
    if parent.get("record") != 2338 or parent.get("matrix_dimension") != 30:
        raise ValueError("unexpected parent owner scope")
    for key, relative in (("source_sha256", "scripts/routea_exact_interpolation_repair_2338.py"),
                          ("integrator_source_sha256", "scripts/routea_marked_sign_arb_certificate_2337.py"),
                          ("capture_sha256", "results/2275_gap_owner_audit.json")):
        digest = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if payload["parent_input_sha256"][key] != digest or parent[key] != digest:
            raise ValueError("parent input hash mismatch")
    matrix_payload = [entry[component] for row in payload["matrix"] for entry in row
                      for component in ("real", "imag")]
    matrix_hash = hashlib.sha256(json.dumps(matrix_payload, sort_keys=True).encode()).hexdigest()
    if matrix_hash != parent["matrix_entry_bounds_sha256"]:
        raise ValueError("exported matrix differs from the original analytic matrix")
    rows = parent["coefficient_rows"]
    if [row["index"] for row in rows] != list(range(30)):
        raise ValueError("reordered parent coefficients")
    expected_boxes = [[row[key] for row in rows] for key in
                      ("ideal_base_coefficient", "ideal_correction_coefficient")]
    if payload["coefficient_rectangles"] != expected_boxes:
        raise ValueError("coefficient rectangles changed or widened")
    capture = json.loads((ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    expected_radii = [str(hex_fraction(pair[0])**2) for pair in capture["families_hex"]]
    expected_modulations = [str(hex_fraction(pair[1])) for pair in capture["families_hex"]]
    if payload["support_radii_exact"] != expected_radii or payload["modulations_exact"] != expected_modulations:
        raise ValueError("captured family owner mismatch")
    nodes = [complex_interval(value) for value in payload["nodes"]]
    expected_nodes = [point(*(hex_fraction(value) for value in pair)) for pair in capture["nodes_hex"]]
    targets = [point(*(hex_fraction(value) for value in pair)) for pair in capture["values_hex"]]
    rhs = [[complex_interval(value) for value in row] for row in payload["right_hand_sides"]]
    if nodes != expected_nodes or rhs != [[point(1)] * 30, targets]:
        raise ValueError("captured nodes or target vectors changed")


def l1_upper(value):
    return sum(max(abs(component[0]), abs(component[1])) for component in value)


def midpoint(value):
    return tuple(((lower + upper) / 2, (lower + upper) / 2) for lower, upper in value)


def sum_complex(values):
    result = point()
    for value in values:
        result = complex_add(result, value)
    return result


def matrix_vector(matrix, vector):
    return [sum_complex(complex_mul(entry, value) for entry, value in zip(row, vector))
            for row in matrix]


def verify(matrix, inverse, rhs_vectors, boxes):
    dimension = len(matrix)
    if dimension == 0 or len(inverse) != dimension:
        raise ValueError("empty or incompatible matrix")
    if any(len(row) != dimension for row in matrix + inverse):
        raise ValueError("incomplete square matrix")
    if len(rhs_vectors) != len(boxes) or not boxes:
        raise ValueError("missing coefficient channel")
    if any(len(vector) != dimension for vector in rhs_vectors + boxes):
        raise ValueError("incomplete vector")
    if any(lower != upper for row in inverse for value in row for lower, upper in value):
        raise ValueError("candidate inverse must be an exact point matrix")
    product = [[sum_complex(complex_mul(inverse[row][index], matrix[index][column])
                            for index in range(dimension))
                for column in range(dimension)] for row in range(dimension)]
    defect = [[complex_add(point(int(row == column)), complex_neg(product[row][column]))
               for column in range(dimension)] for row in range(dimension)]
    row_bounds = [sum(l1_upper(value) for value in row) for row in defect]
    eta = max(row_bounds)
    if eta >= 1:
        raise ValueError("exact Neumann row bound is not below one")
    channels = []
    for rhs, box in zip(rhs_vectors, boxes):
        center = [midpoint(value) for value in box]
        residual = [complex_add(target, complex_neg(value))
                    for target, value in zip(rhs, matrix_vector(matrix, center))]
        corrected = matrix_vector(inverse, residual)
        centered_box = [complex_add(value, complex_neg(base)) for value, base in zip(box, center)]
        moved_box = matrix_vector(defect, centered_box)
        image = [complex_add(base, complex_add(delta, remainder))
                 for base, delta, remainder in zip(center, corrected, moved_box)]
        containment = []
        maximum_ratio = Fraction(0)
        for index, (original, enclosed) in enumerate(zip(box, image)):
            for component, ((lower, upper), (image_lower, image_upper)) in enumerate(zip(original, enclosed)):
                contained = lower <= image_lower and image_upper <= upper
                radius = (upper - lower) / 2
                base = (lower + upper) / 2
                deviation = max(abs(image_lower - base), abs(image_upper - base))
                ratio = deviation / radius if radius else (Fraction(0) if deviation == 0 else None)
                if ratio is not None:
                    maximum_ratio = max(maximum_ratio, ratio)
                containment.append({"index": index, "component": component,
                                    "contained": contained, "ratio_exact": None if ratio is None else str(ratio),
                                    "image_lower_exact": str(image_lower), "image_upper_exact": str(image_upper),
                                    "lower_margin_exact": str(image_lower - lower),
                                    "upper_margin_exact": str(upper - image_upper)})
        channels.append({"all_components_contained": all(row["contained"] for row in containment),
                         "maximum_finite_ratio_exact": str(maximum_ratio), "components": containment})
    return {"eta_exact": str(eta), "row_bounds_exact": [str(value) for value in row_bounds],
            "neumann_pass": True, "channels": channels,
            "coefficient_boxes_invariant": all(channel["all_components_contained"] for channel in channels)}


def run(path):
    payload = json.loads(path.read_text())
    if payload.get("record") != 2351 or payload.get("dimension") != 30:
        raise ValueError("unexpected moment-witness scope")
    validate_owner(payload)
    matrix = [[complex_interval(value) for value in row] for row in payload["matrix"]]
    inverse = [[complex_interval(value) for value in row] for row in payload["candidate_inverse"]]
    rhs = [[complex_interval(value) for value in row] for row in payload["right_hand_sides"]]
    boxes = [[complex_interval(value) for value in row] for row in payload["coefficient_rectangles"]]
    if len(matrix) != 30 or len(rhs) != 2:
        raise ValueError("unexpected witness matrix/channel count")
    result = verify(matrix, inverse, rhs, boxes)
    result.update({"record": 2351, "status": "EXACT_NEUMANN_AND_BOX_PASS" if result["coefficient_boxes_invariant"]
                   else "EXACT_NEUMANN_PASS_BOX_NOT_CERTIFIED",
                   "arithmetic": "Python Fraction rational intervals; no Arb or binary64 operations",
                   "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "witness_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                   "analytic_matrix_enclosures_imported_in_lean": False,
                   "coefficient_realization_imported_in_lean": False,
                   "healthy_detector_instantiated": False, "producer_go": False, "rh_claim": False})
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=ROOT / "results/2351_moment_matrix_witness.json")
    parser.add_argument("--output", type=Path, default=ROOT / "results/2351_moment_matrix_exact_check.json")
    arguments = parser.parse_args()
    result = run(arguments.input)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], "eta", float(Fraction(result["eta_exact"])),
          "max box ratios", [float(Fraction(channel["maximum_finite_ratio_exact"]))
                             for channel in result["channels"]], flush=True)
