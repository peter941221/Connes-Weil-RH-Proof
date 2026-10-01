"""2337: independent exact-rational postprocessing of Arb factor enclosures.

This checks sign arithmetic and provenance, not the integration engine itself.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def get_interval(record):
    lower, upper = Fraction(record["lower_exact"]), Fraction(record["upper_exact"])
    if lower > upper:
        raise ValueError("reversed interval")
    return lower, upper


def get_rectangle(record):
    return get_interval(record["real"]), get_interval(record["imag"])


def add_intervals(first, second):
    return first[0] + second[0], first[1] + second[1]


def negate_interval(interval):
    return -interval[1], -interval[0]


def multiply_intervals(first, second):
    products = [left * right for left in first for right in second]
    return min(products), max(products)


def multiply_rectangles(first, second):
    real = add_intervals(multiply_intervals(first[0], second[0]),
                         negate_interval(multiply_intervals(first[1], second[1])))
    imag = add_intervals(multiply_intervals(first[0], second[1]),
                         multiply_intervals(first[1], second[0]))
    return real, imag


def conjugate_rectangle(rectangle):
    return rectangle[0], negate_interval(rectangle[1])


def contains_point(rectangle, point):
    return all(interval[0] <= coordinate <= interval[1]
               for interval, coordinate in zip(rectangle, point))


def verify_certificate(artifact):
    capture_path = ROOT / "results/2275_gap_owner_audit.json"
    source_path = ROOT / "scripts/routea_marked_sign_arb_certificate_2337.py"
    for path, key in ((capture_path, "capture_sha256"), (source_path, "source_sha256")):
        if hashlib.sha256(path.read_bytes()).hexdigest() != artifact[key]:
            raise ValueError("certificate provenance mismatch")
    if artifact["status"] != "CAPTURED_MARKED_SIGN_CERTIFIED_ONLY":
        raise ValueError("unexpected certificate status")
    if any(artifact[key] for key in ("healthy_detector_instantiated", "producer_go", "rh_claim")):
        raise ValueError("unsupported producer claim")
    capture = json.loads(capture_path.read_text())["owner_capture"]
    rows = artifact["mandatory_nodes"]
    if [row["index"] for row in rows] != list(range(8)):
        raise ValueError("mandatory-node order mismatch")
    source_rectangles = []
    exclusions = []
    for index, row in enumerate(rows):
        node = tuple(Fraction(float.fromhex(value)) for value in capture["nodes_hex"][index])
        target = tuple(Fraction(float.fromhex(value)) for value in capture["values_hex"][index])
        if not contains_point(get_rectangle(row["node"]), node):
            raise ValueError("source-node mismatch")
        if not contains_point(get_rectangle(row["nominal_target"]), target):
            raise ValueError("source-target mismatch")
        source = multiply_rectangles(get_rectangle(row["base"]), get_rectangle(row["correction"]))
        source_rectangles.append(source)
        if not contains_point(source, target):
            exclusions.append(index)
    square_rectangles = [multiply_rectangles(conjugate_rectangle(source_rectangles[companion]),
                                            source_rectangles[index])
                         for index, companion in enumerate((1, 0, 3, 2))]
    if not all(rectangle[0][1] < -Fraction(99, 100) for rectangle in square_rectangles[:2]):
        raise ValueError("independent marked-sign gate failed")
    orbit_upper = sum(rectangle[0][1] for rectangle in square_rectangles)
    if not orbit_upper < -Fraction(19, 10):
        raise ValueError("independent orbit-sign gate failed")
    if exclusions != artifact["source_nominal_target_exclusions"]:
        raise ValueError("independent target exclusion mismatch")
    if exclusions != list(range(8)):
        raise ValueError("expected all eight exact targets to be excluded")
    return {"record": 2337, "status": "RATIONAL_POSTPROCESS_PASS",
            "marked_real_upper_exact": [str(rectangle[0][1]) for rectangle in square_rectangles[:2]],
            "orbit_real_upper_exact": str(orbit_upper), "source_target_exclusions": exclusions,
            "integration_engine_reproved": False, "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=ROOT / "results/2337_marked_sign_certificate.json")
    parser.add_argument("--output", type=Path, default=ROOT / "results/2337_rational_postprocess.json")
    args = parser.parse_args()
    result = verify_certificate(json.loads(args.certificate.read_text()))
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(result["status"], "exact target exclusions", result["source_target_exclusions"])
