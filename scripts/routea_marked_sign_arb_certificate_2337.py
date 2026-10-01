"""2337: Arb certification of the captured source's eight mandatory nodes.

The endpoint slices are bounded separately. No sampled error is promoted to
an enclosure, no coefficients are changed, and no source-zero claim is made.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import struct
import time

import flint
from flint import acb, arb, ctx

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
PRECISION_BITS = 256
EDGE_DELTA = Fraction(1, 64)
MANDATORY_NODE_COUNT = 8


def lift_fraction(value):
    value = Fraction(value)
    return arb(value.numerator) / arb(value.denominator)


def lift_float(value):
    if not isinstance(value, float):
        raise TypeError("stored binary64 operand required")
    return lift_fraction(Fraction(value))


def decode_complex(pair):
    real, imag = (float.fromhex(value) for value in pair)
    return acb(lift_float(real), lift_float(imag))


def get_integrand(radius, source_point, modulation):
    exponent = (source_point + acb(0, modulation)) * radius

    def integrand(coordinate, analytic):
        denominator = 1 - coordinate * coordinate
        if denominator.contains(0):
            return acb("nan")
        return (-30 / denominator + exponent * coordinate).exp()

    return integrand


def get_edge_charge(radius, source_point, delta=EDGE_DELTA):
    if not 0 < Fraction(delta) < 1:
        raise ValueError("edge delta must be strictly between zero and one")
    delta = lift_fraction(delta)
    return 2 * delta * radius * (
        -30 / (delta * (2 - delta)) + abs(source_point.real) * radius).exp()


def add_complex_error(value, error):
    radius = arb(0, error.upper())
    return value + acb(radius, radius)


def integrate_family(width, modulation, source_point, panels=16):
    radius = width * width
    cut = lift_fraction(1 - EDGE_DELTA)
    callback = get_integrand(radius, source_point, modulation)
    total = acb(0)
    for panel in range(panels):
        left = -cut + 2 * cut * panel / panels
        right = -cut + 2 * cut * (panel + 1) / panels
        value = acb.integral(callback, left, right,
                             rel_tol=arb("1e-55"), abs_tol=arb("1e-65"),
                             depth_limit=40, eval_limit=100000)
        if not value.is_finite():
            raise RuntimeError("nonfinite interior integral")
        total += radius * value
    edge_charge = get_edge_charge(radius, source_point)
    return add_complex_error(total, edge_charge), edge_charge


def serialize_real(value):
    if not value.is_finite():
        raise ValueError("nonfinite real ball cannot be exported")
    return {"lower_exact": str(value.lower().fmpq()),
            "upper_exact": str(value.upper().fmpq()),
            "display": value.str(50)}


def serialize_complex(value):
    return {"real": serialize_real(value.real), "imag": serialize_real(value.imag)}


def load_capture():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(lift_float(float.fromhex(width)), lift_float(float.fromhex(modulation)))
                for width, modulation in capture["families_hex"]]
    coefficients = []
    for name in ("base", "corr"):
        pairs = capture[name + "_hex"]
        raw = b"".join(struct.pack("=dd", *(float.fromhex(value) for value in pair))
                       for pair in pairs)
        if hashlib.md5(raw).hexdigest() != capture[name + "_md5"]:
            raise ValueError("coefficient hash mismatch")
        coefficients.append([decode_complex(pair) for pair in pairs])
    if len(families) != 30 or any(len(values) != 30 for values in coefficients):
        raise ValueError("expected captured 30-family source")
    nodes = [decode_complex(pair) for pair in capture["nodes_hex"][:MANDATORY_NODE_COUNT]]
    targets = [decode_complex(pair) for pair in capture["values_hex"][:MANDATORY_NODE_COUNT]]
    if len(nodes) != MANDATORY_NODE_COUNT or len(targets) != MANDATORY_NODE_COUNT:
        raise ValueError("missing mandatory nodes")
    for index, companion in enumerate((1, 0, 3, 2)):
        if not (nodes[companion] - (1 - nodes[index].conjugate())).is_zero():
            raise ValueError("captured companion is not the exact source companion")
    return capture, families, coefficients, nodes, targets


def run_certificate(panels=16, smoke=False):
    ctx.prec = PRECISION_BITS
    start = time.monotonic()
    capture, families, coefficients, nodes, targets = load_capture()
    if smoke:
        value, edge = integrate_family(*families[0], nodes[0], panels)
        second, _ = integrate_family(*families[0], nodes[0], panels * 2)
        if not value.overlaps(second):
            raise RuntimeError("independent partition enclosures disagree")
        return {"record": 2337, "status": "SMOKE_ONLY", "family": serialize_complex(value),
                "edge": serialize_real(edge), "partition_overlap": True}
    rows = []
    source_values = []
    for node_index, (node, target) in enumerate(zip(nodes, targets)):
        base_value, correction_value = acb(0), acb(0)
        base_edges, correction_edges = arb(0), arb(0)
        for family_index, family in enumerate(families):
            transformed, edge = integrate_family(*family, node, panels)
            base_coefficient = coefficients[0][family_index]
            correction_coefficient = coefficients[1][family_index]
            base_value += base_coefficient * transformed
            correction_value += correction_coefficient * transformed
            base_edges += abs(base_coefficient) * edge
            correction_edges += abs(correction_coefficient) * edge
        source_value = base_value * correction_value
        radii = (base_value.real.rad(), base_value.imag.rad(),
                 correction_value.real.rad(), correction_value.imag.rad())
        if not all(radius < arb("1e-35") for radius in radii):
            raise RuntimeError("mandatory-node enclosure too wide")
        source_values.append(source_value)
        rows.append({
            "index": node_index, "node": serialize_complex(node),
            "nominal_target": serialize_complex(target),
            "base": serialize_complex(base_value), "correction": serialize_complex(correction_value),
            "source_n0": serialize_complex(source_value),
            "base_residual": serialize_complex(base_value - 1),
            "correction_residual": serialize_complex(correction_value - target),
            "source_residual": serialize_complex(source_value - target),
            "base_contains_one": bool(base_value.contains(1)),
            "correction_contains_target": bool(correction_value.contains(target)),
            "source_contains_target": bool(source_value.contains(target)),
            "base_edge_charge": serialize_real(base_edges),
            "correction_edge_charge": serialize_real(correction_edges),
        })
        print("certified mandatory node", node_index, "source", source_value,
              "contains nominal target", rows[-1]["source_contains_target"], flush=True)
    square_values = [source_values[companion].conjugate() * source_values[index]
                     for index, companion in enumerate((1, 0, 3, 2))]
    orbit_sum = sum(square_values, acb(0))
    if not all(value.real < arb("-99/100") for value in square_values[:2]):
        raise RuntimeError("marked square negative-sign gate failed")
    if not orbit_sum.real < arb("-19/10"):
        raise RuntimeError("four-point negative-sum gate failed")
    return {
        "record": 2337, "status": "CAPTURED_MARKED_SIGN_CERTIFIED_ONLY",
        "python_flint_version": flint.__version__, "precision_bits": PRECISION_BITS,
        "panels": panels, "edge_delta_exact": str(EDGE_DELTA),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "base_md5": capture["base_md5"], "corr_md5": capture["corr_md5"],
        "mandatory_nodes": rows,
        "square_values_n0": [serialize_complex(value) for value in square_values],
        "orbit_sum_n0": serialize_complex(orbit_sum),
        "marked_real_lt_minus_99_over_100": True,
        "orbit_real_lt_minus_19_over_10": True,
        "source_nominal_target_exclusions": [row["index"] for row in rows
                                              if not row["source_contains_target"]],
        "exact_interpolation_established": False,
        "healthy_detector_instantiated": False, "finite_zero_node_completeness_proved": False,
        "rho_is_source_zero_proved": False, "complete_kernel_sign_proved": False,
        "lean_imported_certificate": False, "producer_go": False, "rh_claim": False,
        "elapsed_seconds": time.monotonic() - start,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--panels", type=int, default=16)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.panels < 1:
        parser.error("panels must be positive")
    output = args.output or ROOT / ("results/2337_marked_sign_smoke.json" if args.smoke
                                  else "results/2337_marked_sign_certificate.json")
    result = run_certificate(args.panels, args.smoke)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("artifact", output, "status", result["status"], flush=True)
