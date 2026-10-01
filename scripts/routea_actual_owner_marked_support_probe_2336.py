"""2336: actual source marked-value and support-composition decision probe.

This is a diagnostic, not an interpolation or Fourier inversion certificate.
Stored coefficient hashes are checked; no coefficients are solved anew.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"


def decode_pairs(values):
    return [complex(float.fromhex(real), float.fromhex(imag))
            for real, imag in values]


def get_support_geometry(families, iterate_index):
    if iterate_index < 0:
        raise ValueError("iterate_index must be nonnegative")
    radius = max(Fraction(width) ** 2 for width, _ in families)
    source_radius = (iterate_index + 2) * radius
    square_radius = 2 * source_radius
    return {
        "iterate_index": iterate_index,
        "base_copy_count": iterate_index + 1,
        "factor_radius_exact": str(radius),
        "source_radius_upper_exact": str(source_radius),
        "square_radius_upper_exact": str(square_radius),
        "single_factor_square_radius_exact": str(2 * radius),
        "source_radius_upper_float": float(source_radius),
        "square_radius_upper_float": float(square_radius),
        "covering_cutoff_scale_diagnostic": math.exp(float(square_radius)),
        "scope": "support upper bounds only; not exact nonzero prime set",
    }


def get_square_values(source_values, companion_indices):
    if len(source_values) != len(companion_indices):
        raise ValueError("companion index count mismatch")
    return [source_values[index].conjugate() * value
            for value, index in zip(source_values, companion_indices)]


def get_companion_indices(nodes):
    output = []
    for node in nodes:
        companion = 1 - node.conjugate()
        matches = [index for index, candidate in enumerate(nodes)
                   if abs(candidate - companion) < 1e-12]
        if len(matches) != 1:
            raise ValueError("missing or ambiguous companion node")
        output.append(matches[0])
    return output


def encode_complex(value):
    return {"real": float(value.real), "imag": float(value.imag)}


def evaluate_factors(families, base, correction, nodes, rule, order):
    import numpy as np
    from scipy.special import roots_legendre

    results = [[], []]
    contributions = [[], []]
    for family_index, (width, modulation) in enumerate(families):
        radius = width * width
        if rule == "gauss":
            roots, weights = roots_legendre(order)
            edges = np.linspace(-radius, radius, 33)
            half = (edges[1:] - edges[:-1]) / 2
            centers = (edges[1:] + edges[:-1]) / 2
            points = (centers[:, None] + half[:, None] * roots).ravel()
            weights = (half[:, None] * weights).ravel()
        elif rule == "trapezoid":
            points = np.linspace(-radius, radius, order + 1)
            weights = np.full(order + 1, 2 * radius / order)
            weights[[0, -1]] /= 2
        else:
            raise ValueError("unknown quadrature rule")
        quotient = 1 - (points / radius) ** 2
        profile = np.zeros_like(points)
        inside = quotient > 0
        profile[inside] = np.exp(-30 / quotient[inside])
        transformed = []
        for node in nodes:
            terms = profile * weights * np.exp((node + 1j * modulation) * points)
            transformed.append(complex(math.fsum(terms.real), math.fsum(terms.imag)))
        for channel, coefficients in enumerate((base, correction)):
            contributions[channel].append(
                [coefficients[family_index] * value for value in transformed])
    for channel in range(2):
        for node_index in range(len(nodes)):
            terms = [row[node_index] for row in contributions[channel]]
            results[channel].append(complex(
                math.fsum(term.real for term in terms),
                math.fsum(term.imag for term in terms)))
    return results


def run_probe():
    import numpy as np

    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(float.fromhex(width), float.fromhex(modulation))
                for width, modulation in capture["families_hex"]]
    base = decode_pairs(capture["base_hex"])
    correction = decode_pairs(capture["corr_hex"])
    if len(families) != 30 or len(base) != 30 or len(correction) != 30:
        raise ValueError("expected the captured 30-family owner")
    for name, coefficients in (("base", base), ("corr", correction)):
        digest = hashlib.md5(np.asarray(coefficients, dtype=np.complex128).tobytes()).hexdigest()
        if digest != capture[name + "_md5"]:
            raise ValueError("stored coefficient hash mismatch")
    captured_nodes = decode_pairs(capture["nodes_hex"])
    targets = decode_pairs(capture["values_hex"])
    rho = captured_nodes[0]
    nodes = captured_nodes
    companion_indices = get_companion_indices(nodes[:4])
    rules = [("gauss", 32), ("gauss", 64), ("trapezoid", 16384)]
    evaluations = [evaluate_factors(families, base, correction, nodes, rule, order)
                   for rule, order in rules]
    reference_base, reference_correction = evaluations[1]
    disagreement = max(abs(value - reference)
                       for evaluation in (evaluations[0], evaluations[2])
                       for channel, references in zip(evaluation, evaluations[1])
                       for value, reference in zip(channel, references))
    base_residual = max(abs(value - 1) for value in reference_base)
    correction_residual = max(abs(value - target)
                              for value, target in zip(reference_correction, targets))
    rows = []
    for iterate_index in (0, 1, 2):
        source_values = [value ** (iterate_index + 1) * correction_value
                         for value, correction_value in
                         zip(reference_base, reference_correction)]
        square_values = get_square_values(source_values[:4], companion_indices)
        rows.append({
            "iterate_index": iterate_index,
            "source_max_target_residual_diagnostic": max(
                abs(value - target) for value, target in zip(source_values, targets)),
            "marked_square_values_diagnostic": [encode_complex(value) for value in square_values],
            "orbit_sum_diagnostic": encode_complex(sum(square_values)),
            "support_geometry": get_support_geometry(families, iterate_index),
        })
    node_readbacks = []
    for index, (node, target) in enumerate(zip(nodes, targets)):
        node_readbacks.append({
            "index": index,
            "node": encode_complex(node),
            "target": encode_complex(target),
            "base_diagnostic": encode_complex(reference_base[index]),
            "correction_diagnostic": encode_complex(reference_correction[index]),
            "source_n0_diagnostic": encode_complex(
                reference_base[index] * reference_correction[index]),
            "rule_disagreement_diagnostic": max(
                abs(evaluation[channel][index] - evaluations[1][channel][index])
                for evaluation in (evaluations[0], evaluations[2])
                for channel in range(2)),
        })
    probe_tolerance = 1e-5
    if max(disagreement, base_residual, correction_residual) >= probe_tolerance:
        verdict = "CAPTURED_SOURCE_REQUIRES_REVIEW"
    else:
        verdict = "CAPTURED_SOURCE_MARKED_VALUES_DIAGNOSTICALLY_RETAINED"
    return {
        "record": 2336,
        "verdict": verdict,
        "rho": encode_complex(rho),
        "rho_is_source_zero_proved": False,
        "finite_node_completeness_proved": False,
        "node_count": len(nodes),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "probe_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "base_md5": capture["base_md5"],
        "corr_md5": capture["corr_md5"],
        "rules": [{"rule": rule, "order": order} for rule, order in rules],
        "rule_disagreement_diagnostic": disagreement,
        "base_max_target_residual_diagnostic": base_residual,
        "correction_max_target_residual_diagnostic": correction_residual,
        "probe_tolerance": probe_tolerance,
        "node_readbacks": node_readbacks,
        "rows": rows,
        "support_certification_scope": "Lean pin radius; exact max-width fractions are formula diagnostics",
        "quadrature_certified": False,
        "kernel_scope_decision": "2R book is not the composed-source support-cover book",
        "actual_nonzero_prime_set_identified": False,
        "interpolation_certified": False,
        "healthy_detector_instantiated": False,
        "fourier_inversion_proved": False,
        "producer_go": False,
        "rh_claim": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "results/2336_actual_owner_marked_support_probe.json")
    args = parser.parse_args()
    result = run_probe()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
