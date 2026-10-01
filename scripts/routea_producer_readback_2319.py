"""Exact source/readback and cutoff controls for record 2319.

This is a scoped obstruction to identifying the P-only auxiliary square
with the selected negative-orbit detector. It does not compute a Weil sign,
instantiate an actual off-line zero, or reopen the frozen four-point family.
"""

import ast
import hashlib
import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results/2319_producer_readback.json"
HALF = (Fraction(1, 2), Fraction(0))
ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))


def subtract(left, right):
    return (left[0] - right[0], left[1] - right[1])


def multiply(left, right):
    return (left[0] * right[0] - left[1] * right[1],
            left[0] * right[1] + left[1] * right[0])


def conjugate(value):
    return (value[0], -value[1])


def decode_complex(pair):
    return tuple(Fraction.from_float(float.fromhex(component)) for component in pair)


def orbit_nodes(rho):
    raw_nodes = (rho, subtract(ONE, conjugate(rho)), conjugate(rho), subtract(ONE, rho))
    return tuple(subtract(node, HALF) for node in raw_nodes)


def polynomial_value(nodes, argument):
    product = ONE
    for node in nodes:
        product = multiply(product, subtract(node, argument))
    return product


def squared_polynomial_value(nodes, argument):
    paired = (-argument[0], argument[1])
    return multiply(conjugate(polynomial_value(nodes, paired)),
                    polynomial_value(nodes, argument))


def encode_complex(value):
    return [str(component) for component in value]


def function_source(path, name):
    text = path.read_text(encoding="utf-8")
    tree = ast.parse(text)
    declaration = next(node for node in tree.body
                       if isinstance(node, ast.FunctionDef) and node.name == name)
    return ast.get_source_segment(text, declaration), declaration


def check_source_shapes():
    counterpart_source, counterpart = function_source(
        ROOT / "scripts/fourpoint_owner_completion_1980.py", "counterpart_nodes")
    expected = ast.parse(
        "[rho - 0.5, (1 - np.conj(rho)) - 0.5, "
        "np.conj(rho) - 0.5, (1 - rho) - 0.5]", mode="eval").body
    actual = next(node.value for node in counterpart.body if isinstance(node, ast.Return))
    if ast.dump(actual) != ast.dump(expected):
        raise AssertionError("counterpart_nodes no longer has the audited four roots")
    polynomial_source, _ = function_source(
        ROOT / "scripts/fourpoint_owner_density_1959.py", "P_from_nodes")
    evaluation_source, _ = function_source(
        ROOT / "scripts/routea_full_known_prefix_direct_owner_grid_m6400_2103.py", "evaluate")
    enclosure_source = (ROOT / "scripts/routea_weighted_zero_l1_enclosure_2249.py").read_text(
        encoding="utf-8")
    four_point_source = (ROOT / "ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean").read_text(
        encoding="utf-8")
    source_multiplier = "".join(four_point_source.split())
    checks = {
        "counterpart_roots_ast": True,
        "polynomial_imaginary_argument": "s = -2j * np.pi * np.asarray(xi)" in polynomial_source,
        "polynomial_root_product": "p = p * (a - s)" in polynomial_source,
        "screen_half_density": "0.5 - 2j * np.pi * grid" in evaluation_source,
        "screen_p_squared": "kernel * p * p * np.abs(base @ v) ** 2" in evaluation_source,
        "screen_legacy_support": "support = 2 * max(a for a, _theta in fam)" in evaluation_source,
        "enclosure_p_squared": "p2, ep2 = m2(p, ep, p, ep)" in enclosure_source,
        "enclosure_legacy_support": "support = 2 * max(pair[0] for pair in fam)" in enclosure_source,
        "counterpart_has_no_gain_shift": "lambda" not in counterpart_source,
        "formal_source_four_factor_multiplier":
            "(((1-rho)-1/2-s)*(starrho-1/2-s)*"
            "((1-starrho)-1/2-s)*(rho-1/2-s))" in source_multiplier,
    }
    if not all(checks.values()):
        raise AssertionError(f"source readback guards failed: {checks}")
    return checks


def build_report():
    source_checks = check_source_shapes()
    captured = json.loads((ROOT / "results/2275_gap_owner_audit.json").read_text(
        encoding="utf-8"))["owner_capture"]
    rho = decode_complex(captured["nodes_hex"][0])
    roots = orbit_nodes(rho)
    stored_roots = tuple(subtract(decode_complex(pair), HALF)
                         for pair in captured["nodes_hex"][:4])
    if roots != stored_roots:
        raise AssertionError("stored first-four orbit nodes disagree with exact rho orbit")
    values = [polynomial_value(roots, root) for root in roots]
    squares = [squared_polynomial_value(roots, root) for root in roots]
    if any(value != ZERO for value in values + squares):
        raise AssertionError("orbit annihilation failed in exact rational arithmetic")
    prescribed = [decode_complex(pair) for pair in captured["values_hex"][:2]]
    prescribed_pair = multiply(conjugate(prescribed[1]), prescribed[0])
    if prescribed_pair != (-Fraction(1), Fraction(0)):
        raise AssertionError("captured prescribed values are no longer the negative pair")
    shifted_roots = tuple((root[0] + Fraction(1, 1024), root[1]) for root in roots)
    mutated = polynomial_value(shifted_roots, roots[0])
    if mutated == ZERO:
        raise AssertionError("shifted-root negative control failed to detect target change")
    growth = []
    for cutoff in (0, 1, 2, 4, 8, 16):
        fixed = 4 * Fraction(3, 4) ** cutoff
        growing = 4 * Fraction(4, 3) ** cutoff * Fraction(3, 4) ** cutoff
        if growing != 4:
            raise AssertionError("coefficient-growth control failed")
        growth.append({"cutoff": cutoff, "fixed_coefficient_tail": str(fixed),
                       "growing_coefficient_tail": str(growing),
                       "p_only_marked_gain": "0", "tail_over_marked_gain": None})
    inputs = (
        "results/2275_gap_owner_audit.json", "results/2249_l1_enclosure.json",
        "scripts/fourpoint_owner_completion_1980.py",
        "scripts/fourpoint_owner_density_1959.py",
        "scripts/routea_full_known_prefix_direct_owner_grid_m6400_2103.py",
        "scripts/routea_weighted_zero_l1_enclosure_2249.py",
        "ConnesWeilRH/Dev/C1RouteAProducerReadback.lean",
        "ConnesWeilRH/Dev/C1RouteAProducerReadbackAudit.lean",
        "ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean",
        "scripts/routea_producer_readback_2319.py",
        "scripts/routea_producer_readback_selftest_2319.py",
    )
    return {
        "record": 2319, "date": "2026-10-01",
        "verdict": "P-ONLY-DIRECT-DETECTOR-IDENTIFICATION-NO-GO",
        "growth_verdict": "MARKED-GAIN-ZERO; ACTUAL-OWNER-GROWTH-NOT-INSTANTIATED",
        "scope": "exact P-only multiplier, no meromorphic cancellation or nonzero span shift",
        "source_checks": source_checks,
        "captured_rho_exact": encode_complex(rho),
        "stored_orbit_matches_exact": True,
        "orbit_polynomial_values": [encode_complex(value) for value in values],
        "orbit_square_values": [encode_complex(value) for value in squares],
        "prescribed_pair_square_value": encode_complex(prescribed_pair),
        "prescribed_values_are_not_a_certified_float_solve": True,
        "shifted_root_control_nonzero": encode_complex(mutated),
        "growth_controls": growth,
        "nonclaims": [
            "No assertion that the captured rho is a source zero.",
            "No formal identification of the numeric integral with an exact Weil gate.",
            "No lower bound on a kernel-book change and no invalidation of local certificates.",
            "The growing coefficient sequence is an algebra control, not the actual owner.",
            "No actual selected-owner growth bound, producer GO, or RH claim.",
        ],
        "provenance_sha256": {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in inputs
        },
    }


def main():
    report = build_report()
    OUTPUT.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n",
                      encoding="utf-8", newline="\n")
    print(report["verdict"])
    print(report["growth_verdict"])
    print("RESULT results/2319_producer_readback.json")


if __name__ == "__main__":
    main()
