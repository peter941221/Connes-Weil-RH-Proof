"""Record 2275: exact refinement counterexample and same-owner capture.

No full-grid experiment is run. --capture-owner reconstructs only the 2249
interpolation matrix and gates both coefficient hashes against that record.
The output is an audit, not an analytic hgap certificate.
"""
import argparse
import ast
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import struct

ROOT = Path(__file__).resolve().parents[1]
INPUTS = (
    "scripts/routea_weighted_zero_l1_enclosure_2249.py",
    "scripts/routea_weighted_zero_l1_gaps_2255.py",
    "results/2249_l1_enclosure.json",
    "results/2255_l1_gaps.json",
)


def source_dependencies():
    pending = [ROOT / "scripts/routea_gap_owner_audit_2275.py"]
    found = set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        found.add(path)
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            modules = [alias.name for alias in node.names] if isinstance(node, ast.Import) else (
                [node.module] if isinstance(node, ast.ImportFrom) and node.module else [])
            for module in modules:
                candidate = ROOT / "scripts" / (module + ".py")
                if candidate.is_file():
                    pending.append(candidate)
    return {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(found)}


def polynomial_value(x, amplitude):
    return amplitude * x * (1 - x) * (x - Fraction(1, 2)) ** 2


def refinement_counterexample(amplitude=Fraction(2400000000)):
    amplitude = Fraction(amplitude)
    coarse = (polynomial_value(Fraction(0), amplitude)
              + polynomial_value(Fraction(1), amplitude)) / 2
    fine = (polynomial_value(Fraction(0), amplitude)
            + 2 * polynomial_value(Fraction(1, 2), amplitude)
            + polynomial_value(Fraction(1), amplitude)) / 4
    integral = amplitude * (
        -Fraction(1, 5) + Fraction(1, 2)
        - Fraction(5, 12) + Fraction(1, 8))
    return coarse, fine, integral


def dyadic_period_exponent(frequencies):
    exponent = 0
    for frequency in frequencies:
        denominator = Fraction(frequency).denominator
        if denominator & (denominator - 1):
            raise ValueError("frequency is not dyadic")
        exponent = max(exponent, denominator.bit_length() - 1)
    return exponent


def check_refinement_source(source):
    tree = ast.parse(source)
    function = next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef)
                    and node.name == "run_instrumented")
    assignments = {
        ast.unparse(node.targets[0]): ast.unparse(node.value)
        for node in function.body if isinstance(node, ast.Assign)
    }
    return (
        assignments.get("r49.M") == "m"
        and assignments.get("r49._GL_XS") == "None"
        and assignments.get("r49._GL_WS") == "None"
        and assignments.get("a_mat") ==
        "r49.r80.family_values(fam, r49.K, np.asarray(nodes, complex), xw).T"
        and assignments.get("base") ==
        "np.linalg.solve(a_mat, np.ones(len(nodes), complex))"
        and assignments.get("corr") ==
        "np.linalg.solve(a_mat, np.asarray(values, complex))"
        and [arg.arg for arg in function.args.args] ==
        ["m", "grid", "chunk", "tag"]
    )


def capture_owner():
    import numpy as np
    import routea_weighted_zero_l1_enclosure_2249 as owner

    owner.M = 6400
    owner._GL_XS = None
    owner._GL_WS = None
    _, nodes, values, families = owner.build()
    cache = {}
    tables = []
    for width, _ in families:
        if width not in cache:
            cache[width] = owner.phi_weights_cached(width)
        tables.append(cache[width])
    matrix = owner.r80.family_values(
        families, owner.K, np.asarray(nodes, complex), tables).T
    base = np.linalg.solve(matrix, np.ones(len(nodes), complex))
    corr = np.linalg.solve(matrix, np.asarray(values, complex))
    baseline = json.loads((ROOT / INPUTS[2]).read_text())["diagnostics"]
    hashes = {
        name + "_md5": hashlib.md5(np.ascontiguousarray(vector).tobytes()).hexdigest()
        for name, vector in (("base", base), ("corr", corr))
    }
    if any(hashes[name] != baseline[name] for name in hashes):
        raise ValueError("2249 coefficient anchor failed; no same-owner capture")
    grid = np.arange(-owner.XMAX, owner.XMAX + owner.STEP / 2, owner.STEP)
    ideal_grid = [Fraction(-40) + Fraction(index, 50) for index in range(len(grid))]
    coordinate_error = max(abs(Fraction(float(point)) - exact)
                           for point, exact in zip(grid, ideal_grid))
    frequencies = [Fraction(float(width)) * Fraction(float(point))
                   for (width, _), (points, _) in zip(families, tables)
                   for point in points]
    exponent = dyadic_period_exponent(frequencies)
    if exponent > 2148:
        raise ValueError("binary64 frequency product bound failed")
    positive_terms = []
    for (width, _), table in zip(families, tables):
        _, terms, _ = owner.phi_terms(width, table)
        if width <= 0 or np.any(terms < 0) or not np.any(terms > 0):
            raise ValueError("positive finite-family witness failed")
        positive_terms.append(int(np.count_nonzero(terms > 0)))
    encode_complex = lambda value: [float(value.real).hex(), float(value.imag).hex()]
    return {
        "status": "SAME-OWNER-COEFFICIENTS-MATCHED",
        "numpy_version": np.__version__,
        **hashes,
        "families_hex": [[float(width).hex(), float(theta).hex()]
                         for width, theta in families],
        "nodes_hex": [encode_complex(value) for value in nodes],
        "values_hex": [encode_complex(value) for value in values],
        "base_hex": [encode_complex(value) for value in base],
        "corr_hex": [encode_complex(value) for value in corr],
        "gl_table_sha256": [hashlib.sha256(
            np.ascontiguousarray(points).tobytes()
            + np.ascontiguousarray(weights).tobytes()).hexdigest()
            for points, weights in tables],
        "frequency_period_exponent": exponent,
        "positive_term_counts": positive_terms,
        "period_convention": "T = (mathematical pi / stored math.pi) * 2^exponent",
        "coordinate_error_exact": str(coordinate_error),
        "coordinate_error_float_diagnostic": float(coordinate_error),
        "capture_scope": "coefficients, table hashes and grid coordinates only; not q replay",
    }


def verify_capture(captured, baseline):
    if captured["status"] != "SAME-OWNER-COEFFICIENTS-MATCHED":
        raise ValueError("invalid owner capture status")
    count = baseline["families"]
    for name in ("families_hex", "nodes_hex", "values_hex", "base_hex", "corr_hex",
                 "gl_table_sha256", "positive_term_counts"):
        if len(captured[name]) != count:
            raise ValueError("owner capture shape mismatch")
    for name in ("base", "corr"):
        data = b"".join(struct.pack("=dd", *(float.fromhex(part) for part in value))
                        for value in captured[name + "_hex"])
        digest = hashlib.md5(data).hexdigest()
        if digest != baseline[name + "_md5"] or digest != captured[name + "_md5"]:
            raise ValueError("serialized owner coefficient anchor failed")
    if not 0 <= captured["frequency_period_exponent"] <= 2148:
        raise ValueError("owner period exponent out of range")
    if min(captured["positive_term_counts"]) <= 0:
        raise ValueError("missing positive finite-family witness")


def build_audit(captured=None):
    source = (ROOT / INPUTS[1]).read_text(encoding="utf-8")
    if not check_refinement_source(source):
        raise ValueError("2255 source shape changed; review the owner audit")
    coarse, fine, integral = refinement_counterexample()
    if coarse != 0 or fine != 0 or integral <= 10000000:
        raise ValueError("exact refinement counterexample failed")
    artifact = json.loads((ROOT / INPUTS[3]).read_text())
    channels = [artifact[name]["gap_charged"] for name in ("quad", "window", "step")]
    if sum(channels) != artifact["total"]["total_gap_charged"]:
        raise ValueError("2255 channel ledger does not reproduce")
    if captured is not None:
        verify_capture(captured, json.loads((ROOT / INPUTS[2]).read_text())["diagnostics"])
    return {
        "record": 2275,
        "status": "REFINEMENT-INFERENCE-NO-GO",
        "hgap_closed": False,
        "scope": "refinement-only and finite-rule-tail inferences; not the actual ideal gap",
        "source_control": "2255 resets M and solves both coefficient vectors anew",
        "counterexample": {
            "function": "A*x*(1-x)*(x-1/2)^2 on [0,1]",
            "amplitude": "2400000000",
            "coarse_trapezoid_exact": str(coarse),
            "fine_trapezoid_exact": str(fine),
            "true_integral_exact": str(integral),
        },
        "finite_rule": {
            "universal_binary64_product_period_exponent": 2148,
            "nondecay_scope": "every nonzero exact finite family sum is periodic, hence cannot tend to zero",
            "exception": "an identically zero sum is not excluded by periodicity alone",
        },
        "trapezoid_target": {
            "window_length": "80", "exact_step": "1/50",
            "bound": "error <= sup_window_abs_G_second / 375",
            "derivative_cap_if_whole_budget_assigned": "sup_window_abs_G_second <= 3750000000",
            "scope": "C2 exact-uniform-grid term only, using the entire 1e7 budget",
        },
        "historical_measured_gap": artifact["total"]["total_gap_charged"],
        "owner_capture": captured,
        "input_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                         for path in INPUTS},
        "source_dependency_sha256": source_dependencies(),
        "nonclaims": ["no bound on the actual ideal-to-discrete gap",
                      "no producer GO or RH claim", "no new Lean theorem"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-owner", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "results/2275_gap_owner_audit.json")
    args = parser.parse_args()
    if args.capture_owner:
        captured = capture_owner()
    elif args.output.is_file():
        previous = json.loads(args.output.read_text())
        if previous["source_dependency_sha256"] != source_dependencies():
            raise ValueError("capture sources changed; rerun with --capture-owner")
        captured = previous["owner_capture"]
    else:
        captured = None
    result = build_audit(captured)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"])
    if result["owner_capture"]:
        print(result["owner_capture"]["status"])


if __name__ == "__main__":
    main()
