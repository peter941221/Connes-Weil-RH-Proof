"""2295: finite-window direct functional-difference diagnostic.

Compares a numerical stored-owner GL reference with the phase-aware Filon
transform on the same xi grid and forms the signed functional difference before
any absolute-value majorant. It is a diagnostic, not an interval certificate.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np

import routea_phase_centered_filon_tail_screen_2280 as filon

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2295_direct_functional_difference_screen.json"


def reference_transform(xi, families, coefficients, panels, nodes_per_panel):
    half = max(width*width for width, _ in families)
    edges = np.linspace(-half, half, panels + 1)
    nodes, weights = np.polynomial.legendre.leggauss(nodes_per_panel)
    output = np.zeros_like(xi, dtype=complex)
    for left, right in zip(edges[:-1], edges[1:]):
        centre = (left + right)/2
        half_panel = (right - left)/2
        y = centre + half_panel*nodes
        amplitudes = filon.owner_values(y, families, coefficients)
        phase = np.exp(-2j*np.pi*xi[:, None]*y[None, :])
        output += half_panel*(phase @ (weights*amplitudes))
    return output


def functional(xi, base_transform, corr_transform, kernel):
    return kernel*np.abs(filon.annihilator(xi))**2*np.abs(base_transform)**2*np.abs(corr_transform)**2


def run(panels, degree, nodes_per_panel, xi_max, xi_step):
    capture, families, base, corr = filon.load_owner()
    half_points = round(xi_max/xi_step)
    if not math.isclose(half_points*xi_step, xi_max, rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError("window endpoint must be an integer multiple of the grid step")
    xi = np.arange(-half_points, half_points + 1)*xi_step
    base_exact = reference_transform(xi, families, base, panels, nodes_per_panel)
    corr_exact = reference_transform(xi, families, corr, panels, nodes_per_panel)
    base_filon = filon.filon_transform(xi, families, base, panels, degree)
    corr_filon = filon.filon_transform(xi, families, corr, panels, degree)
    kernel, prime_count = filon.prime_kernel(xi, 2*max(width*width for width, _ in families))
    exact_value = functional(xi, base_exact, corr_exact, kernel)
    filon_value = functional(xi, base_filon, corr_filon, kernel)
    difference = exact_value - filon_value
    return {
        "panels": panels, "degree": degree, "nodes_per_panel": nodes_per_panel,
        "xi_max": xi_max, "xi_step": xi_step, "xi_points": int(xi.size),
        "prime_power_count": prime_count,
        "reference_signed_integral": float(np.trapezoid(exact_value, xi)),
        "filon_signed_integral": float(np.trapezoid(filon_value, xi)),
        "direct_signed_difference": float(np.trapezoid(difference, xi)),
        "direct_absolute_difference": float(np.trapezoid(np.abs(difference), xi)),
        "reference_absolute_mass": float(np.trapezoid(np.abs(exact_value), xi)),
        "filon_absolute_mass": float(np.trapezoid(np.abs(filon_value), xi)),
        "base_transform_difference_max": float(np.max(np.abs(base_exact-base_filon))),
        "corr_transform_difference_max": float(np.max(np.abs(corr_exact-corr_filon))),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--xi-max", type=float, default=40.0)
    parser.add_argument("--xi-step", type=float, default=0.02)
    parser.add_argument("--steps", default="")
    parser.add_argument("--profiles", default="24:4:256,24:4:512,24:6:256")
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    if args.xi_max <= 0 or args.xi_step <= 0:
        parser.error("xi maximum and step must be positive")
    steps = [float(value) for value in args.steps.split(",")] if args.steps else [args.xi_step]
    if any(value <= 0 for value in steps):
        parser.error("all grid steps must be positive")
    rows = []
    for step in steps:
        for item in args.profiles.split(","):
            panels, degree, nodes = map(int, item.split(":"))
            if panels <= 0 or degree <= 0 or nodes <= 0:
                parser.error("profile entries must be positive")
            rows.append(run(panels, degree, nodes, args.xi_max, step))
    budget = 10000000.0
    for row in rows:
        row["sampled_signed_difference_to_budget"] = abs(row["direct_signed_difference"])/budget
    result = {
        "record": 2295, "status": "DIRECT-FUNCTIONAL-DIFFERENCE-SCREEN",
        "diagnostic_budget": budget,
        "sampled_profiles_accepted": all(row["sampled_signed_difference_to_budget"] <= 1 for row in rows),
        "certificate": False, "hgap_closed": False, "rows": rows,
        "scope": "same-grid sampled direct difference for the captured owner; no interval or integral verdict",
        "input_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in (filon.CAPTURE, Path(filon.__file__), Path(__file__))},
        "instrument_repairs": ["integer-index grid has exact zero frequency",
                               "small-alpha moment power series replaces unstable division recurrence"],
        "nonclaims": ["GL transform is a numerical reference, not an analytic oracle",
                      "finite xi window only", "floating grid is not a quadrature certificate",
                      "no directed transform enclosure or ideal-to-discrete bridge",
                      "no hgap supplier, producer GO or RH claim"]}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps([{key: row[key] for key in ("degree", "nodes_per_panel", "direct_signed_difference", "direct_absolute_difference", "prime_power_count")} for row in rows]))


if __name__ == "__main__":
    main()
