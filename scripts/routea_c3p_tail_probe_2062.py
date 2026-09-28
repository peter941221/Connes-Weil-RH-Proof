import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_density_1959 as r59
import routea_g8h_basis_comparison_2037 as r37
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
import fourpoint_owner_completion_1980 as r80

OUTPUT = ROOT / "results" / "2062_route_a_c3p_tail_probe.json"
GAMMA, SCALE, K, N, DELTA = r94.G8, 0.88, 30.0, 0, 0.10
PHI_RULE_M = 6400


def build_owner():
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=PHI_RULE_M) for a, _theta in fam]
    a = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a, np.asarray(values, complex))
    support = max(width for width, _ in fam) * (N + 2)
    prime_powers = r59.rig.prime_powers_up_to(math.exp(support))
    return rho, fam, xw, corr, support, prime_powers, solve_info


def integrand(xi, fam, xw, corr, rho, prime_powers):
    s = 0.5 - 2j * np.pi * np.asarray(xi)
    values = r80.family_values(fam, K, s, xw)
    lc = corr @ values
    p = np.real(r59.P_from_nodes(xi, r59.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * np.asarray(xi))
    for number, weight in prime_powers:
        kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * np.asarray(xi) * math.log(number))
    return kernel * p * p * np.abs(lc) ** 2


def integrate_band(lo, hi, step, fam, xw, corr, rho, prime_powers):
    count = int(round((hi - lo) / step))
    grid = np.linspace(lo, hi, count + 1)
    values = integrand(grid, fam, xw, corr, rho, prime_powers)
    return {
        "lo": lo,
        "hi": hi,
        "step": step,
        "signed": float(np.trapezoid(values, grid)),
        "absolute": float(np.trapezoid(np.abs(values), grid)),
        "max_abs_integrand": float(np.max(np.abs(values))),
        "endpoint_abs": [float(abs(values[0])), float(abs(values[-1]))],
        "nodes": len(grid),
    }


def main():
    rho, fam, xw, corr, support, prime_powers, solve_info = build_owner()
    bands = []
    for lo, hi in ((40.0, 60.0), (60.0, 80.0), (80.0, 120.0), (120.0, 160.0)):
        bands.append(integrate_band(lo, hi, 0.01, fam, xw, corr, rho, prime_powers))
    total_abs = sum(row["absolute"] for row in bands)
    result = {
        "record": 2062,
        "status": "TAIL-SURVIVAL-PROBE-M6400",
        "phi_rule_m": PHI_RULE_M,
        "owner": "one-copy G8-H",
        "rho": [float(rho.real), float(rho.imag)],
        "scale": SCALE,
        "support": float(support),
        "book_size": len(prime_powers),
        "solve": solve_info,
        "bands": bands,
        "tail_40_to_160_absolute": total_abs,
        "tail_40_to_160_over_q1600": total_abs / 3.406049871881275e12,
        "nonclaims": [
            "measured tail only; not an interval enclosure",
            "no extrapolation beyond |xi| = 160",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "owner_source": "results/2037_route_a_g8h_basis_comparison.json",
            "l2_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
