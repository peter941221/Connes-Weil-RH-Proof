#!/usr/bin/env python3
"""Record 2137: replace the tail's sampled Re(P) by the exact |P| bound."""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402

OUTPUT = ROOT / "results" / "2137_routea_fixed_r48_absP_screen.json"
K = 30.0
R = 48
X0 = 160.0
XMAX = 1.0e6
N48_UPPER = float(json.loads((ROOT / "results" / "2135_routea_root_partition_lipschitz.json").read_text(encoding="utf-8"))["variation_upper"])


def main() -> None:
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    prime_powers = r59.rig.prime_powers_up_to(math.exp(9.504))
    env = sum(2.0 * weight / math.sqrt(number) for number, weight in prime_powers)
    env += max(abs(float(r59.rig.sigma_vec(np.array([2 * math.pi * x]))[0])) for x in np.linspace(X0, 400, 2000))
    env += 2.0
    family_data = [(float(a), float(theta), abs(b), abs(c)) for (a, theta), b, c in zip(fam, base, corr)]
    centered_nodes = np.asarray(r80.counterpart_nodes(rho), dtype=complex)

    def value_bound(a: float, t: float) -> float:
        log_value = 0.5 * a * a + math.log(N48_UPPER) - (2 * R - 2) * math.log(a) - R * math.log(math.hypot(0.5, t))
        if log_value < -745.0:
            return 0.0
        return math.exp(min(log_value, 700.0))

    def p_mod_bound(x: float) -> float:
        return math.prod(math.hypot(float(node.real), float(node.imag) + 2.0 * math.pi * x) for node in centered_nodes)

    def envelope(x: float) -> float:
        base_bound = 0.0
        correction_bound = 0.0
        for a, theta, base_coefficient, correction_coefficient in family_data:
            bound = value_bound(a, theta - 2 * math.pi * x)
            base_bound += base_coefficient * bound
            correction_bound += correction_coefficient * bound
        return env * p_mod_bound(x) ** 2 * base_bound ** 2 * correction_bound ** 2

    grids = {}
    for points in (5000, 10000, 20000):
        grid = np.geomspace(X0, XMAX, points)
        sides = {}
        for name, sign in (("positive", 1.0), ("negative", -1.0)):
            values_env = np.array([envelope(float(sign * x)) for x in grid])
            integral = float(np.trapezoid(values_env, grid))
            remainder = float(values_env[-1] * grid[-1] / (4 * R - 9))
            sides[name] = {"tail_to_1e6": integral, "endpoint_remainder_model": remainder, "total_candidate": integral + remainder}
        grids[str(points)] = sides

    result = {
        "record": 2137,
        "status": "ABS-P-TAIL-SCREEN-CANDIDATE",
        "owner": "one-copy G8-H",
        "change_from_2136": "replace abs(Re(P_from_nodes)) by exact product formula for abs(P_from_nodes), and evaluate both tail signs",
        "rung": R,
        "N48_interval_upper_source": "results/2135_routea_root_partition_lipschitz.json",
        "x0": X0,
        "xmax_numeric": XMAX,
        "q1600_abs": 3.406049871881275e12,
        "l2_charge": 4.412215566637855e10,
        "grid_readings": grids,
        "two_sided_tail_over_q1600_5000": sum(side["total_candidate"] for side in grids["5000"].values()) / 3.406049871881275e12,
        "two_sided_tail_over_l2_5000": sum(side["total_candidate"] for side in grids["5000"].values()) / 4.412215566637855e10,
        "solve": solve_info,
        "nonclaims": ["the N48 variation bound still needs an independent interval audit", "the infinity remainder is still an asymptotic model", "the quadrature is a numerical screen, not a certified integral bound", "the owner is the one-copy numerical G8-H candidate", "no producer theorem or RH claim"],
        "provenance": {"prior_screen": "scripts/routea_fixed_r48_tail_price_2136.py", "variation_source": "results/2135_routea_root_partition_lipschitz.json", "owner_source": "results/2058_l5_solve.json", "script": os.fspath(Path(__file__).relative_to(ROOT))},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
