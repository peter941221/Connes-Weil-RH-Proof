"""Record 2188: stress the candidate weighted-zero budget.

This extends the 2187 candidate screen to a larger known critical-line list
and several shell cutoffs.  Multiplicity/enclosure inflation is reported as a
stress factor; it is not asserted to be the true analytic multiplicity.
"""

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_opposite_gates_height_1994 as r94
import fourpoint_offline_owner_1981 as r81

OUTPUT = ROOT / "results" / "2188_routea_weighted_zero_measure_inflation.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 1600
MAX_ZERO = 240
SHELLS = (7, 8)


def owner_family():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 60
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
            values.append(0j)
    plan = {"main": 0, "real": 0}
    fam = []
    for z in nodes:
        height = float(z.imag)
        if abs(abs(height) - GAMMA) < 1e-9:
            idx = plan["main"]
            plan["main"] += 1
            width = r81.WIDTHS_H1[idx]
        elif abs(height) < 1e-9:
            idx = plan["real"]
            plan["real"] += 1
            width = r81.WIDTHS_REAL[idx]
        else:
            width = 2.2
        fam.append((SCALE * width, -height))
    return nodes, values, fam


def main():
    nodes, values, fam = owner_family()
    xw = [r59.phi_weights(a, panels=6, m=M) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))

    zeros = []
    for index in range(1, MAX_ZERO + 1):
        zeros.append(0.5 + 1j * float(mp.im(mp.zetazero(index))))
    omitted = [z for z in zeros if all(abs(z - node) > 1e-6 for node in nodes)]
    weights = []
    for z in omitted:
        v = r80.family_values(fam, K, np.asarray([z], complex), xw)[:, 0]
        g = np.dot(base, v) * np.dot(corr, v)
        weights.append(float(abs(g) ** 2))

    rows = []
    for shell in SHELLS:
        cutoff = 2.0 ** (shell + 1)
        selected = [w for z, w in zip(omitted, weights) if z.imag < cutoff]
        budget = float(sum(selected))
        rows.append({"N": shell, "cutoff": cutoff,
                     "omitted_known_zero_count": len(selected),
                     "budget": budget,
                     "budget_over_anchor": budget,
                     "stress_factor_to_anchor": 1.0 / budget if budget > 0 else math.inf})

    result = {
        "record": 2188,
        "status": "CANDIDATE-OWNER-WEIGHTED-BUDGET-INFLATION-SCREEN",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam)},
        "quadrature_m": M,
        "known_zero_list": MAX_ZERO,
        "rows": rows,
        "stress_factors": [1, 10, 100, 485, 1000],
        "nonclaims": [
            "known critical-line zeros are not the complete source owner",
            "multiplicities are not supplied by this screen",
            "stress factors are diagnostic, not analytic multiplicity bounds",
            "no interval enclosure, producer theorem, or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "prior": "scripts/routea_weighted_zero_measure_screen_2187.py"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
