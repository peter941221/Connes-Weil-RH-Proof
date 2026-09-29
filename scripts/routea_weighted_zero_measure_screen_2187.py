"""Record 2187: candidate-owner weighted-zero residual screen.

This is deliberately a screen, not a producer certificate.  It evaluates the
exact 2185 weight on a finite mpmath zero list for one existing owner model.
The omitted nodes are the known critical-line zeros below the selected shell
cutoff which are not already interpolation nodes.  The result tests whether
the 2138 residual budget (anchor multiplicity one) is numerically plausible.
It does not claim completeness of the source-zero owner, multiplicities, or
an interval enclosure.
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

OUTPUT = ROOT / "results" / "2187_routea_weighted_zero_measure_screen.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
N_SHELL = 7
MAX_ZERO = 120
M = 6400


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
    return rho, nodes, values, fam


def main():
    rho, nodes, values, fam = owner_family()
    xw = [r59.phi_weights(a, panels=6, m=M) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))

    cutoff = 2.0 ** (N_SHELL + 1)
    shell_zeros = []
    for index in range(1, MAX_ZERO + 1):
        height = float(mp.im(mp.zetazero(index)))
        if height < cutoff:
            shell_zeros.append(0.5 + 1j * height)

    omitted = [z for z in shell_zeros
               if all(abs(z - node) > 1e-6 for node in nodes)]
    weights = []
    for z in omitted:
        v = r80.family_values(fam, K, np.asarray([z], complex), xw)[:, 0]
        g = np.dot(base, v) * np.dot(corr, v)
        # On the critical line, the convolution-square transform at the
        # centered spectral coordinate has modulus |g(z)|^2.
        weights.append(float(abs(g) ** 2))

    budget = float(sum(weights))
    result = {
        "record": 2187,
        "status": "CANDIDATE-OWNER-WEIGHTED-ZERO-MEASURE-SCREEN",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam)},
        "shell": {"N": N_SHELL, "height_cutoff": cutoff,
                  "known_zero_count": len(shell_zeros),
                  "omitted_known_zero_count": len(omitted)},
        "weights": {"sum": budget, "max": max(weights, default=0.0),
                    "anchor_multiplicity": 1.0,
                    "budget_over_anchor": budget},
        "nonclaims": [
            "critical-line numerical zero list is not the complete source owner",
            "multiplicities are set to one in this screen",
            "stored float/matrix/quadrature path is not interval enclosed",
            "no B_zm < epsilon producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "scripts/routea_known_prefix_tail_price_2106.py",
                       "consumer_contract": "docs/proofs/2138_routea_residual_budget_consumer.md"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
