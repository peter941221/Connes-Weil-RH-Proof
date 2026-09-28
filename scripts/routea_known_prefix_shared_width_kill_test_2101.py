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
import fourpoint_offline_owner_1981 as r81
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
import routea_g8h_basis_comparison_2037 as r37

OUTPUT = ROOT / "results" / "2101_known_prefix_shared_width_kill_test.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.15
SCALE = 0.80
M = 400
K = 30.0
STEP = 0.02
XMAX = 40.0


def main():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    additional = []
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
            values.append(0j)
            additional.append(index)
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
    assert len(nodes) == len(fam) == 30
    xw_cache = {}
    xw = []
    for a, _theta in fam:
        if a not in xw_cache:
            xw_cache[a] = r59.phi_weights(a, panels=6, m=M)
        xw.append(xw_cache[a])
    gram = r06.h1_gram(fam)
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    singular_values = np.linalg.svd(a_mat, compute_uv=False)
    base_h1, ib = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    corr_h1, ic = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    direct_base_resid = float(np.max(np.abs(a_mat @ base - 1.0)))
    direct_corr_resid = float(np.max(np.abs(a_mat @ corr - np.asarray(values, complex))))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    support = 2 * max(a for a, _theta in fam)
    primes = r59.rig.prime_powers_up_to(math.exp(support))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in primes:
        kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
    q = float(np.trapezoid(kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2, grid))
    result = {
        "record": 2101,
        "status": "KNOWN-PREFIX-SHARED-WIDTH-KILL-TEST",
        "gamma": GAMMA, "delta": DELTA, "scale": SCALE,
        "additional_zero_indices": additional,
        "nodes": len(nodes), "families": len(fam),
        "support": support, "book": len(primes),
        "matrix_condition": float(singular_values[0] / singular_values[-1]),
        "h1_base_resid": ib["resid"], "h1_corr_resid": ic["resid"],
        "direct_base_resid": direct_base_resid,
        "direct_corr_resid": direct_corr_resid,
        "h1_vs_direct_base_relative": float(np.linalg.norm(base_h1 - base) / np.linalg.norm(base)),
        "h1_vs_direct_corr_relative": float(np.linalg.norm(corr_h1 - corr) / np.linalg.norm(corr)),
        "q_step_002_direct": q,
        "kill_test": {
            "pin_residual_ceiling": 1e-5,
            "negative_margin_required": 1e11,
            "passes": max(direct_base_resid, direct_corr_resid) < 1e-5 and q < -1e11,
        },
        "nonclaims": [
            "m=400 is below the known evaluator trust horizon and is selection only",
            "computed first-30 zeros are not a complete certified owner",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "zero_source": "mpmath.zetazero(1..30)",
                       "previous": "results/2100_truncated_zero_owner_audit.json"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
