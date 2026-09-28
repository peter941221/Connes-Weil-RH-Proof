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
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
import fourpoint_offline_owner_1981 as r81

OUTPUT = ROOT / "results" / "2102_full_known_prefix_direct_owner_m6400.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTAS = (0.15, 0.25, 0.35, 0.445)
SCALE = 0.80
K = 30.0
M = 6400
STEP = 0.02
XMAX = 40.0


def owner_and_family(delta):
    rho = (0.5 + delta) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
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


def evaluate(delta, xw_cache, kernel_cache):
    rho, nodes, values, fam = owner_and_family(delta)
    xw = []
    for a, _theta in fam:
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r59.phi_weights(a, panels=6, m=M)
        xw.append(xw_cache[float(a)])
    gram = r06.h1_gram(fam)
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    base_resid = float(np.max(np.abs(a_mat @ base - 1.0)))
    corr_resid = float(np.max(np.abs(a_mat @ corr - np.asarray(values, complex))))
    singular_values = np.linalg.svd(a_mat, compute_uv=False)
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    support = 2 * max(a for a, _theta in fam)
    if support not in kernel_cache:
        primes = r59.rig.prime_powers_up_to(math.exp(support))
        kernel = r59.rig.sigma_vec(2 * np.pi * grid)
        for number, weight in primes:
            kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
        kernel_cache[support] = (primes, kernel)
    primes, kernel = kernel_cache[support]
    q = float(np.trapezoid(kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2, grid))
    return {"gamma": GAMMA, "delta": delta, "scale": SCALE,
            "nodes": len(nodes), "families": len(fam), "support": support,
            "book": len(primes), "matrix_condition": float(singular_values[0] / singular_values[-1]),
            "base_resid": base_resid, "corr_resid": corr_resid,
            "q_step_002": q, "q_sign": "negative" if q < 0 else "nonnegative"}


def main():
    xw_cache, kernel_cache, rows = {}, {}, []
    for delta in DELTAS:
        row = evaluate(delta, xw_cache, kernel_cache)
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {
        "record": 2102,
        "status": "FULL-KNOWN-PREFIX-DIRECT-OWNER-M6400-SCREEN",
        "rows": rows, "window": [-XMAX, XMAX], "step": STEP,
        "owner": "first 30 numerical critical-line zeros inside the healthy closed ball",
        "family": "distinct orbit/real widths; shared width 2.2 for added kill zeros",
        "nonclaims": [
            "numerical zero list is not a Lean-certified complete owner",
            "finite grid and m=6400 remain screening until outward promotion",
            "no uniform COVER, producer theorem, or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "solver": "direct numpy.linalg.solve, not H1 pseudoinverse",
                       "previous": "results/2101_known_prefix_shared_width_kill_test.json"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
