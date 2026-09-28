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

OUTPUT = ROOT / "results" / "2116_owner_cardinality_compact_widths_m6400.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
STEP = 0.02
XMAX = 40.0
EXTRA_ORBITS = ((0.60, 20.0), (0.62, 25.0), (0.68, 30.0), (0.70, 35.0))
EXTRA_WIDTHS = [2.21 + 0.05 * i for i in range(16)]


def base_owner():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(abs(z - existing) > 1e-6 for existing in nodes):
            nodes.append(z)
            values.append(0j)
    return rho, nodes, values, radius


def add_orbit(nodes, values, z):
    for candidate in (z, 1 - np.conj(z), np.conj(z), 1 - z):
        if all(abs(candidate - existing) > 1e-6 for existing in nodes):
            nodes.append(candidate)
            values.append(0j)


def make_family(nodes, rho, extra_start):
    plan = {"main": 0, "real": 0}
    fam = []
    for node_index, z in enumerate(nodes):
        height = float(z.imag)
        is_main_orbit = (abs(abs(height) - GAMMA) < 1e-9 and abs(z - rho) < 1e-9) \
            or abs(z - (1 - np.conj(rho))) < 1e-9 \
            or abs(z - np.conj(rho)) < 1e-9 \
            or abs(z - (1 - rho)) < 1e-9
        if is_main_orbit:
            idx = plan["main"]
            plan["main"] += 1
            width = r81.WIDTHS_H1[min(idx, len(r81.WIDTHS_H1) - 1)]
        elif abs(height) < 1e-9:
            idx = plan["real"]
            plan["real"] += 1
            width = r81.WIDTHS_REAL[min(idx, len(r81.WIDTHS_REAL) - 1)]
        elif node_index >= extra_start:
            width = EXTRA_WIDTHS[node_index - extra_start]
        else:
            width = 2.2
        fam.append((SCALE * width, -height))
    return fam


def evaluate(orbit_count):
    rho, nodes, values, radius = base_owner()
    for orbit in EXTRA_ORBITS[:orbit_count]:
        z = complex(*orbit)
        if abs(z - rho) > radius:
            raise ValueError("stress orbit outside closed ball")
        add_orbit(nodes, values, z)
    fam = make_family(nodes, rho, 30)
    xw_cache, xw = {}, []
    for a, _ in fam:
        if a not in xw_cache:
            xw_cache[a] = r59.phi_weights(a, panels=6, m=M)
        xw.append(xw_cache[a])
    amat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    sv = np.linalg.svd(amat, compute_uv=False)
    condition = float(sv[0] / max(sv[-1], 1e-300))
    try:
        base = np.linalg.solve(amat, np.ones(len(nodes), complex))
        corr = np.linalg.solve(amat, np.asarray(values, complex))
    except np.linalg.LinAlgError:
        return {"orbit_count": orbit_count, "nodes": len(nodes), "support": 2 * max(a for a, _ in fam),
                "book": None, "matrix_condition": condition, "matrix_status": "SINGULAR"}
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    support = 2 * max(a for a, _ in fam)
    primes = r59.rig.prime_powers_up_to(math.exp(support))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in primes:
        kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
    q = float(np.trapezoid(kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2, grid))
    return {"orbit_count": orbit_count, "nodes": len(nodes), "support": support,
            "book": len(primes), "matrix_condition": condition, "matrix_status": "nonsingular",
            "base_resid": float(np.max(np.abs(amat @ base - 1))),
            "corr_resid": float(np.max(np.abs(amat @ corr - np.asarray(values, complex)))),
            "q_step_002": q, "q_sign": "negative" if q < 0 else "nonnegative"}


def main():
    rows = []
    for orbit_count in range(5):
        row = evaluate(orbit_count)
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {"record": 2116, "status": "OWNER-CARDINALITY-COMPACT-WIDTHS-M6400-SCREEN",
              "gamma": GAMMA, "delta": DELTA, "scale": SCALE, "m": M,
              "rows": rows,
              "nonclaims": ["m=400 is screening only", "extra points are stress inputs, not claimed zeros",
                            "no complete owner theorem or producer/RH claim"],
              "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                             "family": "unique widths for added off-line orbit nodes"}}
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
