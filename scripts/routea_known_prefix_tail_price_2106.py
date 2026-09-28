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

OUTPUT = ROOT / "results" / "2106_known_prefix_tail_price.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
R = 48
N48_UPPER = 1.2466403887652727e81
X0 = 40.0
XMAX = 1.0e6


def owner_family():
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
    xw_cache = {}
    xw = []
    for a, _theta in fam:
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r59.phi_weights(a, panels=6, m=6400)
        xw.append(xw_cache[float(a)])
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    prime_powers = r59.rig.prime_powers_up_to(math.exp(2 * max(a for a, _ in fam)))
    env = sum(2.0 * weight / math.sqrt(number) for number, weight in prime_powers)
    env += max(abs(float(r59.rig.sigma_vec(np.array([2 * math.pi * x]))[0])) for x in np.linspace(X0, 400, 2000))
    env += 2.0
    family_data = [(float(a), float(theta), abs(b), abs(c)) for (a, theta), b, c in zip(fam, base, corr)]

    def v_bound(a, t):
        log_value = (0.5 * a * a + math.log(N48_UPPER)
                     - (2 * R - 2) * math.log(a) - R * math.log(math.hypot(0.5, t)))
        if log_value < -745.0:
            return 0.0
        return math.exp(min(log_value, 700.0))

    def envelope(x):
        lb = cc = 0.0
        for a, theta, bcoef, ccoef in family_data:
            bound = v_bound(a, theta - 2 * math.pi * x)
            lb += bcoef * bound
            cc += ccoef * bound
        p = abs(float(np.real(r59.P_from_nodes(np.array([x]), r80.counterpart_nodes(rho))[0])))
        return env * p * p * lb * lb * cc * cc

    grid = np.geomspace(X0, XMAX, 5000)
    values_env = np.array([envelope(float(x)) for x in grid])
    tail_numeric = float(np.trapezoid(values_env, grid))
    remainder = float(values_env[-1] * grid[-1] / (4 * R - 9))
    total = tail_numeric + remainder
    result = {
        "record": 2106, "status": "KNOWN-PREFIX-TAIL-PRICE-CANDIDATE",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam),
                  "book": len(prime_powers)},
        "rung": R, "x0": X0, "xmax_numeric": XMAX,
        "tail_40_to_1e6": tail_numeric, "remainder_model": remainder,
        "tail_total": total, "sampled_negative_margin": 1675397327895.099,
        "tail_over_sampled_margin": total / 1675397327895.099,
        "env": env,
        "nonclaims": [
            "N48 upper and infinity remainder are inherited candidate bounds, not yet formal for this owner",
            "numerical zero list is not a complete abstract owner",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "results/2103_full_known_prefix_direct_owner_grid_m6400.json",
                       "tail_method": "record 2069 R=48 envelope"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
