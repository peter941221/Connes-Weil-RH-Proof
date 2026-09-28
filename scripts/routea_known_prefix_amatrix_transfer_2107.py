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

OUTPUT = ROOT / "results" / "2107_known_prefix_amatrix_transfer.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
STEP = 0.02
XMAX = 40.0
MP_DPS = 45


def owner_family():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = MP_DPS
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


def true_entry(a, theta, node):
    aa = mp.mpf(repr(float(a)))
    zm = aa * (mp.mpc(repr(complex(node).real), repr(complex(node).imag))
              + 1j * mp.mpf(repr(float(theta))))
    def integrand(x):
        xx = x / aa
        if abs(xx) >= 1:
            return mp.mpc(0)
        return mp.exp(-mp.mpf(K) / (1 - xx * xx) + zm * x)
    return aa * mp.quad(integrand, [-aa, -aa / 2, 0, aa / 2, aa])


def q_value(fam, xw, base, corr, rho, primes, grid):
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in primes:
        kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
    return float(np.trapezoid(kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2, grid))


def main():
    mp.mp.dps = MP_DPS
    rho, nodes, values, fam = owner_family()
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _ in fam]
    a_stored = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    a_true = np.empty_like(a_stored)
    max_gap = 0.0
    for i, node in enumerate(nodes):
        for j, (a, theta) in enumerate(fam):
            value = true_entry(a, theta, node)
            a_true[i, j] = complex(float(mp.re(value)), float(mp.im(value)))
            max_gap = max(max_gap, abs(a_true[i, j] - a_stored[i, j]))
        print(json.dumps({"node": i, "max_abs_gap": max_gap}), flush=True)
    base_stored = np.linalg.solve(a_stored, np.ones(len(nodes), complex))
    corr_stored = np.linalg.solve(a_stored, np.asarray(values, complex))
    base_true = np.linalg.solve(a_true, np.ones(len(nodes), complex))
    corr_true = np.linalg.solve(a_true, np.asarray(values, complex))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    primes = r59.rig.prime_powers_up_to(math.exp(2 * max(a for a, _ in fam)))
    q_stored = q_value(fam, xw, base_stored, corr_stored, rho, primes, grid)
    q_true = q_value(fam, xw, base_true, corr_true, rho, primes, grid)
    result = {
        "record": 2107, "status": "KNOWN-PREFIX-AMATRIX-TRANSFER-CANDIDATE",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam),
                  "book": len(primes)},
        "mp_dps": MP_DPS, "max_abs_entry_gap": max_gap,
        "frobenius_entry_gap": float(np.linalg.norm(a_true - a_stored)),
        "stored_residuals": {"base": float(np.max(np.abs(a_stored @ base_stored - 1)),),
                             "corr": float(np.max(np.abs(a_stored @ corr_stored - np.asarray(values, complex))))},
        "true_residuals": {"base": float(np.max(np.abs(a_true @ base_true - 1))),
                           "corr": float(np.max(np.abs(a_true @ corr_true - np.asarray(values, complex))))},
        "coefficient_relative_movement": {"base": float(np.linalg.norm(base_true - base_stored) / np.linalg.norm(base_stored)),
                                           "corr": float(np.linalg.norm(corr_true - corr_stored) / np.linalg.norm(corr_stored))},
        "q_stored": q_stored, "q_true": q_true, "q_transfer_abs": abs(q_true - q_stored),
        "sampled_margin": 1675397327895.099,
        "q_transfer_over_margin": abs(q_true - q_stored) / 1675397327895.099,
        "nonclaims": ["mpmath reconstruction is not an outward interval certificate",
                      "known-prefix owner is not the complete abstract owner",
                      "Gram transfer remains open", "no producer theorem or RH claim"],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "results/2103_full_known_prefix_direct_owner_grid_m6400.json",
                       "solver": "direct numpy.linalg.solve"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
