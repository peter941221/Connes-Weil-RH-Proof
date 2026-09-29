"""Record 2199: coefficient-error budget for the direct-product screen.

Using the 2197 physical-grid functions, add a worst-case relative coefficient
perturbation envelope.  This is not an interval solve; it prices how much
relative coefficient error the 454x candidate headroom can tolerate.
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

OUTPUT = ROOT / "results" / "2199_weighted_zero_coefficient_error_budget.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
NX = 60001
MARGIN = 1675397327895.099
ERRORS = (1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3)


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
    x = np.linspace(-max(a for a, _ in fam), max(a for a, _ in fam), NX)
    xw = [r59.phi_weights(a, panels=6, m=M) for a, _ in fam]
    mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(mat, np.asarray(values, complex))
    sigma = 1.0
    w = np.exp(sigma * x)
    b = np.zeros_like(x, dtype=complex)
    b2 = np.zeros_like(x, dtype=complex)
    c = np.zeros_like(x, dtype=complex)
    c2 = np.zeros_like(x, dtype=complex)
    b_abs = np.zeros_like(x)
    b2_abs = np.zeros_like(x)
    c_abs = np.zeros_like(x)
    c2_abs = np.zeros_like(x)
    for j, (a, theta) in enumerate(fam):
        u = x / a
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(x)
        phi[mask] = np.exp(-K / q[mask])
        e1 = np.zeros_like(x)
        e2 = np.zeros_like(x)
        e1[mask] = -2.0 * K * u[mask] / (a * q[mask] ** 2)
        e2[mask] = (-2.0 * K / (a * a) *
                    (1.0 / q[mask] ** 2 + 4.0 * u[mask] ** 2 / q[mask] ** 3))
        phase = np.exp(1j * theta * x)
        p2 = phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
        p = phi * phase
        b += base[j] * p
        b2 += base[j] * p2
        c += corr[j] * p
        c2 += corr[j] * p2
        b_abs += abs(base[j]) * np.abs(p)
        b2_abs += abs(base[j]) * np.abs(p2)
        c_abs += abs(corr[j]) * np.abs(p)
        c2_abs += abs(corr[j]) * np.abs(p2)
    mb = np.trapezoid(np.abs(b) * w, x)
    db = np.trapezoid(np.abs(b2) * w, x)
    mc = np.trapezoid(np.abs(c) * w, x)
    dc = np.trapezoid(np.abs(c2) * w, x)
    mbt = np.trapezoid(b_abs * w, x)
    dbt = np.trapezoid(b2_abs * w, x)
    mct = np.trapezoid(c_abs * w, x)
    dct = np.trapezoid(c2_abs * w, x)
    rows = []
    for err in ERRORS:
        mb_e, db_e = mb + err * mbt, db + err * dbt
        mc_e, dc_e = mc + err * mct, dc + err * dct
        cup = min(db_e * mc_e, dc_e * mb_e) / (2.0 * math.pi) ** 2
        # Same diagnostic multiplicity scale as records 2195-2198.
        mult = 301.83032993648527
        tail = 4.0 * mult * (2.0 * math.pi) ** 2 * cup
        rows.append({"relative_coefficient_error": err, "C_upper": float(cup),
                     "tail_upper": float(tail), "tail_over_margin": float(tail / MARGIN)})
    result = {"record": 2199, "status": "CANDIDATE-COEFFICIENT-ERROR-BUDGET",
              "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE, "nodes": len(nodes)},
              "grid": {"x_nodes": NX, "sigma": sigma},
              "baseline": {"base_M0": float(mb), "base_D2": float(db),
                           "corr_M0": float(mc), "corr_D2": float(dc),
                           "triangle_base_M0": float(mbt), "triangle_base_D2": float(dbt),
                           "triangle_corr_M0": float(mct), "triangle_corr_D2": float(dct)},
              "rows": rows,
              "nonclaims": ["measured physical-grid masses", "not interval certified",
                            "coefficient error is a model parameter", "candidate owner only"],
              "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                             "parent": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py"}}
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
