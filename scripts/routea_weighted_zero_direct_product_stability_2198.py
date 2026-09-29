"""Record 2198: coefficient/quadrature stability screen for 2197.

The direct-product mass screen is only useful if the coefficient path is
stable under the committed quadrature refinement.  Recompute the owner matrix
and the direct physical masses at m=1600, 3200, 6400, keeping the physical
grid fixed.  This is a measured control, not an interval certificate.
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

OUTPUT = ROOT / "results" / "2198_weighted_zero_direct_product_stability.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
NX = 60001


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


def direct_mass(fam, base, corr, x, sigma):
    b = np.zeros_like(x, dtype=complex)
    b2 = np.zeros_like(x, dtype=complex)
    c = np.zeros_like(x, dtype=complex)
    c2 = np.zeros_like(x, dtype=complex)
    for coeff, (a, theta), target in [(base[j], fam[j], (b, b2)) for j in range(len(fam))]:
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
        b += coeff * phi * phase
        b2 += coeff * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
    for coeff, (a, theta) in zip(corr, fam):
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
        c += coeff * phi * phase
        c2 += coeff * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
    w = np.exp(sigma * x)
    mb = np.trapezoid(np.abs(b) * w, x)
    db = np.trapezoid(np.abs(b2) * w, x)
    mc = np.trapezoid(np.abs(c) * w, x)
    dc = np.trapezoid(np.abs(c2) * w, x)
    return float(min(db * mc, dc * mb) / (2.0 * math.pi) ** 2)


def main():
    nodes, values, fam = owner_family()
    x = np.linspace(-max(a for a, _ in fam), max(a for a, _ in fam), NX)
    rows = []
    for m in (1600, 3200, 6400):
        xw = [r59.phi_weights(a, panels=6, m=m) for a, _ in fam]
        mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
        base = np.linalg.solve(mat, np.ones(len(nodes), complex))
        corr = np.linalg.solve(mat, np.asarray(values, complex))
        row = {"m": m, "condition": float(np.linalg.cond(mat)),
               "base_max": float(np.max(np.abs(base))),
               "corr_max": float(np.max(np.abs(corr))),
               "base_resid": float(np.max(np.abs(mat @ base - 1))),
               "corr_resid": float(np.max(np.abs(mat @ corr - np.asarray(values, complex))))}
        row["C_upper_sigma1"] = direct_mass(fam, base, corr, x, 1.0)
        rows.append(row)
    ref = rows[-1]["C_upper_sigma1"]
    for row in rows:
        row["C_rel_to_m6400"] = row["C_upper_sigma1"] / ref - 1.0
    result = {"record": 2198, "status": "CANDIDATE-DIRECT-PRODUCT-STABILITY-SCREEN",
              "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE, "nodes": len(nodes)},
              "grid": {"x_nodes": NX, "sigma": 1.0}, "rows": rows,
              "nonclaims": ["float quadrature/solve only", "not interval certified",
                            "candidate owner only", "no producer or RH claim"],
              "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                             "parent": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py"}}
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
