"""Record 2197: owner-local direct-product mass screen.

Unlike record 2196, this forms the complete base/correction functions before
taking absolute values.  It therefore retains signed cancellation among the
family terms.  For F = base * correction in Laplace space, the measured
convolution estimate is

  C <= min(||base''||_1 ||correction||_1,
           ||correction''||_1 ||base||_1)/(2*pi)^2

with the strip weight exp(sigma*x).  The x-grid integrals are still measured,
not interval-certified; this is a route decision screen.
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

OUTPUT = ROOT / "results" / "2197_weighted_zero_direct_product_mass_screen.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
SIGNED_MARGIN = 1675397327895.099
NX = 240001


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
    x_min = -max(a for a, _ in fam)
    x_max = -x_min
    x = np.linspace(x_min, x_max, NX)
    dx = (x_max - x_min) / (NX - 1)
    base_xw = [r59.phi_weights(a, panels=6, m=M) for a, _ in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), base_xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))

    phi_sum = np.zeros_like(x, dtype=complex)
    phi2_sum = np.zeros_like(x, dtype=complex)
    corr_sum = np.zeros_like(x, dtype=complex)
    corr2_sum = np.zeros_like(x, dtype=complex)
    sigma_grid = np.linspace(0.0, 1.0, 101)
    rows = []
    best = None
    for acoef, (a, theta) in zip(base, fam):
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
        phi_sum += acoef * phi * phase
        phi2_sum += acoef * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase
    for ccoef, (a, theta) in zip(corr, fam):
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
        corr_sum += ccoef * phi * phase
        corr2_sum += ccoef * phi * (e2 + e1 * e1 + 2j * theta * e1 - theta * theta) * phase

    for sigma in sigma_grid:
        w = np.exp(float(sigma) * x)
        mb = float(np.trapezoid(np.abs(phi_sum) * w, x))
        db = float(np.trapezoid(np.abs(phi2_sum) * w, x))
        mc = float(np.trapezoid(np.abs(corr_sum) * w, x))
        dc = float(np.trapezoid(np.abs(corr2_sum) * w, x))
        cup = min(db * mc, dc * mb) / (2.0 * math.pi) ** 2
        row = {"sigma": float(sigma), "base_M0": mb, "base_D2": db,
               "corr_M0": mc, "corr_D2": dc, "C_upper": cup}
        rows.append(row)
        if best is None or cup > best["C_upper"]:
            best = row

    xi2 = math.pi / 6.0
    kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
    xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    mult = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)
    b_upper = (2.0 * math.pi) ** 2 * best["C_upper"]
    tail_upper = 4.0 * mult * b_upper
    result = {
        "record": 2197,
        "status": "CANDIDATE-DIRECT-PRODUCT-MASS-SCREEN",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam)},
        "grid": {"x_nodes": NX, "sigma_nodes": len(sigma_grid), "dx": dx},
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant_proxy": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_upper / SIGNED_MARGIN},
        "binding_row": best,
        "nonclaims": [
            "x-grid trapezoids are measured, not outward interval enclosures",
            "finite-difference/grid endpoint and coefficient errors are not charged",
            "multiplicity constant is diagnostic proxy",
            "candidate owner only; no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "scripts/routea_weighted_zero_measure_screen_2187.py"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
