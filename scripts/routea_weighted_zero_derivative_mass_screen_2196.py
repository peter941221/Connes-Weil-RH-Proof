"""Record 2196: structural quadratic-decay upper screen.

For a compact smooth factor f, two integrations by parts give
  |t/(2*pi)|^2 |L_f(sigma+i*t)| <= D2_f(sigma)/(2*pi)^2.
For F = base * correction in Laplace space, combine this with the other
factor's zero-order mass.  The resulting product bound is a structural upper
screen for the global quadratic constant.  Gauss integration is not an
interval certificate; the purpose is to decide whether this route has margin
before investing in outward interval panels.
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

OUTPUT = ROOT / "results" / "2196_weighted_zero_derivative_mass_screen.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
SIGNED_MARGIN = 1675397327895.099


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


def profile_masses(a, theta, sigma, x, w):
    """Return M0 and a triangle upper bound for integral |f''| e^(sigma x)."""
    u = x / a
    q = 1.0 - u * u
    inside = q > 0.0
    phi = np.zeros_like(x)
    phi[inside] = np.exp(-K / q[inside])
    e1 = np.zeros_like(x)
    e2 = np.zeros_like(x)
    e1[inside] = -2.0 * K * u[inside] / (a * q[inside] ** 2)
    e2[inside] = (-2.0 * K / (a * a) *
                  (1.0 / q[inside] ** 2 + 4.0 * u[inside] ** 2 / q[inside] ** 3))
    d1 = phi * e1
    d2 = phi * (e2 + e1 * e1)
    weight = np.exp(sigma * x) * w
    m0 = float(np.sum(phi * weight))
    # |(phi exp(i theta x))''| <= |phi''| + 2|theta||phi'| + theta^2 phi.
    d2mass = float(np.sum((np.abs(d2) + 2.0 * abs(theta) * np.abs(d1) +
                           theta * theta * phi) * weight))
    return m0, d2mass


def main():
    _rho, nodes, values, fam = owner_family()
    base_xw = [r59.phi_weights(a, panels=6, m=M) for a, _ in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), base_xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))

    rows = []
    sigma_grid = np.linspace(0.0, 1.0, 101)
    best = None
    for sigma in sigma_grid:
        mb = db = mc = dc = 0.0
        for j, (a, theta) in enumerate(fam):
            x, w = base_xw[j]
            m0, d2 = profile_masses(a, theta, float(sigma), x, w)
            mb += abs(base[j]) * m0
            db += abs(base[j]) * d2
            mc += abs(corr[j]) * m0
            dc += abs(corr[j]) * d2
        c_upper = min(db * mc, dc * mb) / (2.0 * math.pi) ** 2
        rows.append({"sigma": float(sigma), "base_M0": mb, "base_D2": db,
                     "corr_M0": mc, "corr_D2": dc, "C_upper": c_upper})
        if best is None or c_upper > best["C_upper"]:
            best = rows[-1]

    # Use the same explicit diagnostic multiplicity scale as record 2195.
    xi2 = math.pi / 6.0
    kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
    xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    mult = (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)
    b_upper = (2.0 * math.pi) ** 2 * best["C_upper"]
    tail_upper = 4.0 * mult * b_upper
    result = {
        "record": 2196,
        "status": "CANDIDATE-STRUCTURAL-UPPER-SCREEN",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam)},
        "quadrature": {"panels": 6, "nodes_per_panel": M, "sigma_nodes": len(sigma_grid)},
        "screen": {"C_upper": best["C_upper"], "B_upper": b_upper,
                   "spectralMultiplicityConstant_proxy": mult,
                   "high_shell_budget_upper": tail_upper,
                   "signed_margin_anchor": SIGNED_MARGIN,
                   "tail_upper_over_margin": tail_upper / SIGNED_MARGIN},
        "binding_row": best,
        "nonclaims": [
            "Gauss masses are measured, not outward interval enclosures",
            "triangle inequality loses cancellation between family terms",
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
