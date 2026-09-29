"""Record 2201: coefficient-solve enclosure preflight.

This is the first solve-side enclosure step for the 2197 direct-product
candidate.  The matrix at m=6400 is treated as A0 and the m=3200-to-6400
matrix difference is used as a provisional E.  The standard residual
perturbation estimate

  ||c-c0||inf <= ||A0^-1||inf ||E||inf ||c0||inf /
                  (1 - ||A0^-1||inf ||E||inf)

is then propagated through the same sampled M0/D2 functional used by 2197.
The matrix difference is not yet an analytic outward enclosure; this file is
therefore a preflight and cannot license a producer theorem.
"""
import importlib.util
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

spec = importlib.util.spec_from_file_location(
    "r2197", ROOT / "scripts" /
    "routea_weighted_zero_direct_product_mass_screen_2197.py")
r2197 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r2197)

OUT = ROOT / "results" / "2201_weighted_zero_solve_enclosure_preflight.json"
M_REF = 6400
M_LOW = 3200
NX = 30001
SIGNED_MARGIN = r2197.SIGNED_MARGIN


def multiplicity_proxy():
    xi2 = math.pi / 6.0
    kernel_small = (1.0 / math.pi) ** 0.25 * math.gamma(0.25)
    xi_tail = 2.0 / (1.0 - math.exp(-math.pi))
    xi_growth = 2.0 * xi_tail * (kernel_small + 1.0)
    return (xi_growth + 1.0 + abs(math.log(xi2)) + 192.0) / math.log(2.0)


def matrices(m):
    nodes, values, fam = r2197.owner_family()
    xw = [r2197.r59.phi_weights(a, panels=6, m=m) for a, _ in fam]
    A = r2197.r80.family_values(
        fam, r2197.K, np.asarray(nodes, complex), xw).T
    b0 = np.ones(len(nodes), complex)
    by = np.asarray(values, complex)
    return nodes, fam, A, b0, by


def solve_error(A0, A_low, b):
    c0 = np.linalg.solve(A0, b)
    inv0 = np.linalg.inv(A0)
    e_mat = A_low - A0
    inv_inf = float(np.max(np.sum(np.abs(inv0), axis=1)))
    e_inf = float(np.max(np.sum(np.abs(e_mat), axis=1)))
    c_inf = float(np.max(np.abs(c0)))
    q = inv_inf * e_inf
    if q >= 1.0:
        raise RuntimeError("Neumann denominator is nonpositive")
    radius = inv_inf * e_inf * c_inf / (1.0 - q)
    return c0, {"inv_inf": inv_inf, "matrix_delta_inf": e_inf,
                "c0_inf": c_inf, "neumann_q": q,
                "coefficient_radius_inf": radius}


def profile(fam, coeff, x):
    value = np.zeros_like(x, dtype=complex)
    second = np.zeros_like(x, dtype=complex)
    for acoef, (a, theta) in zip(coeff, fam):
        u = x / a
        q = 1.0 - u * u
        mask = q > 0.0
        phi = np.zeros_like(x)
        phi[mask] = np.exp(-r2197.K / q[mask])
        e1 = np.zeros_like(x)
        e2 = np.zeros_like(x)
        e1[mask] = -2.0 * r2197.K * u[mask] / (a * q[mask] ** 2)
        e2[mask] = (-2.0 * r2197.K / (a * a) *
                    (1.0 / q[mask] ** 2 +
                     4.0 * u[mask] ** 2 / q[mask] ** 3))
        phase = np.exp(1j * theta * x)
        value += acoef * phi * phase
        second += acoef * phi * (e2 + e1 * e1 +
                                 2j * theta * e1 - theta * theta) * phase
    return value, second


def main():
    nodes, fam, A0, b_base, b_corr = matrices(M_REF)
    _, _, A_low, _, _ = matrices(M_LOW)
    base, eb = solve_error(A0, A_low, b_base)
    corr, ec = solve_error(A0, A_low, b_corr)
    x = np.linspace(-max(a for a, _ in fam), max(a for a, _ in fam), NX)
    vb, db = profile(fam, base, x)
    vc, dc = profile(fam, corr, x)
    one = np.ones(len(fam), dtype=complex)
    ve, de = profile(fam, one, x)
    mult = multiplicity_proxy()
    rows = []
    max_ratio = 0.0
    for sigma in np.linspace(0.0, 1.0, 101):
        w = np.exp(sigma * x)
        mb = float(np.trapezoid(np.abs(vb) * w, x))
        db0 = float(np.trapezoid(np.abs(db) * w, x))
        mc = float(np.trapezoid(np.abs(vc) * w, x))
        dc0 = float(np.trapezoid(np.abs(dc) * w, x))
        # A coefficient perturbation of radius r changes each profile by at
        # most r times the sum of the corresponding family envelopes.
        env_m = float(np.trapezoid(np.abs(ve) * w, x))
        env_d = float(np.trapezoid(np.abs(de) * w, x))
        eb_m = env_m * eb["coefficient_radius_inf"]
        eb_d = env_d * eb["coefficient_radius_inf"]
        ec_m = env_m * ec["coefficient_radius_inf"]
        ec_d = env_d * ec["coefficient_radius_inf"]
        cup = min((db0 + eb_d) * (mc + ec_m),
                  (dc0 + ec_d) * (mb + eb_m)) / (2.0 * math.pi) ** 2
        ratio = 4.0 * mult * (2.0 * math.pi) ** 2 * cup / SIGNED_MARGIN
        max_ratio = max(max_ratio, ratio)
        rows.append({"sigma": float(sigma), "budget_ratio": ratio,
                     "C_upper_with_solve_radius": cup})
    result = {
        "record": 2201,
        "status": "SOLVE-ENCLOSURE-PREFLIGHT",
        "owner": {"nodes": len(nodes), "gamma": r2197.GAMMA,
                  "delta": r2197.DELTA, "scale": r2197.SCALE},
        "matrix": {"reference_m": M_REF, "comparison_m": M_LOW,
                   "condition_inf": float(np.linalg.cond(A0))},
        "base": eb, "correction": ec,
        "max_budget_ratio_with_provisional_solve_radius": max_ratio,
        "binding_row": max(rows, key=lambda row: row["budget_ratio"]),
        "nonclaims": [
            "m=3200 to m=6400 matrix difference is not an analytic outward bound",
            "profile integrals are sampled trapezoids",
            "multiplicity constant and signed margin are inherited screen inputs",
            "no producer theorem and no RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "parent": "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
