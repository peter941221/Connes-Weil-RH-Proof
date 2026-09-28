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
import routea_g8h_basis_comparison_2037 as r37
import routea_l3_aggregate_2051 as r51
import routea_finite_window_em_forward_bound_2075 as r75
import routea_finite_window_em_jet_bound_2074 as r74

OUTPUT = ROOT / "results" / "2105_known_prefix_em_forward_bound.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
XMAX = 40.0
PANEL = 0.002
U = np.finfo(float).eps / 2.0


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
            xw_cache[float(a)] = r59.phi_weights(a, panels=6, m=M)
        xw.append(xw_cache[float(a)])
    gram = r06.h1_gram(fam)
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    base_resid = float(np.max(np.abs(a_mat @ base - 1.0)))
    corr_resid = float(np.max(np.abs(a_mat @ corr - np.asarray(values, complex))))
    primes = r59.rig.prime_powers_up_to(math.exp(2 * max(a for a, _ in fam)))
    radius = PANEL / 2.0
    centers = np.arange(-XMAX + radius, XMAX, PANEL)
    model = r51.Model(fam, K, xw, base, corr, r80.counterpart_nodes(rho))
    jets = model.g_jet(centers, radius, 2048)
    gsup = [r51.j_supk(jets, k, radius) for k in range(4)] + [jets[4]]
    kd = r74.kernel_derivatives(centers, primes, 6)
    nums = np.asarray([n for n, _ in primes], dtype=float)
    coeff = np.asarray([2.0 * w / math.sqrt(n) for n, w in primes], dtype=float)
    omega = 2.0 * np.pi * np.log(nums)
    prime_abs = [float(np.sum(np.abs(coeff) * np.abs(omega) ** k)) for k in range(7)]
    sigma_bound = [r75.sigma_global_derivative_bound(k) for k in range(7)]
    gamma_sum = (len(primes) * U) / (1.0 - len(primes) * U)
    k_allow = []
    ksup = []
    for k in range(5):
        summation_allow = 32.0 * gamma_sum * prime_abs[k]
        input_allow = 32.0 * U * (1.0 + prime_abs[k] + sigma_bound[k])
        allow = summation_allow + input_allow
        k_allow.append(allow)
        next_majorant = sigma_bound[k + 1] + prime_abs[k + 1]
        ksup.append(np.abs(kd[k]) + allow + radius * next_majorant)
    f4sup = (ksup[4] * gsup[0] + 4.0 * ksup[3] * gsup[1]
             + 6.0 * ksup[2] * gsup[2] + 4.0 * ksup[1] * gsup[3]
             + ksup[0] * gsup[4])
    l1_bound = float(np.sum(f4sup) * PANEL)
    remainder = (PANEL ** 4 / 720.0) * l1_bound
    result = {
        "record": 2105,
        "status": "KNOWN-PREFIX-EM-FORWARD-BOUND-CANDIDATE",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam),
                  "book": len(primes)},
        "panel_width": PANEL, "panel_count": len(centers),
        "fourth_derivative_l1_forward_bound": l1_bound,
        "em_remainder_forward_bound": remainder,
        "sampled_negative_margin": 1675397327895.099,
        "remainder_over_sampled_margin": remainder / 1675397327895.099,
        "base_resid": base_resid, "corr_resid": corr_resid,
        "kernel_prime_abs_majorants": prime_abs,
        "kernel_sigma_analytic_majorants": sigma_bound,
        "summation_gamma": gamma_sum,
        "nonclaims": [
            "the direct coefficients and IEEE allowance are not yet Lean outward certificates",
            "known-prefix numerical zeros are not a complete abstract owner",
            "this is a finite-window quadrature bound only, not full-line closure",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "jet_source": "scripts/routea_l3_aggregate_2051.py",
                       "kernel_source": "scripts/routea_finite_window_em_forward_bound_2075.py",
                       "owner_source": "results/2103_full_known_prefix_direct_owner_grid_m6400.json"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
