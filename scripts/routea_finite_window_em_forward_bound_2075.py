import json
import math
import os
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_g8h_basis_comparison_2037 as r37
import routea_l3_aggregate_2051 as r51
import routea_finite_window_em_jet_bound_2074 as r74

OUTPUT = ROOT / "results" / "2075_finite_window_em_forward_bound.json"
K = 30.0
XMAX = 40.0
PANEL = 0.002
U = np.finfo(float).eps / 2.0


def sigma_global_derivative_bound(order):
    if order == 0:
        return 100.0
    q = 8.25
    bern = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    dlog = math.factorial(order - 1) / q ** order
    dinv = 0.5 * math.factorial(order) / q ** (order + 1)
    bern_bound = 0.0
    for n, b in enumerate(bern, start=1):
        p = 2 * n
        rising = math.prod(range(p, p + order))
        bern_bound += abs(b) * rising / q ** (p + order)
    shift_bound = sum(math.factorial(order) / (j + 0.25) ** (order + 1)
                      for j in range(8))
    return dlog + dinv + bern_bound + shift_bound


def main():
    rho_o, nodes_o, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes_o, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    primes = r59.rig.prime_powers_up_to(math.exp(9.504))
    radius = PANEL / 2.0
    centers = np.arange(-XMAX + radius, XMAX, PANEL)
    model = r51.Model(fam, K, xw, base, corr,
                      r80.counterpart_nodes(rho_o))
    jets = model.g_jet(centers, radius, 2048)
    gsup = [r51.j_supk(jets, k, radius) for k in range(4)]
    gsup.append(jets[4])
    kd = r74.kernel_derivatives(centers, primes, 6)
    nums = np.asarray([n for n, _ in primes], dtype=float)
    coeff = np.asarray([2.0 * w / math.sqrt(n) for n, w in primes], dtype=float)
    omega = 2.0 * np.pi * np.log(nums)
    prime_abs = [float(np.sum(np.abs(coeff) * np.abs(omega) ** k)) for k in range(7)]
    sigma_bound = [sigma_global_derivative_bound(k) for k in range(7)]
    gamma = (len(primes) * U) / (1.0 - len(primes) * U)
    k_allow = []
    ksup = []
    for k in range(5):
        summation_allow = 32.0 * gamma * prime_abs[k]
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
        "record": 2075,
        "status": "EM-JET-FORWARD-BOUND-CANDIDATE",
        "owner": "one-copy G8-H",
        "window": [-XMAX, XMAX],
        "panel_width": PANEL,
        "panel_count": len(centers),
        "fourth_derivative_l1_forward_bound": l1_bound,
        "em_remainder_forward_bound": remainder,
        "remainder_over_L2_charge": remainder / 4.412215566637855e10,
        "remainder_over_sampled_margin": remainder / 3.406049851781223e12,
        "kernel_center_allowances": k_allow,
        "kernel_prime_abs_majorants": prime_abs,
        "kernel_sigma_analytic_majorants": sigma_bound,
        "summation_gamma": gamma,
        "solve_resid": solve_info["resid"],
        "nonclaims": [
            "the IEEE allowance is a forward-error model, not yet a Lean certificate",
            "the stored owner coefficients and model-to-real gap remain open",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "owner_source": "results/2058_l5_solve.json",
            "jet_source": "scripts/routea_l3_aggregate_2051.py",
            "previous_probe": "results/2074_finite_window_em_jet_bound.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()