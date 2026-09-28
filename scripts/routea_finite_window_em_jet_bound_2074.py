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

OUTPUT = ROOT / "results" / "2074_finite_window_em_jet_bound.json"
K = 30.0
XMAX = 40.0
PANEL = 0.002


def sigma_derivatives(x, order=6):
    x = np.asarray(x, dtype=float)
    z = 0.25 - 1j * np.pi * x
    zz = z + 8.0
    bern = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    out = [r59.rig.sigma_vec(2 * np.pi * x)]
    for k in range(1, order + 1):
        dlog = ((-1) ** (k - 1)) * math.factorial(k - 1) / (zz ** k)
        dinv = ((-1) ** k) * math.factorial(k) / (zz ** (k + 1))
        dpsi = dlog - 0.5 * dinv
        for n, b in enumerate(bern, start=1):
            p = 2 * n
            rising = math.prod(range(p, p + k))
            dpsi = dpsi - b * ((-1) ** k) * rising / (zz ** (p + k))
        ds = np.zeros_like(z)
        for j in range(8):
            ds = ds + ((-1) ** k) * math.factorial(k) / ((z + j) ** (k + 1))
        dpsi = dpsi - ds
        out.append(-dpsi.real)
    return out


def kernel_derivatives(x, primes, order=6):
    x = np.asarray(x, dtype=float)
    sd = sigma_derivatives(x, order)
    out = [np.asarray(v, dtype=float).copy() for v in sd]
    nums = np.asarray([n for n, _ in primes], dtype=float)
    coeff = np.asarray([2.0 * w / math.sqrt(n) for n, w in primes], dtype=float)
    omega = 2.0 * np.pi * np.log(nums)
    for lo in range(0, len(x), 512):
        xx = x[lo:lo + 512, None]
        phase = xx * omega[None, :]
        co = np.cos(phase)
        si = np.sin(phase)
        out[0][lo:lo + 512] += co @ coeff
        out[1][lo:lo + 512] += (-si * omega[None, :]) @ coeff
        out[2][lo:lo + 512] += (-co * (omega[None, :] ** 2)) @ coeff
        out[3][lo:lo + 512] += (si * (omega[None, :] ** 3)) @ coeff
        out[4][lo:lo + 512] += (co * (omega[None, :] ** 4)) @ coeff
        out[5][lo:lo + 512] += (-si * (omega[None, :] ** 5)) @ coeff
        out[6][lo:lo + 512] += (-co * (omega[None, :] ** 6)) @ coeff
    return out


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
    kd = kernel_derivatives(centers, primes, 6)
    prime_coeff = np.asarray([2.0 * w / math.sqrt(n) for n, w in primes])
    omega = 2.0 * np.pi * np.log(np.asarray([n for n, _ in primes], dtype=float))
    prime_abs = [float(np.sum(np.abs(prime_coeff) * np.abs(omega) ** k)) for k in range(7)]
    sigma_global = [float(np.max(np.abs(v)) + 1.0) for v in sigma_derivatives(np.linspace(-XMAX, XMAX, 2001), 6)]
    ksup = []
    for k in range(5):
        next_majorant = sigma_global[k + 1] + prime_abs[k + 1]
        ksup.append(np.abs(kd[k]) + radius * next_majorant)
    f4sup = (ksup[4] * gsup[0] + 4.0 * ksup[3] * gsup[1]
             + 6.0 * ksup[2] * gsup[2] + 4.0 * ksup[1] * gsup[3]
             + ksup[0] * gsup[4])
    l1_bound = float(np.sum(f4sup) * PANEL)
    remainder = (PANEL ** 4 / 720.0) * l1_bound
    result = {
        "record": 2074,
        "status": "EM-JET-BOUND-MEASUREMENT",
        "owner": "one-copy G8-H",
        "window": [-XMAX, XMAX],
        "panel_width": PANEL,
        "panel_count": len(centers),
        "fourth_derivative_l1_upper_proxy": l1_bound,
        "em_remainder_upper_proxy": remainder,
        "remainder_over_L2_charge": remainder / 4.412215566637855e10,
        "remainder_over_sampled_margin": remainder / 3.406049851781223e12,
        "kernel_prime_abs_majorants": prime_abs,
        "kernel_sigma_global_majorants": sigma_global,
        "solve_resid": solve_info["resid"],
        "nonclaims": [
            "kernel center derivatives are floating point",
            "sigma global scan is not an outward enclosure",
            "this is a sizing proxy, not a producer theorem or RH claim",
        ],
        "provenance": {
            "owner_source": "results/2058_l5_solve.json",
            "jet_source": "scripts/routea_l3_aggregate_2051.py",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()