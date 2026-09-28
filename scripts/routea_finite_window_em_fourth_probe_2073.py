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

OUTPUT = ROOT / "results" / "2073_finite_window_em_fourth_probe.json"
K = 30.0
XMAX = 40.0
STEP = 0.005


def first_derivative_end(values, h):
    left = (-25 * values[0] + 48 * values[1] - 36 * values[2]
            + 16 * values[3] - 3 * values[4]) / (12 * h)
    right = (25 * values[-1] - 48 * values[-2] + 36 * values[-3]
             - 16 * values[-4] + 3 * values[-5]) / (12 * h)
    return float(left), float(right)


def main():
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    primes = r59.rig.prime_powers_up_to(math.exp(9.504))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    s = 0.5 - 2j * np.pi * grid
    v = r80.family_values(fam, K, s, xw)
    lb = base @ v
    lc = corr @ v
    h_owner = np.abs(r59.P_from_nodes(grid, r80.counterpart_nodes(rho))) ** 2
    h_owner = h_owner * np.abs(lb) ** 2 * np.abs(lc) ** 2
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in primes:
        kernel = kernel + (2.0 * weight / math.sqrt(number)) * np.cos(2 * np.pi * grid * math.log(number))
    integrand = kernel * h_owner
    value = float(np.trapezoid(integrand, grid))
    fp_left, fp_right = first_derivative_end(integrand, STEP)
    em_correction = -(STEP ** 2 / 12.0) * (fp_right - fp_left)
    em_value = value + em_correction
    f4 = (integrand[:-4] - 4.0 * integrand[1:-3]
          + 6.0 * integrand[2:-2] - 4.0 * integrand[3:-1]
          + integrand[4:]) / (STEP ** 4)
    f4_l1 = float(np.trapezoid(np.abs(f4), grid[2:-2]))
    em_remainder_proxy = (STEP ** 4 / 720.0) * f4_l1
    result = {
        "record": 2073,
        "status": "EM-FOURTH-ORDER-MEASUREMENT",
        "owner": "one-copy G8-H",
        "window": [-XMAX, XMAX],
        "step": STEP,
        "visible_prime_count": len(primes),
        "aggregate_trapezoid": value,
        "endpoint_derivatives": {"left": fp_left, "right": fp_right},
        "em_endpoint_correction": em_correction,
        "em_corrected_value": em_value,
        "finite_difference_f4_l1": f4_l1,
        "em_remainder_proxy": em_remainder_proxy,
        "remainder_over_negative_margin": em_remainder_proxy / abs(value),
        "solve_resid": solve_info["resid"],
        "nonclaims": [
            "finite differences are diagnostic, not an outward enclosure",
            "sigma and family arithmetic errors are not included",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "owner_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()