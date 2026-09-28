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

OUTPUT = ROOT / "results" / "2072_finite_window_aggregate_residual.json"
K = 30.0
XMAX = 40.0


def main():
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    primes = r59.rig.prime_powers_up_to(math.exp(9.504))
    rows = []
    for step in (0.02, 0.01, 0.005):
        grid = np.arange(-XMAX, XMAX + step / 2, step)
        s = 0.5 - 2j * np.pi * grid
        v = r80.family_values(fam, K, s, xw)
        lb = base @ v
        lc = corr @ v
        h = np.abs(r59.P_from_nodes(grid, r80.counterpart_nodes(rho))) ** 2 * np.abs(lb) ** 2 * np.abs(lc) ** 2
        kernel = r59.rig.sigma_vec(2 * np.pi * grid)
        for number, weight in primes:
            kernel = kernel + (2.0 * weight / math.sqrt(number)) * np.cos(2 * np.pi * grid * math.log(number))
        integrand = kernel * h
        value = float(np.trapezoid(integrand, grid))
        derivative = np.diff(integrand) / step
        rows.append({
            "step": step,
            "nodes": len(grid),
            "aggregate_value": value,
            "aggregate_abs_integral": float(np.trapezoid(np.abs(integrand), grid)),
            "aggregate_fd_l1_derivative": float(np.trapezoid(np.abs(derivative), grid[:-1])),
            "max_abs_integrand": float(np.max(np.abs(integrand))),
            "solve_resid": solve_info["resid"],
        })
    result = {
        "record": 2072,
        "status": "AGGREGATE-RESIDUAL-MEASUREMENT",
        "owner": "one-copy G8-H",
        "window": [-XMAX, XMAX],
        "rows": rows,
        "visible_prime_count": len(primes),
        "interpretation": "The derivative and absolute-integral readings are diagnostics for an aggregate signed quadrature enclosure; they are not certified bounds.",
        "nonclaims": [
            "no interval enclosure",
            "no source-transform or coefficient enclosure",
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