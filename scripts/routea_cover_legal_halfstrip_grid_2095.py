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
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
import routea_g8h_basis_comparison_2037 as r37

OUTPUT = ROOT / "results" / "2095_cover_legal_halfstrip_grid_m6400.json"
K = 30.0
DELTAS = (0.10, 0.20, 0.30, 0.40, 0.49)
STEP = 0.02
XMAX = 40.0
GAMMAS = (r94.G7, r94.G8, 43.327073280914999, 48.005150881167159)
SCALE = 0.86


def evaluate_case(gamma, delta):
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam = r94.family_for_ext(nodes, SCALE, gamma)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    gram = r06.h1_gram(fam)
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base, ib = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    corr, ic = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    s = 0.5 - 2j * np.pi * grid
    v = r80.family_values(fam, K, s, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    primes = r59.rig.prime_powers_up_to(math.exp(max(a for a, _ in fam) * 2))
    for number, weight in primes:
        kernel = kernel + 2.0 * weight / math.sqrt(number) * np.cos(
            2 * np.pi * grid * math.log(number))
    integrand = kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    q = float(np.trapezoid(integrand, grid))
    return {
        "gamma": gamma,
        "delta": delta,
        "scale": SCALE,
        "nodes": len(nodes),
        "families": len(fam),
        "support": max(a for a, _ in fam) * 2,
        "book": len(primes),
        "q_step_002": q,
        "q_sign": "negative" if q < 0 else "nonnegative",
        "base_resid": ib["resid"],
        "corr_resid": ic["resid"],
    }


def main():
    rows = []
    for gamma in GAMMAS:
        for delta in DELTAS:
            row = evaluate_case(gamma, delta)
            rows.append(row)
            print(json.dumps(row), flush=True)
    result = {
        "record": 2095,
        "status": "COVER-LEGAL-HALFSTRIP-GRID-M6400-SCREEN",
        "window": [-XMAX, XMAX],
        "step": STEP,
        "rows": rows,
        "nonclaims": [
            "m=6400 and finite grid are still screening only",
            "scale=0.86 is fixed for this grid",
            "legal delta grid stops at 0.49; no boundary claim",
            "no uniform COVER statement",
            "no producer theorem or RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT))},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
