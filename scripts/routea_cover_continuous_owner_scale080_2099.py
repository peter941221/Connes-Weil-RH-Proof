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
import fourpoint_offline_owner_1981 as r81
import routea_g8h_basis_comparison_2037 as r37

OUTPUT = ROOT / "results" / "2099_cover_continuous_owner_scale080_m6400.json"
K = 30.0
DELTAS = (0.15, 0.25, 0.35, 0.445)
GAMMAS = ((r94.G7 + r94.G8) / 2.0,
          (r94.G8 + 43.327073280914999) / 2.0,
          (43.327073280914999 + 48.005150881167159) / 2.0)
SCALE = 0.80
STEP = 0.02
XMAX = 40.0


CONTINUOUS_KILL_POOL = [2.2, 2.6, 3.0, 3.4, 3.8, 4.2, 4.6, 5.0, 5.4, 5.8]


def continuous_family(nodes, gamma):
    plan = {"main": 0, "real": 0, "kill": 0}
    pools = {"main": list(r81.WIDTHS_H1), "real": list(r81.WIDTHS_REAL),
             "kill": CONTINUOUS_KILL_POOL}
    fam = []
    for z in nodes:
        iz = float(np.imag(z))
        if abs(abs(iz) - gamma) < 1e-9:
            key = "main"
        elif abs(iz) < 1e-9:
            key = "real"
        else:
            key = "kill"
        idx = plan[key]
        plan[key] += 1
        if idx >= len(pools[key]):
            raise RuntimeError("continuous family pool exhausted for %s" % key)
        fam.append((SCALE * pools[key][idx], -iz))
    return fam
xw_cache = {}
prime_cache = {}

def weights_for_family(fam):
    out = []
    for a, _theta in fam:
        key = float(a)
        if key not in xw_cache:
            xw_cache[key] = r59.phi_weights(key, panels=6, m=6400)
        out.append(xw_cache[key])
    return out

def evaluate_case(gamma, delta):
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam = continuous_family(nodes, gamma)
    xw = weights_for_family(fam)
    gram = r06.h1_gram(fam)
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base, ib = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    corr, ic = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    s = 0.5 - 2j * np.pi * grid
    v = r80.family_values(fam, K, s, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    support = max(a for a, _ in fam) * 2
    if support not in prime_cache:
        primes = r59.rig.prime_powers_up_to(math.exp(support))
        kernel = r59.rig.sigma_vec(2 * np.pi * grid)
        for number, weight in primes:
            kernel = kernel + 2.0 * weight / math.sqrt(number) * np.cos(
                2 * np.pi * grid * math.log(number))
        prime_cache[support] = (primes, kernel)
    primes, kernel = prime_cache[support]
    integrand = kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    q = float(np.trapezoid(integrand, grid))
    return {
        "gamma": gamma, "delta": delta, "scale": SCALE,
        "nodes": len(nodes), "families": len(fam), "support": support,
        "book": len(primes), "q_step_002": q,
        "q_sign": "negative" if q < 0 else "nonnegative",
        "base_resid": ib["resid"], "corr_resid": ic["resid"],
    }

def main():
    rows = []
    for gamma in GAMMAS:
        for delta in DELTAS:
            row = evaluate_case(gamma, delta)
            rows.append(row)
            print(json.dumps(row), flush=True)
    result = {
        "record": 2099,
        "status": "COVER-CONTINUOUS-OWNER-SCALE080-M6400-SCREEN",
        "window": [-XMAX, XMAX], "step": STEP, "rows": rows,
        "cache": {"weight_keys": sorted(xw_cache), "prime_keys": sorted(prime_cache)},
        "nonclaims": [
            "interior points are screening only",
            "continuous 18-node owner extension is fixed",
            "m=6400 finite grid is not an outward certificate",
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
