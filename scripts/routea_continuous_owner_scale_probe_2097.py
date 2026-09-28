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

OUTPUT = ROOT / "results" / "2097_continuous_owner_scale_probe_m6400.json"
K = 30.0
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.15
SCALES = (0.76, 0.78, 0.80, 0.82, 0.84, 0.86, 0.88, 0.90, 0.92)
KILL_POOL = [2.2, 2.6, 3.0, 3.4, 3.8, 4.2, 4.6, 5.0, 5.4, 5.8]
STEP = 0.02
XMAX = 40.0
xw_cache = {}
prime_cache = {}

def family(nodes, scale):
    plan = {"main": 0, "real": 0, "kill": 0}
    pools = {"main": list(r81.WIDTHS_H1), "real": list(r81.WIDTHS_REAL), "kill": KILL_POOL}
    out = []
    for z in nodes:
        iz = float(np.imag(z))
        key = "main" if abs(abs(iz) - GAMMA) < 1e-9 else ("real" if abs(iz) < 1e-9 else "kill")
        idx = plan[key]
        plan[key] += 1
        out.append((scale * pools[key][idx], -iz))
    return out

def eval_scale(scale):
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    fam = family(nodes, scale)
    xw = []
    for a, _ in fam:
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r59.phi_weights(float(a), panels=6, m=6400)
        xw.append(xw_cache[float(a)])
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
            kernel += 2.0 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
        prime_cache[support] = (primes, kernel)
    primes, kernel = prime_cache[support]
    integrand = kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    q = float(np.trapezoid(integrand, grid))
    return {"gamma": GAMMA, "delta": DELTA, "scale": scale, "nodes": len(nodes),
            "families": len(fam), "support": support, "book": len(primes),
            "q_step_002": q, "q_sign": "negative" if q < 0 else "nonnegative",
            "base_resid": ib["resid"], "corr_resid": ic["resid"]}

def main():
    rows = []
    for scale in SCALES:
        row = eval_scale(scale)
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {"record": 2097, "status": "CONTINUOUS-OWNER-SCALE-M6400-SCREEN",
              "window": [-XMAX, XMAX], "step": STEP, "rows": rows,
              "nonclaims": ["single interior owner only", "m=6400 finite grid is screening only",
                            "no uniform COVER statement", "no producer theorem or RH claim"],
              "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                             "failure_source": "results/2096_cover_cell_interior_m6400.json"}}
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
