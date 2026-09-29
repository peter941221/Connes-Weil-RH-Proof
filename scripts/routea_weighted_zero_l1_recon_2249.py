"""2249 recon probe: magnitudes, cancellation meters, mass profile of the
finite-window functional q at the anchor candidate (record 2103, gamma =
39.25244858548658, delta = 0.445, scale = 0.80).  Screening only."""
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80      # noqa: E402
import fourpoint_owner_density_1959 as r59         # noqa: E402
import routea_opposite_gates_height_1994 as r94    # noqa: E402
import fourpoint_offline_owner_1981 as r81         # noqa: E402

import mpmath as mp                                # noqa: E402

GAMMA = 39.25244858548658
DELTA = 0.445
SCALE = 0.80
K = 30.0
M = 6400
STEP = 0.02
XMAX = 40.0


def build():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = 50
    for index in range(1, 31):
        height = float(mp.im(mp.zetazero(index)))
        z = 0.5 + 1j * height
        if abs(z - rho) <= radius and all(
                abs(z - existing) > 1e-6 for existing in nodes):
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
    rho, nodes, values, fam = build()
    xw_cache = {}
    xw = []
    for a, _theta in fam:
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r59.phi_weights(a, panels=6, m=M)
        xw.append(xw_cache[float(a)])
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    report = {
        "nodes": len(nodes), "families": len(fam),
        "cond": float(np.linalg.cond(a_mat)),
        "base_abs_max": float(np.abs(base).max()),
        "corr_abs_max": float(np.abs(corr).max()),
        "a_mat_abs_max": float(np.abs(a_mat).max()),
    }
    t0 = time.time()
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    report["v_eval_seconds"] = time.time() - t0
    lb = base @ v
    lc = corr @ v
    term_b = np.abs(base[:, None] * v).max(axis=0)
    term_c = np.abs(corr[:, None] * v).max(axis=0)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    support = 2 * max(a for a, _t in fam)
    primes = r59.rig.prime_powers_up_to(math.exp(support))
    kernel = r59.rig.sigma_vec(2.0 * np.pi * grid)
    for number, weight in primes:
        kernel = kernel + 2 * weight / math.sqrt(number) * np.cos(
            2 * np.pi * grid * math.log(number))
    g = kernel * p * p * np.abs(lb) ** 2 * np.abs(lc) ** 2
    q = float(np.trapezoid(g, grid))
    report.update({
        "support": support, "primes": len(primes),
        "q": q, "q_step_002_2103": -1675397327895.099,
        "abs_lb_min": float(np.abs(lb).min()),
        "abs_lb_max": float(np.abs(lb).max()),
        "abs_lc_min": float(np.abs(lc).min()),
        "abs_lc_max": float(np.abs(lc).max()),
        "cancel_ratio_b_max": float((term_b / np.abs(lb)).max()),
        "cancel_ratio_c_max": float((term_c / np.abs(lc)).max()),
        "kernel_min": float(kernel.min()), "kernel_max": float(kernel.max()),
        "p2_min": float((p * p).min()), "p2_max": float((p * p).max()),
        "g_abs_max": float(np.abs(g).max()),
        "sum_abs_g_step": float(np.abs(g).sum() * STEP),
    })
    cum = np.cumsum(np.abs(g)) * STEP
    total = cum[-1]
    for frac in (0.5, 0.9, 0.99, 0.999999, 0.999999999):
        idx = int(np.searchsorted(cum, frac * total))
        report["mass_frac_%s_at_x" % frac] = float(grid[idx])
    # sign split of the integral mass
    pos = float(np.sum(g[g > 0]) * STEP)
    neg = float(np.sum(g[g < 0]) * STEP)
    report["pos_mass_step"] = pos
    report["neg_mass_step"] = neg
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()