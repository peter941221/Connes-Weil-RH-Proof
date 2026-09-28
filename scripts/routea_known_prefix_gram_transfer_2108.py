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
import routea_opposite_gates_height_1994 as r94
import fourpoint_offline_owner_1981 as r81

OUTPUT = ROOT / "results" / "2108_known_prefix_gram_transfer.json"
GAMMA = (r94.G7 + r94.G8) / 2.0
DELTA = 0.445
SCALE = 0.80
K = 30.0
STEP = 0.02
XMAX = 40.0
MP_DPS = 45


def owner_family():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    radius = r80.ball_radius(rho, 0)
    mp.mp.dps = MP_DPS
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


def phi_derivative(a, theta, x):
    aa = mp.mpf(repr(float(a)))
    tt = mp.mpf(repr(float(theta)))
    xx = mp.mpf(x)
    u = xx / aa
    if abs(u) >= 1:
        return mp.mpc(0), mp.mpc(0)
    core = mp.exp(-mp.mpf(K) / (1 - u * u))
    phase = mp.exp(1j * tt * xx)
    dcore = core * (-2 * mp.mpf(K) * xx / (aa * aa * (1 - u * u) ** 2))
    return core * phase, (dcore + 1j * tt * core) * phase


def true_gram_entry(ai, ti, aj, tj):
    radius = max(mp.mpf(repr(float(ai))), mp.mpf(repr(float(aj))))
    amin = min(mp.mpf(repr(float(ai))), mp.mpf(repr(float(aj))))
    cuts = sorted(set([-radius, -amin, mp.mpf(0), amin, radius]))
    def integrand(x):
        pi, di = phi_derivative(ai, ti, x)
        pj, dj = phi_derivative(aj, tj, x)
        return mp.conj(pi) * pj + mp.conj(di) * dj
    return mp.quad(integrand, cuts)


def q_value(fam, xw, base, corr, rho, primes, grid):
    v = r80.family_values(fam, K, 0.5 - 2j * np.pi * grid, xw)
    p = np.real(r59.P_from_nodes(grid, r80.counterpart_nodes(rho)))
    kernel = r59.rig.sigma_vec(2 * np.pi * grid)
    for number, weight in primes:
        kernel += 2 * weight / math.sqrt(number) * np.cos(2 * np.pi * grid * math.log(number))
    return float(np.trapezoid(kernel * p * p * np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2, grid))


def main():
    mp.mp.dps = MP_DPS
    rho, nodes, values, fam = owner_family()
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _ in fam]
    gram_stored = __import__('routea_health_cone_2006', fromlist=['h1_gram']).h1_gram(fam)
    gram_true = np.empty_like(gram_stored)
    max_gap = 0.0
    for i, (ai, ti) in enumerate(fam):
        for j in range(i, len(fam)):
            value = true_gram_entry(ai, ti, fam[j][0], fam[j][1])
            z = complex(float(mp.re(value)), float(mp.im(value)))
            gram_true[i, j] = z
            gram_true[j, i] = np.conj(z)
            max_gap = max(max_gap, abs(z - gram_stored[i, j]))
        print(json.dumps({"family": i, "max_abs_gap": max_gap}), flush=True)
    gram_true = (gram_true + gram_true.conj().T) / 2.0
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base_ss = np.linalg.solve(gram_stored * 0 + a_mat, np.ones(len(nodes), complex))
    corr_ss = np.linalg.solve(gram_stored * 0 + a_mat, np.asarray(values, complex))
    # The direct interpolant is independent of the Gram; use the same A solve.
    primes = r59.rig.prime_powers_up_to(math.exp(2 * max(a for a, _ in fam)))
    grid = np.arange(-XMAX, XMAX + STEP / 2, STEP)
    q_stored = q_value(fam, xw, base_ss, corr_ss, rho, primes, grid)
    # This Gram comparison is diagnostic: solve the H1 minimum with each Gram,
    # while pin targets remain exact. It cannot replace the direct owner solve.
    def h1_solve(gram):
        ew, ev = np.linalg.eigh(gram)
        floor = max(float(ew.max()) * 1e-12, 1e-18)
        inv = (ev / np.maximum(ew, floor)) @ ev.conj().T
        schur = a_mat @ inv @ a_mat.conj().T
        return inv @ a_mat.conj().T @ np.linalg.solve(schur, np.ones(len(nodes), complex)), \
               inv @ a_mat.conj().T @ np.linalg.solve(schur, np.asarray(values, complex))
    base_gs, corr_gs = h1_solve(gram_stored)
    base_gt, corr_gt = h1_solve(gram_true)
    q_h1_stored = q_value(fam, xw, base_gs, corr_gs, rho, primes, grid)
    q_h1_true = q_value(fam, xw, base_gt, corr_gt, rho, primes, grid)
    result = {
        "record": 2108, "status": "KNOWN-PREFIX-GRAM-TRANSFER-CANDIDATE",
        "owner": {"gamma": GAMMA, "delta": DELTA, "scale": SCALE,
                  "nodes": len(nodes), "support": 2 * max(a for a, _ in fam), "book": len(primes)},
        "mp_dps": MP_DPS, "max_abs_gram_entry_gap": max_gap,
        "frobenius_gram_gap": float(np.linalg.norm(gram_true - gram_stored)),
        "h1_q_stored": q_h1_stored, "h1_q_true": q_h1_true,
        "h1_gram_transfer_abs": abs(q_h1_true - q_h1_stored),
        "sampled_margin": 1675397327895.099,
        "h1_gram_transfer_over_margin": abs(q_h1_true - q_h1_stored) / 1675397327895.099,
        "nonclaims": ["mpmath Gram is not an outward interval certificate",
                      "known-prefix owner is not the complete abstract owner",
                      "direct-solve model is separate from H1 diagnostic",
                      "no producer theorem or RH claim"],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "owner_source": "results/2103_full_known_prefix_direct_owner_grid_m6400.json"},
    }
    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
