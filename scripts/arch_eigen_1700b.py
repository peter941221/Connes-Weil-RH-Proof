#!/usr/bin/env python3
# Record 1700 rig, part 2: settle the lambda_max ~ 0 reading.
#   (i)  N-stability: w=0.29 at N_PAD = 2400 vs 4800 (lambda_max must stay
#        at noise level with the same sign behaviour);
#   (ii) constraint ablation: top eigenvalue with 0, 1, 2, 3 of the node
#        moments removed (the collapse must be CAUSED by the constraints;
#        with 0 moments the top should be O(0.8), the unconstrained scale);
#   (iii) shape of the near-null top eigenvector at 3 moments.
# RH is not claimed.

import json
import numpy as np
from scipy.linalg import eigh
import sys
sys.path.insert(0, "scripts")
from arch_eigen_1700 import build_M, arch_sum, moment_matrix

Y_MAX = 40.0


def top_eig(w, n_pad, n_moments):
    pad = 4.0 * w
    xgrid = -pad + (2.0 * pad) / n_pad * np.arange(n_pad)
    dx = xgrid[1] - xgrid[0]
    M = build_M(xgrid, w)
    act = np.abs(xgrid) <= w + 1e-12
    Mact = M[np.ix_(act, act)]
    xa = xgrid[act]
    Cm = moment_matrix(xa, dx)[:n_moments]
    if n_moments > 0:
        P = np.eye(len(xa)) - Cm.T @ np.linalg.pinv(Cm @ Cm.T) @ Cm
    else:
        P = np.eye(len(xa))
    sym = (P @ Mact @ P.T + P @ Mact.T @ P.T) / 2.0
    vals, vecs = eigh(sym)
    lam = vals[-1] / dx
    g = np.zeros(n_pad)
    g[act] = vecs[:, -1]
    return lam, g, xgrid


def main():
    print("== 1700b: settle lambda_max ~ 0 ==")
    out = {"nstab": [], "ablation": []}

    print("-- (i) N-stability at w=0.29, 3 moments --")
    for n_pad in (2400, 4800):
        lam, g, xgrid = top_eig(0.29, n_pad, 3)
        dx = xgrid[1] - xgrid[0]
        qd = arch_sum(g, xgrid)
        out["nstab"].append(dict(n_pad=n_pad, lam_max=lam, q_dir=qd))
        print(f"   N={n_pad}: lambda_max={lam:+.3e}   Q_dir(max)={qd:+.3e}")

    print("-- (ii) constraint ablation at w=0.29, N=2400 --")
    for nm in (0, 1, 2, 3):
        lam, g, xgrid = top_eig(0.29, 2400, nm)
        out["ablation"].append(dict(n_moments=nm, lam_max=lam))
        print(f"   moments removed = {nm}: lambda_max = {lam:+.6f}")

    print("-- (iiib) random spot-check: arch_sum of confined g with int g = 0 --")
    rng = np.random.default_rng(11)
    w = 0.29
    xgrid = -4.0 * w + (8.0 * w) / 2400 * np.arange(2400)
    dx = xgrid[1] - xgrid[0]
    act = np.abs(xgrid) <= w + 1e-12
    xa = xgrid[act]
    c0 = (np.exp(0.0 * xa) * dx)[None, :]           # the mass row only
    pinv0 = np.linalg.pinv(c0 @ c0.T)
    M = build_M(xgrid, w)
    mx = -1e9
    for _ in range(20):
        v = rng.standard_normal(len(xgrid)) * act
        v[act] = v[act] - c0.T @ (pinv0 @ (c0 @ v[act]))
        v /= np.linalg.norm(v) * np.sqrt(dx)
        mx = max(mx, arch_sum(v, xgrid))
    out["random_max_arch_mass_zero"] = mx
    print(f"   max arch over 20 random unit-mass g with int g = 0: {mx:+.6f}")

    print("-- (iii) top eigenvector profile, w=0.29, 3 moments --")
    lam, g, xgrid = top_eig(0.29, 2400, 3)
    act = np.abs(xgrid) <= w + 1e-12
    xa = xgrid[act]
    ga = g[act]
    prof = [f"{x:+.3f}:{v:+.2f}" for x, v in
            zip(xa[:: max(1, len(xa) // 12)], ga[:: max(1, len(ga) // 12)])]
    print("   " + "  ".join(prof))
    out["profile_w029"] = prof

    with open("results/1700b_lambda_nstability.json", "w") as f:
        json.dump(out, f, indent=1)
    print("saved results/1700b_lambda_nstability.json")


if __name__ == "__main__":
    main()
