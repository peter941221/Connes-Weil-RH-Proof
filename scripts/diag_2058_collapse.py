"""2058 diagnostic: size the solve-channel functional-sensitivity collapse.

The 2057 record charges the solve channel by a POINTWISE input-perturbation
envelope: the measured coefficient deviations delta_b/delta_c (per family)
scale the family jet (value + derivative slots + K4) and the envelope is
integrated positively, then multiplied by the crude kernel bound
(SIG_MAX + C_book) = 463.42.  The functional is Q = int K p^2 |lb|^2 |cc|^2
with lb = base @ v(xi), cc = corr @ v(xi) -- QUADRATIC in each coefficient
vector -- so the solve-channel difference is exactly

    dQ_solve = Q(b+db, c+dc) - Q(b, c)
             = 2 Re[ sum_j db_j Ab_j + sum_j dc_j Cc_j ]
               + (second-order integral),

with Ab_j = int K p^2 |cc|^2 conj(lb) v_j dxi and
     Cc_j = int K p^2 |lb|^2 conj(cc) v_j dxi.

This diagnostic measures, on the committed construction (xw1600):
  - the coefficient scales and the deviations delta_b/delta_c (float
    min-norm vs the committed r37.min_h1 float solve);
  - dQ_solve directly, and the linear/quadratic split;
  - the linear collapse bound 2 sum |delta_j| |A_j| and the same-grid
    POINTWISE envelope analog (the 2057 charge's structure, without the
    RT/derivative/K4 inflation);
so the expected gain of the 2058 batch is sized before any probe is built.
"""
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fourpoint_owner_completion_1980 as r80   # noqa: E402
import fourpoint_owner_density_1959 as r59      # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import routea_l3_aggregate_2051 as r51          # noqa: E402
import routea_reduced_evaluator_2054 as r54     # noqa: E402

K = r37.K
M_RED = 1600
XI = 40.0


def main():
    rho, nodes, values, fam, xw400, gram, a_mat, _, _ = r37.setup(False)
    xw1600 = [r59.phi_weights(a, panels=6, m=M_RED) for (a, _t) in fam]
    base, ib = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    corr, ic = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    cnt = r80.counterpart_nodes(rho)
    model = r51.Model(fam, K, xw1600, base, corr, cnt)
    ps = model.ps
    # the exact twin of the committed rule: in exact arithmetic the clamped
    # inverse is I/floor (uniform-floor regime), i.e. the min-norm solve
    A = np.asarray(a_mat)
    S = A @ A.conj().T
    z_b = np.linalg.solve(S, np.ones(len(nodes), complex))
    z_c = np.linalg.solve(S, np.asarray(values, complex))
    cmn_b = A.conj().T @ z_b
    cmn_c = A.conj().T @ z_c
    db = cmn_b - base
    dc = cmn_c - corr
    out = {
        "cond_S": float(np.linalg.cond(S)),
        "cond_A": float(np.linalg.cond(A)),
        "cnorm_b": float(np.max(np.abs(base))),
        "cnorm_c": float(np.max(np.abs(corr))),
        "d_b": float(np.max(np.abs(db))),
        "d_c": float(np.max(np.abs(dc))),
        "minh1_resid_b": ib["resid"], "minh1_resid_c": ic["resid"],
        "resid_mn_b": float(np.max(np.abs(A @ cmn_b - 1.0))),
        "resid_mn_c": float(np.max(np.abs(A @ cmn_c
                                       - np.asarray(values)))),
        "db": [[float(x.real), float(x.imag)] for x in db],
        "dc": [[float(x.real), float(x.imag)] for x in dc]}
    print("cnorm %.3e/%.3e  d_b %.3e d_c %.3e  cond(A) %.3e"
          % (out["cnorm_b"], out["cnorm_c"], out["d_b"], out["d_c"],
             out["cond_A"]), flush=True)

    for dxi in (0.008, 0.004, 0.002):
        t0 = time.time()
        xg = np.arange(-XI, XI + dxi / 2, dxi)
        v = r80.family_values(fam, K, 0.5 - 2j * np.pi * xg, xw1600)
        p = np.real(r59.P_from_nodes(xg, cnt))
        ker = r54.kernel_at(xg, ps)
        W = ker * p * p
        lb0 = base @ v
        cc0 = corr @ v
        lb1 = (base + db) @ v
        cc1 = (corr + dc) @ v
        g0 = np.abs(lb0) ** 2 * np.abs(cc0) ** 2
        g1 = np.abs(lb1) ** 2 * np.abs(cc1) ** 2
        Q0 = float(np.trapezoid(W * g0, xg))
        Q1 = float(np.trapezoid(W * g1, xg))
        Ab = (W * np.abs(cc0) ** 2 * np.conj(lb0)) @ v.T
        Cc = (W * np.abs(lb0) ** 2 * np.conj(cc0)) @ v.T
        lin = 2 * float(np.real(np.sum(db * Ab) + np.sum(dc * Cc)))
        linbound = 2 * float(np.sum(np.abs(db) * np.abs(Ab))
                             + np.sum(np.abs(dc) * np.abs(Cc)))
        Db = np.abs(db) @ np.abs(v)
        Dc = np.abs(dc) @ np.abs(v)
        env1 = float(np.trapezoid(
            np.abs(ker) * p * p
            * (2 * np.abs(lb0) * Db * np.abs(cc0) ** 2
               + 2 * np.abs(cc0) * Dc * np.abs(lb0) ** 2), xg))
        env2 = float(np.trapezoid(
            np.abs(ker) * p * p
            * (Db ** 2 * np.abs(cc0) ** 2
               + 2 * np.abs(lb0) * Db * Dc ** 2
               + 2 * np.abs(cc0) * Db ** 2 * Dc
               + Db ** 2 * Dc ** 2), xg))
        envj_db = [float(x) for x in 2 * np.abs(db) * np.array([
            np.trapezoid(np.abs(ker) * p * p * np.abs(v[j])
                         * np.abs(cc0) ** 2 * np.abs(lb0), xg)
            for j in range(17)])]
        envj_dc = [float(x) for x in 2 * np.abs(dc) * np.array([
            np.trapezoid(np.abs(ker) * p * p * np.abs(v[j])
                         * np.abs(lb0) ** 2 * np.abs(cc0), xg)
            for j in range(17)])]
        key = "grid_%g" % dxi
        out[key] = {
            "Q0": Q0, "Q1": Q1, "dQ": Q1 - Q0, "lin": lin,
            "lin_minus_dQ": lin - (Q1 - Q0),
            "linbound": linbound, "env1": env1, "env2": env2,
            "env1_over_bound": env1 / max(linbound, 1e-300),
            "env1_over_dQ": env1 / max(abs(Q1 - Q0), 1e-300),
            "sec_over_dQ": (Q1 - Q0 - lin) / max(abs(Q1 - Q0), 1e-300),
            "Ab": [[float(x.real), float(x.imag)] for x in Ab],
            "Cc": [[float(x.real), float(x.imag)] for x in Cc],
            "envj_db": envj_db, "envj_dc": envj_dc,
            "n_pts": len(xg), "t": time.time() - t0}
        print("grid %g: dQ %.6e lin %.6e rel_gap %.3e linbound %.6e "
              "env1 %.6e env1/bound %.3e sec/dQ %.3e (%.1fs)"
              % (dxi, Q1 - Q0, lin, abs(((Q1 - Q0) - lin) / (Q1 - Q0)),
                 linbound, env1, env1 / max(linbound, 1e-300),
                 (Q1 - Q0 - lin) / max(abs(Q1 - Q0), 1e-300),
                 time.time() - t0), flush=True)
    # ---- construction check: mp-exact min-norm vs the float solve -----
    # The 2058 probe prices dQ against the mp-exact min-norm interpolant
    # cast to float, while THIS script's cmn comes from a float solve of
    # S = A A^H (cond 3.8e+08) -- a different object.  Measure the
    # deviation, the size of which explains the 12% dQ divergence between
    # the two constructions.
    import mpmath as mp
    save_dps = mp.mp.dps
    mp.mp.dps = 50
    nq2 = A.shape[0]
    vals_np = np.asarray(values)
    Am = mp.matrix(nq2, nq2)
    onev = mp.matrix(nq2, 1)
    valv = mp.matrix(nq2, 1)
    for i in range(nq2):
        for j in range(nq2):
            Am[i, j] = mp.mpc(complex(A[i, j]))
        onev[i, 0] = mp.mpf(1)
        valv[i, 0] = mp.mpc(complex(vals_np[i]))
    Sm_ = Am * Am.H
    zb_mp = Sm_ ** -1 * onev
    zc_mp = Sm_ ** -1 * valv
    cmn_mp_b = np.zeros(nq2, complex)
    cmn_mp_c = np.zeros(nq2, complex)
    for i in range(nq2):
        sb = mp.mpc(0)
        sc = mp.mpc(0)
        for k in range(nq2):
            sb += Am.H[i, k] * zb_mp[k, 0]
            sc += Am.H[i, k] * zc_mp[k, 0]
        cmn_mp_b[i] = complex(sb)
        cmn_mp_c[i] = complex(sc)
    mp.mp.dps = save_dps
    for nm, cfl, cmp_ in (("b", cmn_b, cmn_mp_b), ("c", cmn_c, cmn_mp_c)):
        out["cmn_dev_%s_abs" % nm] = float(np.max(np.abs(cfl - cmp_)))
        out["cmn_dev_%s_rel" % nm] = float(np.max(np.abs(cfl - cmp_))
                                           / np.max(np.abs(cmp_)))
    print("cmn dev float-vs-mp: b %.3e (rel %.2e) c %.3e (rel %.2e)"
          % (out["cmn_dev_b_abs"], out["cmn_dev_b_rel"],
             out["cmn_dev_c_abs"], out["cmn_dev_c_rel"]), flush=True)

    with open("results/diag_2058.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote results/diag_2058.json")


main()