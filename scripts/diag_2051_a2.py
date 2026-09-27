#!/usr/bin/env python3
# diag_2051_a2.py — localizer for the record-2051 A2 failures.
# Replicates the full rig's setup and call order (module import + g_jet),
# finds panels where the enclosed U falls below the committed float
# stencil, and at the worst ones prints BOTH stencils:
#   st_commit = |second difference| of the committed grid g_com / dxi^2
#   st_model  = same construction on the MODEL's own enclosed values
#               (j_val centres at the same 9 points, spacing h/8)
# plus the jet decomposition of U.  The point: U encloses the stored-floats
# exact-real function O; the committed grid is a different float evaluation
# C of the same object.  If st_model <= U while st_commit > U, the failure
# is the C-vs-O evaluation gap (an L5-class line to book), not an enclosure
# defect.
#
# CLI: python3 scripts/diag_2051_a2.py H LIMIT

import os
import sys
import time

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402
import routea_l3_aggregate_2051 as rig  # noqa: E402

XI_MAX = rig.XI_MAX


def main():
    h = float(sys.argv[1]) if len(sys.argv) > 1 else 0.001
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    t0 = time.time()
    rho_o, nodes_o, values, fam, xw, gram, a_mat, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, _ = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    model = rig.Model(fam, r37.K, xw, base, corr, r80.counterpart_nodes(rho_o))

    dxi_g = 0.00025
    n_g = int(round(2 * XI_MAX / dxi_g))
    edges = np.linspace(-XI_MAX, XI_MAX, n_g + 1)
    s = 0.5 - 2j * np.pi * edges
    v = r80.family_values(fam, r37.K, s, xw)
    lb_f = base @ v
    p_f = np.real(r59.P_from_nodes(edges, r80.counterpart_nodes(rho_o)))
    g_com = np.asarray(p_f * p_f * np.abs(lb_f) ** 2
                       * np.abs(corr @ v) ** 2, dtype=float)
    gpp = np.empty_like(g_com)
    gpp[1:-1] = (g_com[2:] - 2 * g_com[1:-1] + g_com[:-2]) / (dxi_g ** 2)
    gpp[0] = gpp[1]
    gpp[-1] = gpp[-2]
    print("grid %.0fs gmax %.6g" % (time.time() - t0, g_com.max()), flush=True)

    n_pan = int(round(2 * XI_MAX / h))
    grid = np.linspace(-XI_MAX, XI_MAX, n_pan + 1)
    nodes = grid[:-1]
    step = int(round(h / dxi_g))
    h_sub = h / 8.0
    ts = np.arange(9) * h_sub
    viol = []
    for lo in range(0, n_pan, 4096):
        hi = min(lo + 4096, n_pan)
        xc = nodes[lo:hi]
        k = hi - lo
        gj = model.g_jet(xc, h, 4096)
        UU = rig.j_supk(gj, 2, h)
        idx = np.round((xc + XI_MAX) / dxi_g).astype(np.int64)
        j0 = idx[0]
        sl = np.abs(gpp[j0:j0 + step * k]).reshape(k, step).max(axis=1)
        st = np.maximum(sl, np.abs(gpp[j0 + step:j0 + step * k + 1:step]))
        bad = np.where(UU < st * (1 - 1e-9))[0]
        for b in bad:
            viol.append((lo + int(b), float(st[b]), float(UU[b])))
    print("h %g panels %d violations %d  (%.0fs)"
          % (h, n_pan, len(viol), time.time() - t0), flush=True)
    viol.sort(key=lambda t: -(t[1] / t[2]))
    for pi, st_c, uu in viol[:limit]:
        xi = float(nodes[pi])
        j0 = int(round((xi + XI_MAX) / dxi_g))
        gj = model.g_jet(nodes[pi:pi + 1], h, 4096)
        gv = [rig.j_val(gj, float(t), h)[0][0] for t in ts]
        gvm = np.array(gv, dtype=float)
        st_m = float(np.max(np.abs(np.diff(gvm, 2))) / (h_sub ** 2))
        b2 = float(np.abs(gj[2][0][0]) + gj[2][1][0])
        b3 = float(h * (np.abs(gj[3][0][0]) + gj[3][1][0]))
        k4 = float(h * h / 2.0 * gj[4][0])
        gmass = float(np.max(np.abs(g_com[j0:j0 + step + 1])))
        print("-" * 72)
        print("panel %d xi %.6f  st_commit %.6g  st_model %.6g  U %.6g"
              % (pi, xi, st_c, st_m, uu))
        print("  st_c/U %.4f  st_m/U %.4f  local gmax %.6g (gmax %.3g)"
              % (st_c / uu, st_m / uu, gmass, g_com.max()))
        print("  U parts: |b2|+e2 %.6g  h(|b3|+e3) %.6g  h^2/2 K4 %.6g"
              % (b2, b3, k4))
        print("  fd-excess term (dxi^2/12)K4 %.6g"
              % ((dxi_g ** 2 / 12.0) * float(gj[0][4][0])))
    print("done %.0fs" % (time.time() - t0), flush=True)


if __name__ == "__main__":
    main()