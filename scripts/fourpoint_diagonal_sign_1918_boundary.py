#!/usr/bin/env python3
# fourpoint_diagonal_sign_1918_boundary.py — record 1918 boundary scan
#
# Scouting extension of scripts/fourpoint_diagonal_sign_1918.py (imported as a
# module; its engines are reused verbatim). Question: on the committed-class
# family, does the vertex-branch verdict (D > 0, gate determinant
# D*C - B01^2 < 0, B01 = B10 to 2.8e-12 measured) survive as the bump width c
# and the height gamma grow, or does the relative margin
# B01^2/(D*C) - 1 vanish/flip at some boundary?
#
# Grid: widths {1.3, 1.6, 2.0, 2.4, 3.0} x heights {21.0220, 30.4249},
# abscissa delta = 0.05. Certified reading (law F79): D from the analytic-Fhat
# engine E4 with E3 as the certified-pair check; certified sensitivity
# propagates that pair plus the three-engine spread of the small entries.
# No gate sign is proved here.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402


def ics(entry):
    return rig.gate_engines_ic(entry)


def spread(entry):
    v = [entry["IC"], entry["IC_direct"], entry["IC_split"]]
    return max(v) - min(v)


def main():
    rig.log("record 1918 boundary scan — vertex branch vs width and height")
    widths = [1.3, 1.6, 2.0, 2.4, 3.0]
    gammas = [21.022039638771555, 30.424876125859513]
    delta = 0.05
    out = []
    for c in widths:
        g = rig.bump(c)
        sp_g = rig.CubicSpline(rig.XG, g)
        for gamma in gammas:
            rho = (0.5 + delta) + 1j * gamma
            tag = "c=%.1f g=%.2f" % (c, gamma)
            rig.log("case %s rho = %.3f %+.6fi" % (tag, rho.real, rho.imag))
            u, nodes = rig.fourpoint_annihilator(g, rho)
            S_pair = 2.0 * c

            def Fhat_u2(xi):
                s = -2j * np.pi * xi
                Lu_s = rig.poly_P(s, nodes) * rig.laplace_read(sp_g, s)
                Lu_cs = rig.poly_P(np.conj(s), nodes) * \
                    rig.laplace_read(sp_g, np.conj(s))
                return np.conj(Lu_cs) * Lu_s

            eD = rig.gate_entry(u, u, S_pair, tag="D", Fhat_analytic=Fhat_u2)
            eC = rig.gate_entry(g, g, S_pair, tag="C")
            eB = rig.gate_entry(u, g, S_pair, tag="B01")

            Ds = ics(eD)
            D = Ds.get("E4", Ds["E3"])
            dD_pair = abs(Ds.get("E4", Ds["E3"]) - Ds["E3"])
            C = ics(eC)["E3"]
            B01 = ics(eB)["E3"]
            # B10 = B01 by the measured cross-term symmetry (<= 2.8e-12).
            Bs = 2.0 * B01
            disc = Bs * Bs - 4.0 * C * D
            det = D * C - B01 * B01
            margin = disc / (4.0 * C * D)
            ddisc_cert = (2.0 * abs(Bs) * 2.0 * spread(eB)
                          + 4.0 * abs(C) * dD_pair + 4.0 * abs(D) * spread(eC))
            lam_v = Bs / (2.0 * C)
            branch = "vertex" if (D > 0 and disc > 0) else "NOT-vertex"
            rig.log("  -> D=%+.4e C=%+.4e B01=%+.4e det=%+.4e margin=%+.3e "
                    "disc=%+.3e (cert sens %.1e) lam=%+.4e branch=%s"
                    % (D, C, B01, det, margin, disc, ddisc_cert, lam_v,
                       branch))
            out.append({"tag": tag, "c": c, "gamma": gamma, "D": D, "C": C,
                        "B01": B01, "det": det, "margin_rel": margin,
                        "disc": disc, "ddisc_cert": ddisc_cert,
                        "lam_vertex": lam_v, "branch": branch})
    ok = sum(1 for r in out if r["branch"] == "vertex")
    worst = min(out, key=lambda r: r["margin_rel"])
    rig.log("BOUNDARY SUMMARY vertex-branch cases: %d of %d; min margin %.3e "
            "at %s; max width with vertex: %s"
            % (ok, len(out), worst["margin_rel"], worst["tag"],
               max((r["c"] for r in out if r["branch"] == "vertex"),
                   default=None)))
    os.makedirs("results", exist_ok=True)
    with open("results/1918_fourpoint_diagonal_sign_boundary.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    rig.log("wrote results/1918_fourpoint_diagonal_sign_boundary.json")


if __name__ == "__main__":
    main()