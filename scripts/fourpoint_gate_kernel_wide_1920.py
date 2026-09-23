#!/usr/bin/env python3
# fourpoint_gate_kernel_wide_1920.py — record 1920 (scouting, part b)
#
# Where does the arch channel's variance-gap criterion stop holding as the
# owner widens, and does the FULL kernel (with the visible prime powers)
# survive there?  Kernel-form only (record 1919 machinery, imported): no
# engine arbitration here, since the 1919 identity check already fixed the
# k-form against the certified pair.
#
# For each (c, gamma): W = |ghat|^2 from the c-bump, P the orbit quartic,
# mu = K*W*dxi for K = full and K = sigma (arch).  Reported: A, f, the
# criterion ratio R (only meaningful when A > 0), and det = I2*A - I1^2 with
# the identity self-check det vs A^2*Var_nu.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402
import fourpoint_gate_kernel_form_1919 as kf  # noqa: E402

G14 = 14.134725141734693
G21 = 21.022039638771555


def main():
    rig.log("record 1920b — wide-owner scan of the variance-gap criterion")
    dxi = 1.0 / (rig.NF * rig.DU)
    delta = 0.05
    cases = [(c, gm) for c in (1.3, 1.6, 2.0, 2.4, 3.0)
             for gm in (G14, G21)]
    out = []
    print("%-5s %8s %6s %10s %10s %12s %14s %8s %8s"
          % ("c", "gamma", "chan", "A", "f", "det", "R", "hold", "idchk"))
    for c, gm in cases:
        g = rig.bump(c)
        xi, Fh = kf.ghat_grid(g)
        W = (Fh * np.conj(Fh)).real
        om = 2.0 * np.pi * xi
        P = (delta * delta + gm * gm - om * om) ** 2 \
            + 4.0 * delta * delta * om * om
        S_pair = 2.0 * c
        K = kf.kernel_grid(xi, S_pair)
        sig = rig.sigma_vec(om)
        Kp = K - sig
        dets = {}
        for name, ker in (("full", K), ("arch", sig), ("prime", Kp)):
            A = float(np.sum(ker * W) * dxi)
            I1 = float(np.sum(ker * P * W) * dxi)
            I2 = float(np.sum(ker * P * P * W) * dxi)
            det = I2 * A - I1 * I1
            dets[name] = det
            mu = ker * W * dxi
            mp, mm, xp, xm, vp, vm = kf.stats(mu, P)
            f = mm / A if A != 0 else float("nan")
            dm = xp - xm
            var = (1.0 + f) * vp - f * vm - f * (1.0 + f) * dm * dm
            idrel = (A * A * var - det) / det if det != 0 else float("nan")
            R = ((f * vm + f * (1.0 + f) * dm * dm) / ((1.0 + f) * vp)
                 if (1.0 + f) > 0 else None)
            hold = None if R is None else bool(R > 1.0)
            Rstr = "%.4e" % R if R is not None else "out-class"
            holdstr = str(hold) if hold is not None else "n/a"
            print("%-5.1f %8.2f %6s %10.3e %10.5f %12.4e %14s %8s %8.1e"
                  % (c, gm, name, A, f, det, Rstr, holdstr, idrel))
            out.append({"c": c, "gamma": gm, "channel": name, "A": A,
                        "f": f, "det": det, "R": R, "hold": hold,
                        "identity_rel": idrel})
        cross = dets["full"] - dets["arch"] - dets["prime"]
        print("%-5.1f %8.2f %6s %10s %10s %12.4e %14s"
              % (c, gm, "cross", "", "", cross, ""))
        out.append({"c": c, "gamma": gm, "channel": "cross", "det": cross})
    # verdict lines
    for name in ("full", "arch"):
        rows = [r for r in out if r["channel"] == name]
        holds = [r for r in rows if r["hold"]]
        last_c = max((r["c"] for r in holds), default=None)
        rig.log("%s: holds on %d of %d rows; max c with hold: %s"
                % (name, len(holds), len(rows), last_c))
    os.makedirs("results", exist_ok=True)
    with open("results/1920_gate_kernel_wide.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    rig.log("wrote results/1920_gate_kernel_wide.json")


if __name__ == "__main__":
    main()