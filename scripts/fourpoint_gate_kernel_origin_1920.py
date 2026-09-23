#!/usr/bin/env python3
# fourpoint_gate_kernel_origin_1920.py — record 1920 (scouting, part c)
#
# Mechanism attribution for the negative mass of mu = K*W*dxi as the owner
# widens.  The arch symbol sigma is positive exactly on |xi| < xi* = 1.0011,
# so inside that interval every negative value of the FULL kernel
# K = sigma + K_prime is created by the visible prime sum (sigma > 0 there).
# Outside, sigma < 0 already contributes.
#
# Reported per c: W mass share inside |xi| < xi*, negative-mass shares
# N_in / N_out, the arch-only negative mass N_arch, and the prime-kernel
# amplitude against sigma at xi = 0.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402
import fourpoint_gate_kernel_form_1919 as kf  # noqa: E402

G21 = 21.022039638771555


def main():
    rig.log("record 1920c — origin of the negative mass (sigma tail vs "
            "prime oscillations)")
    dxi = 1.0 / (rig.NF * rig.DU)
    print("%-5s %10s %10s %10s %10s %10s %10s %8s %10s"
          % ("c", "W_in", "N_in", "N_out", "N_arch", "N_in/N", "Kp0", "schg",
             "det_arch"))
    out = []
    for c in (0.5, 1.0, 1.3, 2.0, 3.0):
        g = rig.bump(c)
        xi, Fh = kf.ghat_grid(g)
        W = (Fh * np.conj(Fh)).real
        om = 2.0 * np.pi * xi
        S_pair = 2.0 * c
        K = kf.kernel_grid(xi, S_pair)
        sig = rig.sigma_vec(om)
        pos = sig > 0
        dmu = K * W * dxi
        Nin = -dmu[(dmu < 0) & pos].sum()
        Nout = -dmu[(dmu < 0) & (~pos)].sum()
        N = Nin + Nout
        Narch = -(sig * W * dxi)[sig < 0].sum()
        Win = (W[pos].sum() * dxi)
        Wtot = W.sum() * dxi
        Kp0 = float(K[np.argmin(np.abs(xi))]) - float(
            sig[np.argmin(np.abs(xi))])
        # sign changes of K inside the sigma-positive interval
        order = np.argsort(xi)
        ins = order[pos[order]]
        Ks = K[ins]
        schg = int(np.sum(np.diff(np.sign(Ks)) != 0))
        # arch-channel determinant (k-form)
        da = float(np.sum(sig * W) * dxi)
        d1 = float(np.sum(sig * om ** 0 * W) * dxi)
        P = (0.0025 + G21 * G21 - om * om) ** 2 + 4.0 * 0.0025 * om * om
        det_arch = float(np.sum(sig * P * P * W) * dxi) * da \
            - float(np.sum(sig * P * W) * dxi) ** 2
        print("%-5.1f %10.3e %10.3e %10.3e %10.3e %10.3f %10.2f %8d %10.3e"
              % (c, Win, Nin, Nout, Narch, Nin / N if N else 0.0, Kp0,
                 schg, det_arch))
        out.append({"c": c, "W_inside": Win, "W_total": Wtot, "N_in": Nin,
                    "N_out": Nout, "N_arch": Narch,
                    "N_in_share": Nin / N if N else 0.0, "Kprime_0": Kp0,
                    "K_sign_changes_inside": schg, "det_arch": det_arch})
    os.makedirs("results", exist_ok=True)
    with open("results/1920_gate_kernel_origin.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    rig.log("wrote results/1920_gate_kernel_origin.json")


if __name__ == "__main__":
    main()