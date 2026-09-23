#!/usr/bin/env python3
# fourpoint_gate_kernel_stress_1920.py — record 1920 (scouting)
#
# Stress test for the record-1919 variance-gap criterion on the ARCH channel
# of the Cut-2 gate.  Question: is
#
#   det_arch < 0   <=>   f*Var_- + f*(1+f)*Delta^2 > (1+f)*Var_+
#
# structural for a WIDE class of nonnegative spectral densities W, or is it
# an accident of the bump family?
#
# Arch channel measure: mu = sigma(2*pi*xi) * W(xi) * dxi on the padded FFT
# grid (the same discrete object whose kernel-form determinant matched the
# E3 engine to 2.6e-8 in record 1919).  sigma has a single sign flip at
# u* = 6.289836 (xi* = 1.0011), so the positive region is one interval and
# the sign split of mu is a threshold split.
#
# Reported per (W, gamma): f (negative mass ratio), Var_+/Var_-, Delta, and
# the criterion ratio
#
#   R = (f*Var_- + f*(1+f)*Delta^2) / ((1+f)*Var_+),
#
# criterion holds iff R > 1.  No proof here; scouting only.

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402

DXI = 1.0 / (rig.NF * rig.DU)


def stats(mu, x):
    mp = mu[mu > 0].sum()
    mm = -mu[mu < 0].sum()
    xp = (mu * x)[mu > 0].sum() / mp
    xm = -(mu * x)[mu < 0].sum() / mm
    vp = (mu * x * x)[mu > 0].sum() / mp - xp * xp
    vm = -(mu * x * x)[mu < 0].sum() / mm - xm * xm
    return mp, mm, xp, xm, vp, vm


def ratio_sigma(W, gm, sig, dxi=DXI):
    """sigma(2 pi xi) with width gm; returns (f, m+, m-, Delta, V+/V-)."""
    mu = sig * W * dxi
    mp, mm, xp, xm, vp, vm = stats(mu, gm)
    if mp <= 0 or mm <= 0:
        return None
    A = mp - mm
    f = mm / A
    return A, f, xp, xm, xp - xm, vp, vm


def main():
    rig.log("record 1920 — arch-channel variance-gap stress test")
    xi = np.fft.fftfreq(rig.NF, d=rig.DU)
    om = 2.0 * np.pi * xi
    sig = rig.sigma_vec(om)
    pos = sig > 0
    rig.log("sigma sign split: positive on |xi| < %.4f (grid), "
            "mass share %.4f of uniform"
            % (np.max(np.abs(xi[pos])), pos.mean()))
    out = []
    gammas = [14.134725141734693, 21.022039638771555, 30.424876125859513]
    delta = 0.05

    # W families
    fams = []
    for c in (0.5, 1.0, 2.0, 4.0):
        g = rig.bump(c)
        Fp = np.zeros(rig.NF, dtype=complex)
        Fp[:rig.N] = g
        Fh = rig.DU * np.fft.fft(Fp)
        fams.append(("bump c=%.1f" % c, (Fh * np.conj(Fh)).real))
    for s in (0.3, 1.0, 3.0, 10.0):
        fams.append(("gauss s=%.1f" % s,
                     np.exp(-xi * xi / (2.0 * s * s))))
    for U in (0.5, 0.8, 1.20, 2.0, 5.0):
        fams.append(("box U=%.2f" % U, (np.abs(xi) < U).astype(float)))

    print("%-12s %8s %10s %10s %12s %12s %12s %8s"
          % ("W", "gamma", "A", "f", "Var-/Var+", "D^2/Var+", "R", "hold"))
    for name, W in fams:
        W = W / np.max(W)
        for gm_h in (gammas[:1] + gammas[2:]):
            P = (delta * delta + gm_h * gm_h - om * om) ** 2 \
                + 4.0 * delta * delta * om * om
            r = ratio_sigma(W, P, sig)
            if r is None:
                print("%-12s %8.2f %10s %10s %12s %12s %12s %8s"
                      % (name, gm_h, "-", "-", "-", "-", "-",
                         "no-sign-split"))
                out.append({"W": name, "gamma": gm_h, "hold": None})
                continue
            A, f, xp, xm, dm, vp, vm = r
            R = (f * vm + f * (1.0 + f) * dm * dm) / ((1.0 + f) * vp)
            hold = R > 1.0
            print("%-12s %8.2f %10.3e %10.5f %12.4e %12.4e %12.4e %8s"
                  % (name, gm_h, A, f, vm / vp, dm * dm / vp, R, hold))
            out.append({"W": name, "gamma": gm_h, "A": A, "f": f,
                        "Var_ratio": vm / vp, "D2_over_Vp": dm * dm / vp,
                        "R": R, "hold": bool(hold)})
    ok = sum(1 for r in out if r.get("hold"))
    rig.log("hold: %d of %d" % (ok, len(out)))
    fails = [r for r in out if r.get("hold") is False]
    for r in fails:
        rig.log("  fail: %s gamma=%.2f R=%.4f"
                % (r["W"], r["gamma"], r["R"]))
    os.makedirs("results", exist_ok=True)
    with open("results/1920_gate_kernel_stress.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    rig.log("wrote results/1920_gate_kernel_stress.json")


if __name__ == "__main__":
    main()