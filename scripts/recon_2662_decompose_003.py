#!/usr/bin/env python3
"""Record-2662 k=3 deviation decomposition: which term carries the 8.7e-87
raw deviation, and does the true residual integral respect the certified R.
"""

import os
import sys
from fractions import Fraction as F

import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import recon_2662_partition_budget as R  # noqa: E402

mp.mp.dps = 80
MPF = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)  # noqa: E731


def main():
    p2661 = R.read("C1RouteAPanelCenterNormalization2661P095.lean")
    r3sq = R.rats(p2661, "widthEntry3_2661")[0] ** 2
    t095 = R.read("C1RouteAComplexPanelTable2655P095.lean")
    beta = R.rats(t095, "complexPanelBeta2648P095")[0]
    psi = R.rats(t095, "complexPanelPsi2648P095")[0]
    B, P, R2 = MPF(beta), MPF(psi), MPF(r3sq)
    H = F(1, 200)
    center = lambda k: F(-19, 20) + F(2 * k + 1, 200)  # noqa: E731

    for k in (3, 95):
        tg = f"{k:03d}"
        amp = R.read(f"C1RouteAAmpPin2657P{tg}.lean")
        ph = R.read(f"C1RouteAPhasePin2658P{tg}.lean")
        tb = R.read(f"C1RouteAComplexPanelTable2655P{tg}.lean")
        an = R.read(f"C1RouteAComplexPanelAnalytic2656P{tg}.lean")
        amp_val = MPF(R.rats(amp, f"ampValue2657P{tg}")[0])
        amp_rad = R.rats(amp, f"ampRadius2657P{tg}")[0]
        ph_val = R.pair(ph, f"phaseValue2658P{tg}")
        ph_rad = R.rats(ph, f"phaseRadius2658P{tg}")[0]
        integral = R.pair(tb, f"complexPanelIntegral2648P{tg}")
        ru = R.rats(tb, f"complexPanelResidualUpper2648P{tg}")[0]
        var = R.var_of(an)
        c = center(k)
        deficit = 1 - (abs(c) + H) ** 2
        cl, cr = c - H, c + H
        ph0 = -30 / (1 - c * c)

        e_amp = mp.exp(B * MPF(c) + ph0)          # true e^{ampArg}
        rot_c = mp.exp(1j * P * MPF(c))           # true e^{i psi c}
        rot_pin = mp.mpc(MPF(ph_val[0]), MPF(ph_val[1]))
        ipoly = mp.mpc(MPF(integral[0]), MPF(integral[1]))
        f = lambda u: mp.exp((B + 1j * P) * u - 30 / (1 - u * u))  # noqa: E731
        g = lambda t: mp.exp((B + 1j * P) * MPF(c + t) - 30 / (1 - (MPF(c) + t) ** 2))  # noqa: E731,E501
        hres = lambda t: mp.exp((B + 1j * P) * t - 30 / (1 - (MPF(c) + t) ** 2) - ph0)  # noqa: E731,E501
        tv = mp.quad(f, [MPF(cl), MPF(cr)])
        rtrue = mp.quad(hres, [MPF(-H), MPF(H)]) - ipoly
        R_cert = mp.exp(MPF(var)) * MPF(ru / deficit**2) * MPF(2 * H * H)
        surr = amp_val * rot_pin * ipoly
        dev = abs(tv - surr)
        t_amp = abs(e_amp - amp_val)
        t_rot = abs(rot_c - rot_pin)
        t_res = abs(rtrue)
        print(f"\n== k={k}  c={float(c):+.4f}  var={float(var):.4f}")
        print(f"ampV={mp.nstr(amp_val,8)} ampR={mp.nstr(MPF(amp_rad),4)} "
              f"|e_amp-ampV|={mp.nstr(t_amp,4)}")
        print(f"phR={mp.nstr(MPF(ph_rad),4)} L1(rot_c-rot_pin)={mp.nstr(t_rot,4)}")
        print(f"true residual int={mp.nstr(mp.nstr(t_res,6))}  "
              f"certified R={mp.nstr(R_cert,4)}  ratio="
              f"{mp.nstr(t_res / R_cert, 4) if R_cert > 0 else 'inf'}")
        print(f"|intpoly|={mp.nstr(abs(ipoly),6)}")
        print(f"dev(raw)={mp.nstr(dev,6)}")
        print(f"  term_amp = t_amp*|ipoly| = {mp.nstr(t_amp * abs(ipoly),4)}")
        print(f"  term_rot = e_amp*t_rot*|ipoly| = "
              f"{mp.nstr(e_amp * t_rot * abs(ipoly),4)}")
        print(f"  term_res = e_amp*t_res = {mp.nstr(e_amp * t_res,4)}")


if __name__ == "__main__":
    sys.exit(main())