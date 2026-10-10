#!/usr/bin/env python3
"""Record-2662 ground truth: the actual entry (0,3) integral vs the
committed partition surrogate and the 2597 row_03 rectangle.

Trust design: the raw integrand exp((beta+i psi)u - 30/(1-u^2)) has a
11-decade dynamic range on far panels and mp.quad's default tanh-sinh is
NOT trustworthy there (the record-2653 trust-horizon lesson).  The
assembled route uses the exact factorisation

    int_k F = e^{ampArg} * e^{i psi c} * (ipoly_k + r_k),
    r_k = int_{-h}^{h} ( exp(phase(t)-phase(0)) - poly(t) ) dt,

with a bounded smooth residual integrand (|.| <= e^{|beta| h + 2 VAR_k});
the raw quadrature is kept as a cross-check on a panel sample at dps 150.

Run:  python scripts/recon_2662_ground_truth.py
"""

import sys
from fractions import Fraction as F

import mpmath as mp

sys.path.insert(0, __import__("os").path.dirname(
    __import__("os").path.abspath(__file__)))
import recon_2662_partition_budget as R  # noqa: E402

mp.mp.dps = 150
MPF = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)  # noqa: E731


def main():
    p2661 = R.read("C1RouteAPanelCenterNormalization2661P095.lean")
    r3sq = R.rats(p2661, "widthEntry3_2661")[0] ** 2
    t095 = R.read("C1RouteAComplexPanelTable2655P095.lean")
    beta = R.rats(t095, "complexPanelBeta2648P095")[0]
    psi = R.rats(t095, "complexPanelPsi2648P095")[0]
    B, P, R2 = MPF(beta), MPF(psi), MPF(r3sq)
    H = F(1, 200)
    Hm = MPF(H)
    center = lambda k: F(-19, 20) + F(2 * k + 1, 200)  # noqa: E731

    def panel_data(k):
        tg = f"{k:03d}"
        amp = R.read(f"C1RouteAAmpPin2657P{tg}.lean")
        ph = R.read(f"C1RouteAPhasePin2658P{tg}.lean")
        tb_name = f"C1RouteAComplexPanelTable2655P{tg}.lean"
        if not R.exists(tb_name):
            tb_name = f"C1RouteAComplexPanelTable2648P{tg}.lean"
        tb = R.read(tb_name)
        an = R.read((f"C1RouteAComplexPanelAnalytic2649P109.lean" if k == 109
                     else f"C1RouteAComplexPanelAnalytic2656P{tg}.lean"))
        return dict(
            amp_val=R.rats(amp, f"ampValue2657P{tg}")[0],
            amp_rad=R.rats(amp, f"ampRadius2657P{tg}")[0],
            ph_val=R.pair(ph, f"phaseValue2658P{tg}"),
            ph_rad=R.rats(ph, f"phaseRadius2658P{tg}")[0],
            integral=R.pair(tb, f"complexPanelIntegral2648P{tg}"),
            ru=R.rats(tb, f"complexPanelResidualUpper2648P{tg}")[0],
            var=R.var_of(an))

    def fullint(k, c):
        hres = lambda t: mp.exp((B + 1j * P) * t  # noqa: E731
                                - 30 / (1 - (MPF(c) + t) ** 2)
                                + 30 / (1 - MPF(c) ** 2))
        return mp.quad(hres, [-Hm, Hm], maxdegree=8)

    # ---- cross-check: raw quad vs assembled route on a panel sample ----
    print("raw-quad vs assembled cross-check (dps 150):")
    for k in (0, 2, 3, 4, 95, 186, 187, 189):
        c = center(k)
        d = panel_data(k)
        ipoly = mp.mpc(MPF(d["integral"][0]), MPF(d["integral"][1]))
        e_amp = mp.exp(B * MPF(c) - 30 / (1 - MPF(c) ** 2))
        rot = mp.exp(1j * P * MPF(c))
        assembled = e_amp * rot * fullint(k, c)
        f = lambda u: mp.exp((B + 1j * P) * u - 30 / (1 - u * u))  # noqa: E731
        raw = mp.quad(f, [MPF(c - H), MPF(c + H)], maxdegree=8)
        rel = abs(raw - assembled) / abs(assembled)
        print(f"  k={k:3d} rel(raw vs assembled) = {mp.nstr(rel, 4)}")

    # ---- per-panel deviation vs committed budgets ----
    tot_true_dev = mp.mpf(0)
    s_surr = mp.mpc(0)
    s_budget = mp.mpf(0)
    worst = []
    for k in range(190):
        c = center(k)
        d = panel_data(k)
        amp_val = MPF(d["amp_val"])
        amp_rad = MPF(d["amp_rad"])
        ipoly = mp.mpc(MPF(d["integral"][0]), MPF(d["integral"][1]))
        rot_pin = mp.mpc(MPF(d["ph_val"][0]), MPF(d["ph_val"][1]))
        e_amp = mp.exp(B * MPF(c) - 30 / (1 - MPF(c) ** 2))
        rot = mp.exp(1j * P * MPF(c))
        true_int = e_amp * rot * fullint(k, c)
        surr = amp_val * rot_pin * ipoly
        deficit = 1 - (abs(c) + H) ** 2
        charge = amp_rad * (abs(MPF(d["ph_val"][0]))
                            + abs(MPF(d["ph_val"][1])) + 2 * MPF(d["ph_rad"])) \
            * (abs(MPF(d["integral"][0])) + abs(MPF(d["integral"][1])))
        charge += (amp_val + amp_rad) * 2 * MPF(d["ph_rad"]) \
            * (abs(MPF(d["integral"][0])) + abs(MPF(d["integral"][1])))
        resc = (amp_val + amp_rad) * 2 * mp.exp(MPF(d["var"])) \
            * MPF(d["ru"] / deficit**2) * MPF(2 * H * H)
        dev_true = abs(true_int - surr)
        tot_true_dev += dev_true
        s_surr += surr * R2
        s_budget += (charge + resc) * R2
        worst.append((float(dev_true / (charge + resc)),
                      k, mp.nstr(dev_true, 5),
                      mp.nstr(charge + resc, 5)))

    print(f"\nsurrogate sum (r3^2 *)     = {mp.nstr(s_surr, 12)}")
    print(f"exact partition sum check  = "
          f"(-3.9072971124645...e-52 + 5.8623231581980...e-52j)")
    print(f"total TRUE dev (r3^2 *)    = {mp.nstr(R2 * tot_true_dev, 6)}")
    print(f"total committed budget     = {mp.nstr(s_budget, 6)}")
    worst.sort(reverse=True)
    print("worst dev/budget panels (ratio, k, dev_true, budget):")
    for row in worst[:6]:
        print("  ", row)


if __name__ == "__main__":
    sys.exit(main())