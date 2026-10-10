#!/usr/bin/env python3
"""Record-2663 budget recon v2: exact-rational 190-panel charge ledger with the
RATIONALIZED residual factor `3^n` (the Lean-side bound), plus the base-2 edge
slices, against the committed entry (0,3) home rectangle; and the frozen 60-
significant-digit bar literals consumed by the generated assembly modules.

v2 changes vs v1 (all recorded in the 2663 record):
  - edge device is base-2: |F u| <= e^(|beta| - 4000/13) on 19/20 <= |u| <= 1,
    and a0bar = 4000/13 - |beta| >= 605/2 suffices for e^(-a0bar) <= 2^(-302)
    (no log-3 constants in Lean: e^(605/2) >= e^302 > 2^302 > 0);
  - emits results/2663_bars.json with per-panel floor/ceil bars at 60
    significant decimal digits (re, im, charge) plus the frozen sums, for the
    generated per-panel bar theorems and the decide+kernel sum evaluations.

v3 changes vs v2:
  - asserts the four strict-coordinate barrier facts the generated assembly
    consumes: reBarLo = r3sq*(LO_re - (CBAR + EBAR)) >= reLo,
    reBarHi = r3sq*(HI_re + (CBAR + EBAR)) <= reHi, and the im analogues,
    all as exact rationals; emits them (with the rectangle endpoints) into
    results/2663_budget_recon.json under `barriers`.

Everything is parsed from committed Lean literals (no float display text):

  r3      = widthEntry3_2661        (owner multiplier r3^2)
  beta    = complexPanelBeta2648P*  (asserted equal across probe panels and
                                     tied exactly to Re(node0) * r3^2)
  per k   = ampValue/ampRadius (2657 pins), phaseRadius/phaseValue (2658),
            complexPanelIntegral2648P* and complexPanelResidualUpper2648P*
            (table modules), deficit (2656/2649 analytic modules)
  charge_k = ampRadius * (M1 + 2 phRad) * M2
             + (ampValue + ampRadius) * 2 phRad * M2          (assembly)
  res_k    = (ampValue + ampRadius) * 2 * (3^n * RU / ds) * (2 h^2)
  center_k = ampValue * (phaseValue * integral)              (complex pair)

Ledger: total = r3^2 * Sum_k (charge_k + res_k) + (1/10) * 2^(-302);
margin_axis = halfwidth_axis - |r3^2 * Sum center_axis - rect center_axis|;
the brick requires margin_axis >= total on BOTH axes.

Bars (60 significant digits, step 10^(e-60), e = floor(log10 |x|)):
  reLo/reHi, imLo/imHi floor/ceil the exact per-panel center;
  chBar ceils charge_k + res_k.  Frozen sums are the exact rational sums of
  the bar literals (a valid floor/ceil of the true sum by construction).

Recon only: no Lean claim.  Out: results/2663_budget_recon.json and
results/2663_bars.json
"""

import json
import math
import os
import re
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_2663_slots as S  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
H = F(1, 200)          # panel half width
EDGE_LEN = F(1, 20)    # each edge slice length
EDGE_POW2 = 302        # 2^-302 edge bar (needs a0bar >= 605/2 >= 302 log 2)
SIGDIG = 60            # bar significant digits


def bars60(x):
    """Floor and ceil of x on the 60-significant-digit decimal grid."""
    if x == 0:
        return F(0), F(0)
    e = math.floor(math.log10(abs(float(x))))
    step = F(10) ** (e - SIGDIG)
    return (x // step) * step, -((-x) // step) * step


def fstr(x):
    return f"{x.numerator}/{x.denominator}"


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    # ---- owner multiplier and coefficient (exact literals) ----
    p2661 = S.read("C1RouteAPanelCenterNormalization2661P095.lean")
    r3 = S.rats(p2661, "widthEntry3_2661")[0]
    r3sq = r3 ** 2
    node_re = S.rats(p2661, "nodeEntry0_2661")[0]

    betas = {}
    for k in (0, 94, 95, 109, 189):
        s = S.slots(k)
        betas[k] = S.rats(S.read(s["table_module"]), f"complexPanelBeta2648P{s['tag']}")[0]
    beta = betas[95]
    assert len(set(betas.values())) == 1, betas
    assert beta == node_re * r3sq, (beta, node_re * r3sq)
    print(f"beta = {beta}  (== Re(node0) * r3^2: OK)")

    # ---- edge bar (base 2) ----
    a0bar = F(4000, 13) - abs(beta)
    assert a0bar >= F(605, 2), f"edge bar fails: a0bar = {float(a0bar)}"
    edge_total = 2 * EDGE_LEN * F(2) ** (-EDGE_POW2)
    print(f"edge: a0bar = {float(a0bar):.6f} (>= 605/2 = 302.5), "
          f"edge_total = {float(edge_total):.3e}")

    # ---- per-panel charges, centers, bars (exact) ----
    rows = []
    for k in range(190):
        s = S.slots(k)
        tag = s["tag"]
        ph = S.read(s["phase_module"] + ".lean")
        tb = S.read(s["table_module"])
        ph_val = S.pair(ph, f"phaseValue2658P{tag}")
        integral = S.pair(tb, f"complexPanelIntegral2648P{tag}")
        m1 = abs(ph_val[0]) + abs(ph_val[1])
        m2 = abs(integral[0]) + abs(integral[1])
        ru = S.rats(tb, f"complexPanelResidualUpper2648P{tag}")[0]
        ds = F(s["deficit"][0], s["deficit"][1]) ** 2
        charge = (s["amp_rad"] * (m1 + 2 * s["ph_rad"]) * m2
                  + (s["amp_val"] + s["amp_rad"]) * (2 * s["ph_rad"]) * m2)
        res = (s["amp_val"] + s["amp_rad"]) * (
            2 * (F(3) ** s["n"] * (ru / ds)) * (2 * H * H))
        c_re = s["amp_val"] * (ph_val[0] * integral[0] - ph_val[1] * integral[1])
        c_im = s["amp_val"] * (ph_val[0] * integral[1] + ph_val[1] * integral[0])
        re_lo, re_hi = bars60(c_re)
        im_lo, im_hi = bars60(c_im)
        ch_lo, ch_hi = bars60(charge + res)
        assert ch_hi >= charge + res >= ch_lo
        rows.append(dict(k=k, tag=tag, n=s["n"], charge=charge, res=res,
                         center=(c_re, c_im),
                         reLo=re_lo, reHi=re_hi, imLo=im_lo, imHi=im_hi,
                         chBar=ch_hi))

    charge_sum = sum(r["charge"] for r in rows)
    res_sum = sum(r["res"] for r in rows)
    s_re = sum(r["center"][0] for r in rows) * r3sq
    s_im = sum(r["center"][1] for r in rows) * r3sq
    total_scaled = r3sq * (charge_sum + res_sum) + edge_total
    worst = sorted(rows, key=lambda r: -(r["charge"] + r["res"]))[:8]

    # ---- frozen bar sums (exact rationals of the emitted literals) ----
    LO_re = sum(r["reLo"] for r in rows)
    HI_re = sum(r["reHi"] for r in rows)
    LO_im = sum(r["imLo"] for r in rows)
    HI_im = sum(r["imHi"] for r in rows)
    CBAR = sum(r["chBar"] for r in rows)
    assert LO_re <= sum(r["center"][0] for r in rows) <= HI_re
    assert LO_im <= sum(r["center"][1] for r in rows) <= HI_im
    assert CBAR >= charge_sum + res_sum
    scaled_lo_re = r3sq * LO_re
    scaled_hi_re = r3sq * HI_re
    scaled_lo_im = r3sq * LO_im
    scaled_hi_im = r3sq * HI_im
    scaled_cbar = r3sq * CBAR

    # ---- home rectangle: analyticMomentInterval2597_row_00 element 3 ----
    iv = S.read("C1RouteACorrectionAnalyticIntervals2597.lean")
    m = re.search(r"noncomputable def analyticMomentInterval2597_row_00"
                  r"[^\n]*?:=\s*!\[(.*)\n\s*\]\s*$", iv, re.S | re.M)
    if not m:
        m = re.search(r"noncomputable def analyticMomentInterval2597_row_00"
                      r"[^\n]*?:=\s*(!\[.*?\])\n", iv, re.S)
    fields = re.findall(
        r"(reLo|reHi|imLo|imHi) := \(\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)",
        m.group(1))
    assert len(fields) == 120, len(fields)
    quad = {f[0]: F(int(f[1]), int(f[2])) for f in fields[12:16]}
    re_lo, re_hi = quad["reLo"], quad["reHi"]
    im_lo, im_hi = quad["imLo"], quad["imHi"]
    re_ctr, im_ctr = (re_lo + re_hi) / 2, (im_lo + im_hi) / 2
    hw_re, hw_im = (re_hi - re_lo) / 2, (im_hi - im_lo) / 2

    print(f"r3^2 (multiplier) = {float(r3sq):.9e}")
    print(f"sum charge (exact, assembly)   = {float(charge_sum):.6e}")
    print(f"sum charge (exact, +3^n resid) = {float(charge_sum + res_sum):.6e}")
    print(f"ledger total (scaled + edge)   = {float(total_scaled):.6e}")
    print(f"Sigma centers (scaled): re {float(s_re):.9e}  im {float(s_im):.9e}")
    print(f"rect: ctr re {float(re_ctr):.9e} im {float(im_ctr):.9e}  "
          f"hw re {float(hw_re):.3e} im {float(hw_im):.3e}")
    ok = True
    for lbl, half, ctr, sig in (("re", hw_re, re_ctr, s_re),
                                ("im", hw_im, im_ctr, s_im)):
        d = abs(sig - ctr)
        margin = half - d
        ratio = margin / total_scaled
        ok = ok and ratio >= 1
        print(f"  {lbl}: |Sigma-ctr| = {float(d):.6e}  margin = "
              f"{float(margin):.6e}  margin/total = {float(ratio):.4f}"
              + ("" if ratio >= 1 else "   *** BELOW 1 ***"))
    # the strict-coordinate ledger the Lean assembly consumes: the certified
    # bar interval [r3sq*LO, r3sq*HI] must sit strictly inside the rectangle
    # after charging CBAR on ONE side per axis (the assembly subtracts the
    # charge from the nearer endpoint).
    for lbl, lo_b, hi_b, lo_r, hi_r in (
            ("re", scaled_lo_re, scaled_hi_re, re_lo, re_hi),
            ("im", scaled_lo_im, scaled_hi_im, im_lo, im_hi)):
        head_lo = lo_r - lo_b
        head_hi = hi_r - hi_b
        print(f"  {lbl} bar headroom: lo {float(head_lo):.6e} "
              f"hi {float(head_hi):.6e}")
    print("top ledger entries:")
    for r in worst:
        print(f"  P{r['tag']} n={r['n']:2d} charge={float(r['charge']):.3e} "
              f"res={float(r['res']):.3e}")
    # ---- strict-coordinate barriers (the four frozen Lean facts) ----
    # The assembly proves, per axis:
    #   Re(entry) >= r3sq * (LO_re - (CBAR + EBAR))
    #   Re(entry) <= r3sq * (HI_re + (CBAR + EBAR))
    # (per-panel: Re P_k >= c_re_k - chBar_k >= reLo_k - chBar_k and
    #  <= reHi_k + chBar_k; edges cost EBAR).  Membership in the rectangle
    # therefore follows from the four exact-rational barrier facts below,
    # which the generated Lean module replays with norm_num.
    EBAR = edge_total
    reBarLo = r3sq * (LO_re - (CBAR + EBAR))
    reBarHi = r3sq * (HI_re + (CBAR + EBAR))
    imBarLo = r3sq * (LO_im - (CBAR + EBAR))
    imBarHi = r3sq * (HI_im + (CBAR + EBAR))
    barriers = (
        ("reBarLo >= reLo", reBarLo >= re_lo),
        ("reBarHi <= reHi", reBarHi <= re_hi),
        ("imBarLo >= imLo", imBarLo >= im_lo),
        ("imBarHi <= imHi", imBarHi <= im_hi),
    )
    for nm, b in barriers:
        print(f"  barrier {nm}: {'OK' if b else '*** FAIL ***'}")
    ok = ok and all(b for _, b in barriers)
    print("VERDICT:", "LEDGER PASSES BOTH AXES" if ok else "LEDGER FAILS")

    out = dict(
        beta=str(beta), r3sq=str(r3sq),
        charge_sum=str(charge_sum), res_sum=str(res_sum),
        total_scaled=str(total_scaled), edge_total=str(edge_total),
        a0bar=str(a0bar),
        sigma_re=str(s_re), sigma_im=str(s_im),
        rect={kk: str(vv) for kk, vv in quad.items()},
        margin_re=str(hw_re - abs(s_re - re_ctr)),
        margin_im=str(hw_im - abs(s_im - im_ctr)),
        ratio_re=str((hw_re - abs(s_re - re_ctr)) / total_scaled),
        ratio_im=str((hw_im - abs(s_im - im_ctr)) / total_scaled),
        passes=ok,
        bar_sums=dict(LO_re=fstr(LO_re), HI_re=fstr(HI_re),
                      LO_im=fstr(LO_im), HI_im=fstr(HI_im), CBAR=fstr(CBAR)),
        barriers=dict(
            EBAR=fstr(EBAR),
            reBarLo=fstr(reBarLo), reBarHi=fstr(reBarHi),
            imBarLo=fstr(imBarLo), imBarHi=fstr(imBarHi),
            reLo=fstr(re_lo), reHi=fstr(re_hi),
            imLo=fstr(im_lo), imHi=fstr(im_hi),
            checks={nm: bool(b) for nm, b in barriers}),
        top=[dict(tag=r["tag"], n=r["n"], charge=str(r["charge"]),
                  res=str(r["res"])) for r in worst],
    )
    out_path = os.path.join(ROOT, "results", "2663_budget_recon.json")
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote results/2663_budget_recon.json")

    bars = dict(
        sigdig=SIGDIG, edge_pow2=EDGE_POW2,
        h=fstr(H),
        r3sq=fstr(r3sq),
        panels=[dict(tag=r["tag"], n=r["n"],
                     reLo=fstr(r["reLo"]), reHi=fstr(r["reHi"]),
                     imLo=fstr(r["imLo"]), imHi=fstr(r["imHi"]),
                     chBar=fstr(r["chBar"])) for r in rows],
        sums=dict(LO_re=fstr(LO_re), HI_re=fstr(HI_re),
                  LO_im=fstr(LO_im), HI_im=fstr(HI_im), CBAR=fstr(CBAR)),
    )
    bars_path = os.path.join(ROOT, "results", "2663_bars.json")
    with open(bars_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(bars, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote results/2663_bars.json")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())