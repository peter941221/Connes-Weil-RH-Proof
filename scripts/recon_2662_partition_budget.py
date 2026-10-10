#!/usr/bin/env python3
"""Record-2662 direction recon: exact-rational partition budget for entry (0,3).

Re-derives, from the COMMITTED Lean literals (no float display text), the
per-panel charge accounting of the entry (0,3) partition and the containment
margin against `analyticMomentInterval2597_row_03` element 3.  Also settles
the direction of the record-2657 `supArg` vacuous-channel pins in exact
arithmetic.  Recon only: no Lean claim, no certificate; the Lean brick
re-proves what it consumes.

Run:  python scripts/recon_2662_partition_budget.py
Out:  results/2662_partition_budget_recon.json
"""

import json
import math
import os
import re
import sys
from fractions import Fraction as F

sys.set_int_max_str_digits(200000)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "ConnesWeilRH", "Dev")

RAT_ASCRIBED = re.compile(r"\(\s*(-?\d+)\s*:\s*[ℚℝ]\s*\)\s*/\s*(\d+)")
RAT_PLAIN = re.compile(r"(-?\d+)\s*/\s*(\d+)")


def read(name):
    with open(os.path.join(DEV, name), encoding="utf-8") as fh:
        return fh.read()


def exists(name):
    return os.path.exists(os.path.join(DEV, name))


def def_body(text, name):
    """Body of a `def NAME ... := BODY`, up to the next declaration."""
    m = re.search(
        r"^(?:noncomputable )?def " + re.escape(name)
        + r"\b[^\n]*?:=\s*(.*?)(?=\n\s*\n|\n/--|\n(?:noncomputable )?def "
        r"|\ntheorem |\n#print )", text, re.M | re.S)
    if not m:
        raise KeyError(name)
    return m.group(1)


def body_rats(body):
    """All rational literals of a def body, in order."""
    out = [F(int(a), int(b)) for a, b in RAT_ASCRIBED.findall(body)]
    if not out:
        out = [F(int(a), int(b)) for a, b in RAT_PLAIN.findall(body)]
    return out


def has_def(text, name):
    return re.search(r"^(?:noncomputable )?def " + re.escape(name) + r"\b",
                     text, re.M) is not None


def rats(text, name):
    return body_rats(def_body(text, name))


def pair(text, name):
    r = rats(text, name)
    if len(r) < 2:
        raise ValueError(f"{name}: expected a rational pair, got {r}")
    return (r[0], r[1])


VAR_STRICT = re.compile(
    r"Real\.exp \(2 \* \(\((\d+)\s*/\s*(\d+)\)\s*:\s*[ℝℚ]\)\)")
VAR_PLAIN = re.compile(r"Real\.exp \((\d+)\s*/\s*(\d+)\)")


def var_of(text):
    """The exp ARGUMENT literal printed in the certificate (`2 * (N/D)` or
    a plain `N/D` spelling)."""
    vals = [2 * F(int(a), int(b)) for a, b in VAR_STRICT.findall(text)]
    vals += [F(int(a), int(b)) for a, b in VAR_PLAIN.findall(text)]
    if not vals:
        raise ValueError("no VAR literal")
    if any(v != vals[0] for v in vals):
        raise ValueError(f"VAR literals disagree: {vals}")
    return vals[0]


def main():
    tag = lambda k: f"{k:03d}"  # noqa: E731

    # ---- entry-level parameters from the capture (record 2584 / 2661) ----
    p2661 = read("C1RouteAPanelCenterNormalization2661P095.lean")
    node = pair(p2661, "nodeEntry0_2661")
    theta = rats(p2661, "modulationEntry3_2661")[0]
    width3 = rats(p2661, "widthEntry3_2661")[0]
    r3sq = width3 * width3
    coeff = (node[0] * r3sq, (node[1] + theta) * r3sq)

    # ---- table coefficients (record 2655) and the independent tie ----
    t095 = read("C1RouteAComplexPanelTable2655P095.lean")
    beta = rats(t095, "complexPanelBeta2648P095")[0]
    psi = rats(t095, "complexPanelPsi2648P095")[0]
    assert coeff == (beta, psi), f"tie mismatch: {coeff} vs {(beta, psi)}"
    t094 = read("C1RouteAComplexPanelTable2655P094.lean")
    assert rats(t094, "complexPanelBeta2648P094")[0] == beta
    assert rats(t094, "complexPanelPsi2648P094")[0] == psi

    H = F(1, 200)
    center = lambda k: F(-19, 20) + F(2 * k + 1, 200)  # noqa: E731

    # ---- per-panel parse ----
    panels = []
    for k in range(190):
        tg = tag(k)
        amp = read(f"C1RouteAAmpPin2657P{tg}.lean")
        ph = read(f"C1RouteAPhasePin2658P{tg}.lean")
        tb_name = f"C1RouteAComplexPanelTable2655P{tg}.lean"
        if not exists(tb_name):
            tb_name = f"C1RouteAComplexPanelTable2648P{tg}.lean"
        tb = read(tb_name)
        an = read((f"C1RouteAComplexPanelAnalytic2649P109.lean" if k == 109
                   else f"C1RouteAComplexPanelAnalytic2656P{tg}.lean"))
        c = center(k)
        assert rats(tb, f"complexPanelCenter2648P{tg}")[0] == c
        amp_arg = rats(amp, f"ampArg2657P{tg}")[0]
        amp_val = rats(amp, f"ampValue2657P{tg}")[0]
        amp_rad = rats(amp, f"ampRadius2657P{tg}")[0]
        ph_arg = rats(ph, f"phaseArg2658P{tg}")[0]
        ph_val = pair(ph, f"phaseValue2658P{tg}")
        ph_rad = rats(ph, f"phaseRadius2658P{tg}")[0]
        integral = pair(tb, f"complexPanelIntegral2648P{tg}")
        ru = rats(tb, f"complexPanelResidualUpper2648P{tg}")[0]
        var = var_of(an)
        # exact convention checks against the entry parameters
        assert amp_arg == beta * c - 30 / (1 - c * c), tg
        assert ph_arg == psi * c, tg
        panels.append(dict(k=k, c=c, amp_arg=amp_arg, amp_val=amp_val,
                           amp_rad=amp_rad, ph_arg=ph_arg, ph_val=ph_val,
                           ph_rad=ph_rad, integral=integral, ru=ru, var=var,
                           has_sup=has_def(amp, f"supArg2657P{tg}")))

    # committed classification: the 46 sup pins mark the vacuous channel
    vac46 = [p for p in panels if p["has_sup"]]
    normal = [p for p in panels if not p["has_sup"]]
    var_ge1 = [p["k"] for p in panels if p["var"] / 2 >= 1]
    print(f"panels: {len(panels)}  normal {len(normal)}  sup-46 "
          f"{len(vac46)}")
    print("sup-46 k:", [p["k"] for p in vac46])
    print(f"var>=1 set ({len(var_ge1)}) matches sup-46: "
          f"{sorted(var_ge1) == [p['k'] for p in vac46]}")

    def mag(pair_):
        return abs(pair_[0]) + abs(pair_[1])

    def charge2659(p):
        m1 = mag(p["ph_val"])
        m2 = mag(p["integral"])
        return (p["amp_rad"] * (m1 + 2 * p["ph_rad"]) * m2
                + (p["amp_val"] + p["amp_rad"]) * 2 * p["ph_rad"] * m2)

    def rescharge(p):
        deficit = 1 - (abs(p["c"]) + H) ** 2
        r = math.exp(float(p["var"])) * float(p["ru"]) / float(deficit**2) \
            * float(2 * H * H)
        return float(p["amp_val"] + p["amp_rad"]) * 2 * r

    def pair_mul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def pair_scale(s, a):
        return (s * a[0], s * a[1])

    for p in panels:
        ctr = pair_scale(p["amp_val"], pair_mul(p["ph_val"], p["integral"]))
        ctr = pair_scale(r3sq, ctr)
        p["center"] = ctr
        p["charge"] = charge2659(p)
        p["resc"] = rescharge(p)

    s_all = [sum((p["center"][0] for p in panels), F(0)),
             sum((p["center"][1] for p in panels), F(0))]
    s_144 = [sum((p["center"][0] for p in normal), F(0)),
             sum((p["center"][1] for p in normal), F(0))]
    tot_all = sum(p["charge"] + p["resc"] for p in panels)
    tot_144 = sum(p["charge"] + p["resc"] for p in normal)

    print(f"\nSigma(center) all-190 : {float(s_all[0]):.9e}, "
          f"{float(s_all[1]):.9e}")
    print(f"Sigma(center) normal-144 : {float(s_144[0]):.9e}, "
          f"{float(s_144[1]):.9e}")
    print(f"total charge all-190 (2659+res): {tot_all:.6e}")
    print(f"total charge normal-144        : {tot_144:.6e}")
    print(f"sum(resc) all-190: {sum(p['resc'] for p in panels):.6e}")

    # ---- sample panels ----
    print("\nsample panels (ampV, |integral|, |center|, charge, res):")
    byk = {p["k"]: p for p in panels}
    for k in (0, 22, 23, 34, 35, 46, 95, 109, 154, 155, 166, 189):
        p = byk[k]
        v = p["center"]
        print(f"  k={k:3d} c={float(p['c']):+.3f} ampV={float(p['amp_val']):.3e} "
              f"|int|={mag(p['integral']):.3e} |ctr|={mag(v):.3e} "
              f"charge={p['charge']:.3e} res={p['resc']:.3e} "
              f"var={float(p['var']):.3f}")

    # ---- vacuous channel: committed vs corrected sup ----
    def sup_committed(p):
        return beta * H + 30 / (1 - p["c"] ** 2) \
            - 30 / (1 - (abs(p["c"]) + H) ** 2)

    def sup_corrected(p):
        return beta * H + 30 / (1 - p["c"] ** 2) \
            - 30 / (1 - (abs(p["c"]) - H) ** 2)

    vac_rows = []
    for p in vac46[:: max(1, len(vac46) // 8)]:
        sc, sr = sup_committed(p), sup_corrected(p)
        amp_txt = read(f"C1RouteAAmpPin2657P{tag(p['k'])}.lean")
        sa = rats(amp_txt, f"supArg2657P{tag(p['k'])}")[0]
        vac_rows.append(dict(k=p["k"], sup_arg_committed=str(sa),
                             committed_value=f"{float(sc):.6f}",
                             corrected_value=f"{float(sr):.6f}",
                             committed_matches_committed_formula=(sa == sc),
                             ratio=f"{math.exp(float(sr) - float(sc)):.3e}"))
    vac_charge_corrected = sum(
        float(p["amp_val"] + p["amp_rad"]) * float(2 * H)
        * math.exp(float(sup_corrected(p))) for p in vac46)
    print("\nsup-channel exhibit (committed vs corrected):")
    for row in vac_rows:
        print("  ", row)
    print(f"vacuous corrected bound total (46): {vac_charge_corrected:.6e}")

    # ---- edge slices [0.95, 1] and [-1, -0.95] ----
    edge = 0.0
    for sgn in (1, -1):
        u = F(sgn) * F(19, 20)
        re_f = float(beta * u - 30 / (1 - u * u))
        edge += 0.05 * math.exp(re_f)
    print(f"\nedge charge (monotone bound): {edge:.6e}")

    # ---- the 2597 rectangle (entry (0,3) home: row_00 element 3,
    # value-verified by the 900-rect scan) ----
    iv = read("C1RouteACorrectionAnalyticIntervals2597.lean")
    m = re.search(r"noncomputable def analyticMomentInterval2597_row_00"
                  r"[^\n]*?:=\s*!\[(.+?)\]\n", iv, re.S)
    if m is None:
        raise ValueError("row_03 literal not found")
    fields = re.findall(
        r"(reLo|reHi|imLo|imHi) := \(\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)",
        m.group(1))
    assert len(fields) == 120, len(fields)
    rect = {}
    for idx in range(30):
        quad = fields[4 * idx:4 * idx + 4]
        if idx == 3:
            rect = {f[0]: F(int(f[1]), int(f[2])) for f in quad}
    re_lo, re_hi = rect["reLo"], rect["reHi"]
    im_lo, im_hi = rect["imLo"], rect["imHi"]
    re_ctr = float(re_lo + re_hi) / 2
    im_ctr = float(im_lo + im_hi) / 2
    half_re = float(re_hi - re_lo) / 2
    half_im = float(im_hi - im_lo) / 2
    print(f"\nrow_00 elem3 rect: re in [{float(re_lo):.6e}, "
          f"{float(re_hi):.6e}]  im in [{float(im_lo):.6e}, "
          f"{float(im_hi):.6e}]")
    print(f"rect center {re_ctr:.9e}, {im_ctr:.9e}  "
          f"half-width re {half_re:.3e} im {half_im:.3e}")
    for lbl, s in (("all190", s_all), ("normal144", s_144)):
        d_re = abs(float(s[0]) - re_ctr)
        d_im = abs(float(s[1]) - im_ctr)
        print(f"  |Sigma - center| ({lbl}): re {d_re:.3e}  im {d_im:.3e}")
    for lbl, s, tot in (("all190", s_all, tot_all),
                        ("normal144", s_144, tot_144)):
        for axis, marg in (("re", half_re), ("im", half_im)):
            c0 = re_ctr if axis == "re" else im_ctr
            d = abs(float(s[0] if axis == "re" else s[1]) - c0)
            print(f"  {lbl} {axis}: margin after |Sigma-ctr| = "
                  f"{marg - d:.6e}  ratio to charge = "
                  f"{(marg - d) / tot:.3e}")

    out = dict(
        entry_params=dict(beta=str(beta), psi=str(psi), r3sq=str(r3sq)),
        counts=dict(total=len(panels), normal144=len(normal),
                    sup46=len(vac46)),
        sup_k=[p["k"] for p in vac46],
        sup_exhibit=vac_rows,
        sigma_all190=[str(s_all[0]), str(s_all[1])],
        sigma_normal144=[str(s_144[0]), str(s_144[1])],
        total_charge_all190=tot_all,
        total_charge_normal144=tot_144,
        vacuous_bound_corrected=vac_charge_corrected,
        resc_sum=sum(p["resc"] for p in panels),
        edge_charge=edge,
        rect_elem3={k: str(v) for k, v in rect.items()},
        margin=dict(
            all190=dict(re=half_re - abs(float(s_all[0]) - re_ctr),
                        im=half_im - abs(float(s_all[1]) - im_ctr),
                        tot=tot_all),
            normal144=dict(re=half_re - abs(float(s_144[0]) - re_ctr),
                           im=half_im - abs(float(s_144[1]) - im_ctr),
                           tot=tot_144)),
        top_charge=[dict(k=p["k"], charge=f"{p['charge']:.3e}",
                         res=f"{p['resc']:.3e}")
                    for p in sorted(panels,
                                    key=lambda p: -(p["charge"]
                                                    + p["resc"]))[:8]],
    )
    os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
    with open(os.path.join(ROOT, "results", "2662_partition_budget_recon.json"),
              "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("\ntop per-panel charges (charge2659, rescharge):")
    for row in out["top_charge"]:
        print("  ", row)
    print("\nwrote results/2662_partition_budget_recon.json")


if __name__ == "__main__":
    sys.exit(main())