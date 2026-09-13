#!/usr/bin/env python3
"""1390 component-5 discharge rig (route A, route-alpha register).

VERBATIM transcription of docs/proofs/1390_component5_route_A_prereg_v2.md.
Law 42: grids, formulas, bands, gates and the sentinel are locked by that
prereg; this script implements them and NOTHING ELSE.  Law 65: every number
this run prints is MODEL evidence about budget arithmetic on hypothetical
off-line geometry; no claim about actual zeta zeros, no RH inference either
way, and the archimedean gate is never evaluated (prereg section 0).
"""
import json
import math
import sys

import numpy as np

LOG2 = math.log(2.0)

# ---- locked grids (prereg section 2) ----
D_GRID = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45]
DELTA_GRID = [0.01, 0.03, 0.1, 0.3, 0.6, 1.0]
RADII = [0.02, 0.05, 0.08, 0.12, 0.1732]  # log(2)/4 truncated DOWN
EPS_GRID = [0.01, 0.1]
RERE_GRID = [0.55, 0.6, 0.75, 0.9, 0.99]
IMRI_GRID = [14.134725, 21.022040, 25.010858, 1054.0]
REF = dict(d=0.05, delta=0.1, Rf=0.08, Ru=0.08, eps=0.01, epsp=0.01,
           rere=0.75, imri=14.134725)

PASS_EDGE = 0.5  # PASS: ratio >= 1/2 ; MARGINAL: 0 < ratio < 1/2 ; FAIL: ratio <= 0

V_PATTERN = np.array([1.0, 1.0, 1.0, 1.0], dtype=complex)     # xi-side (u)
Y_PATTERN = np.array([0.0, 0.0, 0.0, -1.0], dtype=complex)    # taper (f)

RANK = {"PASS": 2, "MARGINAL": 1, "FAIL": 0}


def nodes(rere, imri):
    return np.array([0.0, 0.5, 1.0, complex(rere, imri)], dtype=complex)


def gram(R, s):
    """G_ij = int_-R^R exp((s_i + conj s_j) x) dx = 2 sinh(A R)/A, branch A=0 -> 2R.
    The zero-frequency branch IS hit: A_00 = 0 exactly (prereg 1.3)."""
    A = s[:, None] + s.conj()[None, :]
    G = np.empty((4, 4), dtype=complex)
    for i in range(4):
        for j in range(4):
            a = A[i, j]
            G[i, j] = 2.0 * R if a == 0 else 2.0 * np.sinh(a * R) / a
    return G


def kloc_with_diag(R, s, pattern):
    """Return (K_loc, |imag|, cond(G), rel-residual).  K_loc = z* G^-1 z is real."""
    G = gram(R, s)
    cond = float(np.linalg.cond(G))
    rhs = pattern
    x = np.linalg.solve(G, rhs)
    resid = float(np.linalg.norm(G @ x - rhs) / max(np.linalg.norm(rhs), 1e-300))
    val = np.vdot(rhs, x)  # conj(rhs) . x  ==  z* G^-1 z  (rhs=z here)
    return float(val.real), float(abs(val.imag)), cond, resid


def c_couplings(d, delta, Rg):
    C_C = (8.0 * math.pi * math.sinh(d * Rg) ** 2
           + 2.0 * delta ** 3 * Rg ** 3 * math.exp(2.0 * d * Rg))
    C_D = (2.0 * Rg * delta * (math.exp(d * Rg) - 1.0) ** 2
           + (4.0 / 3.0) * delta ** 3 * Rg ** 3)
    return C_C, C_D


def ratio_of(ceiling, C_min, delta):
    return 1.0 - 2.0 * C_min * ceiling / delta


def band(ratio):
    if ratio >= PASS_EDGE:
        return "PASS"
    if ratio > 0.0:
        return "MARGINAL"
    return "FAIL"


def main():
    # ---- precompute K_loc per (radius, rho, pattern) with diagnostics (G3 data) ----
    Kf, Ku, kdiag = {}, {}, {}
    for R in RADII:
        for rr in RERE_GRID:
            for im in IMRI_GRID:
                s = nodes(rr, im)
                kf, fi, cf, rf = kloc_with_diag(R, s, Y_PATTERN)
                ku, ui, cu, ru = kloc_with_diag(R, s, V_PATTERN)
                Kf[(R, rr, im)] = kf
                Ku[(R, rr, im)] = ku
                kdiag[(R, rr, im)] = dict(Kf=kf, Kf_imag=fi, Gf_cond=cf,
                                          Kf_resid=rf, Ku=ku, Ku_imag=ui,
                                          Gu_cond=cu, Ku_resid=ru)
    print(f"[pre] K_loc tables: {len(Kf)} entries each; "
          f"range Kf [{min(Kf.values()):.6g}, {max(Kf.values()):.6g}]  "
          f"Ku [{min(Ku.values()):.6g}, {max(Ku.values()):.6g}]", flush=True)

    # ---- per-cell sweep (96000 cells) ----
    cells = []
    counts = {"PASS": 0, "MARGINAL": 0, "FAIL": 0}
    g0_bad, g3_bad, g4_bad, g5_bad = [], [], [], []
    for d in D_GRID:
        for delta in DELTA_GRID:
            for Rf in RADII:
                for Ru in RADII:
                    Rg = Rf + Ru
                    if Rg > LOG2 / 2:  # G0 admissibility
                        g0_bad.append((d, delta, Rf, Ru))
                    if d * Rg > 0.53:  # G5 regime
                        g5_bad.append((d, delta, Rf, Ru))
                    C_C, C_D = c_couplings(d, delta, Rg)
                    C_min = min(C_C, C_D)
                    if C_min <= 0 or C_min > C_C + 1e-300 or C_min > C_D + 1e-300:
                        g4_bad.append((d, delta, Rf, Ru))
                    for eps in EPS_GRID:
                        for epsp in EPS_GRID:
                            for rr in RERE_GRID:
                                for im in IMRI_GRID:
                                    kf = Kf[(Rf, rr, im)]
                                    ku = Ku[(Ru, rr, im)]
                                    if kf <= 0.0 or ku <= 0.0:
                                        g3_bad.append((d, delta, Rf, Ru, rr, im))
                                    ceiling = (2.0 * Ru) * ((1.0 + epsp) * ku) \
                                        * ((1.0 + eps) * kf)
                                    if ceiling <= 0.0:
                                        g3_bad.append(("ceil", d, delta, Rf, Ru, rr, im))
                                    rat = ratio_of(ceiling, C_min, delta)
                                    b = band(rat)
                                    counts[b] += 1
                                    cells.append((d, delta, Rf, Ru, Rg, kf, ku,
                                                  ceiling, C_C, C_D, C_min, rat, b))
    # G3 invertibility/precision diagnostics
    for key, dg in kdiag.items():
        for c in (dg["Gf_cond"], dg["Gu_cond"]):
            if not (c < 1e12):
                g3_bad.append(("cond", key, c))
        for r in (dg["Kf_resid"], dg["Ku_resid"]):
            if not (r < 1e-7):
                g3_bad.append(("resid", key, r))
        if not (dg["Kf_imag"] < 1e-6 * max(1.0, abs(dg["Kf"]))):
            g3_bad.append(("imag", key, dg["Kf_imag"]))
        if not (dg["Ku_imag"] < 1e-6 * max(1.0, abs(dg["Ku"]))):
            g3_bad.append(("imag", key, dg["Ku_imag"]))

    n = len(cells)
    print(f"[sweep] cells={n}  PASS={counts['PASS']}  MARGINAL={counts['MARGINAL']}  "
          f"FAIL={counts['FAIL']}", flush=True)

    # ---- reference cell ----
    def evaluate(d, delta, Rf, Ru, eps, epsp, rere, imri, kf_scale=1.0):
        Rg = Rf + Ru
        C_C, C_D = c_couplings(d, delta, Rg)
        C_min = min(C_C, C_D)
        kf = kf_scale * Kf[(Rf, rere, imri)]
        ku = Ku[(Ru, rere, imri)]
        ceiling = (2.0 * Ru) * ((1.0 + epsp) * ku) * ((1.0 + eps) * kf)
        rat = ratio_of(ceiling, C_min, delta)
        return dict(Rg=Rg, Kf=kf, Ku=ku, ceiling=ceiling, C_C=C_C, C_D=C_D,
                    C_min=C_min, ratio=rat, band=band(rat))

    ref = evaluate(**REF)
    ref10 = evaluate(**REF, kf_scale=10.0)
    print(f"[ref]  ratio={ref['ratio']:.10g} band={ref['band']}  "
          f"ceiling={ref['ceiling']:.6g}  C_min={ref['C_min']:.6g}", flush=True)
    print(f"[ref]  x10-inflation: ratio={ref10['ratio']:.10g} band={ref10['band']}",
          flush=True)

    # ---- gates ----
    gates = {}

    # G0: admissibility across the WHOLE grid (radii + d*Rg <= 0.15588).
    g0_maxsum = max(Rf + Ru for Rf in RADII for Ru in RADII)
    g0_maxdr = max(d * (Rf + Ru) for d in D_GRID for Rf in RADII for Ru in RADII)
    gates["G0"] = dict(
        status="PASS" if (g0_maxsum <= LOG2 / 2 and g0_maxdr <= 0.15588 + 1e-12
                          and not g0_bad) else "FAIL",
        max_Rf_plus_Ru=g0_maxsum, log2_half=LOG2 / 2,
        max_d_Rg=g0_maxdr, cap=0.15588, n_violations=len(g0_bad))

    # G1: negative control — reference band must DROP under x10 K_loc_f.
    g1_ok = RANK[ref10["band"]] < RANK[ref["band"]]
    gates["G1"] = dict(
        status="PASS" if g1_ok else "FAIL",
        ref_ratio=ref["ratio"], ref_band=ref["band"],
        inflated_ratio=ref10["ratio"], inflated_band=ref10["band"],
        shortfall_before=1.0 - ref["ratio"], shortfall_after=1.0 - ref10["ratio"])

    # G2: pure formula calculus on the locked closed forms.
    rg_sweep = np.linspace(0.04, LOG2 / 2, 40)
    cmin_Rg = [min(c_couplings(0.05, 0.1, float(r))) for r in rg_sweep]
    d_sweep = np.linspace(1e-4, 0.45, 40)
    cmin_d = [min(c_couplings(float(dv), 0.1, 0.16)) for dv in d_sweep]
    dl_sweep = np.linspace(1e-3, 1.0, 40)
    cmin_delta = [min(c_couplings(0.05, float(dl), 0.16)) for dl in dl_sweep]
    ceils = np.linspace(0.05, 5.0, 40)
    r_at_cm = [ratio_of(c, 0.3, 0.1) for c in ceils]
    cms = np.linspace(0.01, 1.0, 40)
    r_at_ce = [ratio_of(2.0, m, 0.1) for m in cms]
    g2_ok = (all(b > a for a, b in zip(cmin_Rg, cmin_Rg[1:]))
             and all(b > a for a, b in zip(cmin_d, cmin_d[1:]))
             and all(b > a for a, b in zip(cmin_delta, cmin_delta[1:]))
             and all(b < a for a, b in zip(r_at_cm, r_at_cm[1:]))
             and all(b < a for a, b in zip(r_at_ce, r_at_ce[1:])))
    gates["G2"] = dict(status="PASS" if g2_ok else "FAIL",
                       cmin_increasing_Rg=True, note="strict sweep checks on "
                       "the locked closed forms; see per-diff below")
    gates["G2"]["diffs"] = dict(
        cmin_Rg_min_step=float(min(np.diff(cmin_Rg))),
        cmin_d_min_step=float(min(np.diff(cmin_d))),
        cmin_delta_min_step=float(min(np.diff(cmin_delta))))

    # G3: positivity + invertibility/precision of every Gram used.
    gates["G3"] = dict(status="PASS" if not g3_bad else "FAIL",
                       n_violations=len(g3_bad),
                       examples=[str(v) for v in g3_bad[:8]],
                       cond_max=float(max(max(dg["Gf_cond"], dg["Gu_cond"])
                                          for dg in kdiag.values())),
                       resid_max=float(max(max(dg["Kf_resid"], dg["Ku_resid"])
                                           for dg in kdiag.values())))

    # G4: C_min = min by construction + small-d limit (prereg 1.6) at d=1e-3.
    # Limits checked at the prereg reference geometry (Rg=0.16, delta=0.1); the
    # universal branch is the C_D < C_C attainment claim over all radius/delta.
    dT = 1e-3
    CC_T, CD_T = c_couplings(dT, 0.1, 0.16)
    lim_CC = 8.0 * math.pi * dT ** 2 * 0.16 ** 2 + 2.0 * 0.1 ** 3 * 0.16 ** 3
    lim_CD = (4.0 / 3.0) * 0.1 ** 3 * 0.16 ** 3
    a_ok = abs(CC_T - lim_CC) <= 0.01 * CC_T
    b_ok = abs(CD_T - lim_CD) <= 0.01 * CD_T
    c_ok = all(c_couplings(dT, dl, rg)[1] < c_couplings(dT, dl, rg)[0]
               for dl in DELTA_GRID
               for rg in sorted({rf + ru for rf in RADII for ru in RADII}))
    gates["G4"] = dict(status="PASS" if (a_ok and b_ok and c_ok and not g4_bad)
                       else "FAIL",
                       C_C_at_d1e3=CC_T, C_C_limit=lim_CC, rel_err_C=abs(CC_T - lim_CC) / CC_T,
                       C_D_at_d1e3=CD_T, C_D_limit=lim_CD, rel_err_D=abs(CD_T - lim_CD) / CD_T,
                       CD_attains_at_small_d=bool(c_ok), n_violations=len(g4_bad))

    # G5: regime assertion — zero cells with d*Rg > 0.53.
    gates["G5"] = dict(status="PASS" if not g5_bad else "FAIL",
                       n_violations=len(g5_bad), max_d_Rg=g0_maxdr)

    # G6: window balance — informational, NO verdict weight (prereg 3, 3.6).
    balance = {}
    for Ru in RADII:
        for rr in RERE_GRID:
            for im in IMRI_GRID:
                best = None
                for Rf in RADII:
                    e = evaluate(REF["d"], REF["delta"], Rf, Ru, REF["eps"],
                                 REF["epsp"], rr, im)
                    obj = e["C_min"] * e["ceiling"]
                    if best is None or obj < best[1]:
                        best = (Rf, obj, e["ratio"], e["band"])
                balance[f"{Ru}|{rr}+{im}i"] = dict(Rf_star=best[0],
                                                   objective=best[1],
                                                   ratio=best[2], band=best[3])
    gates["G6"] = dict(status="REPORTED (no verdict weight)",
                       n=len(balance), table=balance)

    # ---- frontier / seam tables ----
    frontier = {}  # per (d, Rg): largest delta with PASS (any split/eps/rho)
    seam = {}      # per (delta, Rg): largest d with FAIL (any ...)
    for row in cells:
        d, delta, Rf, Ru, Rg, kf, ku, ceil, C_C, C_D, C_min, rat, b = row
        k = (d, round(Rg, 6))
        if b == "PASS":
            cur = frontier.get(k)
            if cur is None or delta > cur:
                frontier[k] = delta
        if b == "FAIL":
            kk = (delta, round(Rg, 6))
            cur = seam.get(kk)
            if cur is None or d > cur:
                seam[kk] = d
    print("[frontier] per (d, Rg) largest-PASS-delta (NONE = no PASS):", flush=True)
    for k in sorted(frontier):
        print(f"  d={k[0]}  Rg={k[1]}  delta*={frontier[k]}", flush=True)
    print(f"[seam] (delta, Rg) largest-FAIL-d table entries={len(seam)}", flush=True)
    for k in sorted(seam):
        print(f"  delta={k[0]}  Rg={k[1]}  d_failmax={seam[k]}", flush=True)

    # ---- outputs ----
    best = max(cells, key=lambda r: r[11])
    worst = min(cells, key=lambda r: r[11])
    summary = dict(
        prereg="1390 v2", law65="MODEL only", n_cells=n, counts=counts,
        reference=dict(**{k: REF[k] for k in REF},
                       **{k: ref[k] for k in ("Rg", "Kf", "Ku", "ceiling", "C_C",
                                              "C_D", "C_min", "ratio", "band")}),
        reference_x10=dict(ratio=ref10["ratio"], band=ref10["band"]),
        best_cell=dict(d=best[0], delta=best[1], Rf=best[2], Ru=best[3],
                       ratio=best[11], band=best[12]),
        worst_cell=dict(d=worst[0], delta=worst[1], Rf=worst[2], Ru=worst[3],
                        ratio=worst[11], band=worst[12]),
        frontier={f"{k[0]}|{k[1]}": v for k, v in sorted(frontier.items())},
        seam={f"{k[0]}|{k[1]}": v for k, v in sorted(seam.items())},
        gates=gates)
    with open("docs/proofs/1390_component5_rig_results.json", "w") as f:
        json.dump(summary, f, indent=1, default=str)
    with open("docs/proofs/1390_component5_rig_cells.tsv", "w") as f:
        f.write("d\tdelta\tRf\tRu\tRg\tK_loc_f\tK_loc_u\tceiling\tC_C\tC_D\tC_min\tratio\tband\n")
        for row in cells:
            d, delta, Rf, Ru, Rg, kf, ku, ceil, C_C, C_D, C_min, rat, b = row
            f.write(f"{d}\t{delta}\t{Rf}\t{Ru}\t{Rg:.6f}\t{kf:.10g}\t{ku:.10g}\t"
                    f"{ceil:.10g}\t{C_C:.10g}\t{C_D:.10g}\t{C_min:.10g}\t{rat:.10g}\t{b}\n")

    # ---- sentinel (prereg section 4: literal DONE line, FAIL entries name gates) ----
    parts = ",".join(f"{k}:{'PASS' if gates[k]['status'] == 'PASS' else 'FAIL'}"
                     for k in ("G0", "G1", "G2", "G3", "G4", "G5"))
    print(f"DONE gates={parts}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
