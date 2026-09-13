#!/usr/bin/env python3
"""1393 component-5 discharge rig, v3 (route A, route-alpha register).

VERBATIM transcription of docs/proofs/1393_component5_route_A_prereg_v3_instrument_fix.md:
model sections re-lock 1390 verbatim; the two revisions are G1 (band-universal
negative control: shortfall x10 identity) and G3 (locked precision class:
mpmath 200-bit = ~60 dps everywhere).  Law 42: grids, formulas, bands, gates
and the sentinel are locked by that prereg and this script implements NOTHING
ELSE.  Law 65: every number printed is MODEL evidence; the archimedean gate
is never evaluated (prereg section 0).
"""
import json
import math
import sys
from itertools import product

import mpmath as mp

mp.mp.prec = 200  # ~60 decimal digits (prereg 3-G3 precision class)

LOG2 = mp.mpf(math.log(2.0))          # exact conversion of the double is fine:
                                     # prereg formula uses the real log(2);
                                     # 200-bit context carries it to 1e-60.
LOG2_HALF = mp.log(2) / 2             # mp-accurate log(2)/2 (used for G0)

D_GRID = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45]
DELTA_GRID = [0.01, 0.03, 0.1, 0.3, 0.6, 1.0]
RADII = [0.02, 0.05, 0.08, 0.12, 0.1732]
EPS_GRID = [0.01, 0.1]
RERE_GRID = [0.55, 0.6, 0.75, 0.9, 0.99]
IMRI_GRID = [14.134725, 21.022040, 25.010858, 1054.0]
REF = dict(d=mp.mpf("0.05"), delta=mp.mpf("0.1"), Rf=mp.mpf("0.08"),
           Ru=mp.mpf("0.08"), eps=mp.mpf("0.01"), epsp=mp.mpf("0.01"),
           rere=mp.mpf("0.75"), imri=mp.mpf("14.134725"))

HALF = mp.mpf("0.5")
ZERO = mp.mpf("0")
TIE = mp.mpf("1e-30")      # prereg G3 tie-report window (not a band rule)
RES_TOL = mp.mpf("1e-30")  # prereg G3 solve-residual class
IMAG_TOL = mp.mpf("1e-30")  # prereg G3 |Im K| class
G1_TOL = mp.mpf("1e-9")     # prereg G1 shortfall identity tolerance

V_PATTERN = [mp.mpf(1), mp.mpf(1), mp.mpf(1), mp.mpf(1)]
Y_PATTERN = [mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(-1)]

RANK = {"PASS": 2, "MARGINAL": 1, "FAIL": 0}


def nodes(rere, imri):
    return [mp.mpf(0), mp.mpf("0.5"), mp.mpf(1),
            mp.mpc(rere, imri)]


def gram(R, s):
    """G_ij = 2*sinh(A*R)/A with A = s_i + conj(s_j); branch A == 0 -> 2R."""
    G = mp.zeros(4, 4)
    for i in range(4):
        for j in range(4):
            a = s[i] + mp.conj(s[j])
            G[i, j] = 2 * R if a == 0 else 2 * mp.sinh(a * R) / a
    return G


def kloc_with_diag(R, s, pattern):
    """K_loc = z* G^-1 z at locked precision. Returns (K, |Im|, residual)."""
    G = gram(R, s)
    # NOTE: mp.matrix(4, 1, list) treats the third argument as a callable,
    # NOT as entries (the v3 invocation-1 zero-fill bug).  Build via nested
    # single-column lists.
    z = mp.matrix([[v] for v in pattern])
    x = mp.lu_solve(G, z)
    resid = mp.norm(G * x - z, mp.inf) / max(mp.norm(z, mp.inf), mp.mpf(10) ** (-1000))
    val = sum(mp.conj(z[k, 0]) * x[k, 0] for k in range(4))
    return val.real, abs(val.imag), resid


def c_couplings(d, delta, Rg):
    C_C = (8 * mp.pi * mp.sinh(d * Rg) ** 2
           + 2 * delta ** 3 * Rg ** 3 * mp.exp(2 * d * Rg))
    C_D = (2 * Rg * delta * (mp.exp(d * Rg) - 1) ** 2
           + mp.mpf(4) / 3 * delta ** 3 * Rg ** 3)
    return C_C, C_D


def band_of(rat):
    if rat >= HALF:
        return "PASS"
    if rat > ZERO:
        return "MARGINAL"
    return "FAIL"


def main():
    M = mp.mpf
    # ---- K_loc tables at locked precision (G3 data + diagnostics) ----
    Kf, Ku, g3_bad, ties_note = {}, {}, [], None
    min_K = None
    for R in map(M, (str(r) for r in RADII)):
        for rr, im in product(RERE_GRID, IMRI_GRID):
            s = nodes(M(str(rr)), M(str(im)))
            for pat, tab, tag in ((Y_PATTERN, Kf, "f"), (V_PATTERN, Ku, "u")):
                val, imag, resid = kloc_with_diag(R, s, pat)
                if not (resid <= RES_TOL):
                    g3_bad.append(("resid", str(R), rr, im, tag, mp.nstr(resid, 6)))
                if not (imag <= IMAG_TOL):
                    g3_bad.append(("imag", str(R), rr, im, tag, mp.nstr(imag, 6)))
                if not (val > 0):
                    g3_bad.append(("pos", str(R), rr, im, tag, mp.nstr(val, 6)))
                if min_K is None or val < min_K:
                    min_K = val
                tab[(float(R), rr, im)] = val
    print(f"[pre] K tables: {len(Kf)} each; min K_loc = {mp.nstr(min_K, 10)}; "
          f"Kf range [{mp.nstr(min(Kf.values()), 6)}, "
          f"{mp.nstr(max(Kf.values()), 6)}]  "
          f"Ku range [{mp.nstr(min(Ku.values()), 6)}, "
          f"{mp.nstr(max(Ku.values()), 6)}]", flush=True)

    # ---- ceiling cache (d/delta-free): 25 radii x 4 eps x 20 rho = 20000 ----
    ceilings = {}
    for Rf, Ru in product(RADII, RADII):
        for eps, epsp in product(EPS_GRID, EPS_GRID):
            for rr in RERE_GRID:
                for im in IMRI_GRID:
                    k_f = Kf[(Rf, rr, im)]
                    k_u = Ku[(Ru, rr, im)]
                    c = (2 * M(str(Ru)) * ((1 + M(str(epsp))) * k_u)
                         * ((1 + M(str(eps))) * k_f))
                    ceilings[(Rf, Ru, eps, epsp, rr, im)] = c
    print(f"[pre] ceiling cache: {len(ceilings)} entries", flush=True)

    # ---- per-cell sweep, banding in mpf (96000 cells) ----
    cells = []
    counts = {"PASS": 0, "MARGINAL": 0, "FAIL": 0}
    g0_bad, g3b_bad, g4_bad, g5_bad = [], [], [], []
    tie_cells = []
    for d in D_GRID:
        dm = M(str(d))
        for delta in DELTA_GRID:
            dl = M(str(delta))
            for Rf, Ru in product(RADII, RADII):
                Rg = M(str(Rf)) + M(str(Ru))
                if Rg > LOG2_HALF:
                    g0_bad.append((d, delta, Rf, Ru))
                if dm * Rg > M("0.53"):
                    g5_bad.append((d, delta, Rf, Ru))
                C_C, C_D = c_couplings(dm, dl, Rg)
                C_min = min(C_C, C_D)
                if not (C_min > 0 and C_min <= C_C and C_min <= C_D):
                    g4_bad.append((d, delta, Rf, Ru))
                for eps, epsp in product(EPS_GRID, EPS_GRID):
                    for rr in RERE_GRID:
                        for im in IMRI_GRID:
                            ceiling = ceilings[(Rf, Ru, eps, epsp, rr, im)]
                            if not (ceiling > 0):
                                g3b_bad.append(("ceil", d, delta, Rf, Ru, rr, im))
                            rat = 1 - 2 * C_min * ceiling / dl
                            b = band_of(rat)
                            counts[b] += 1
                            if abs(rat - HALF) <= TIE or abs(rat) <= TIE:
                                tie_cells.append((d, delta, Rf, Ru, rr, im,
                                                  mp.nstr(rat, 12)))
                            cells.append((d, delta, Rf, Ru, float(Rg),
                                          mp.nstr(Kf[(Rf, rr, im)], 10),
                                          mp.nstr(Ku[(Ru, rr, im)], 10),
                                          mp.nstr(ceiling, 10),
                                          mp.nstr(C_C, 10), mp.nstr(C_D, 10),
                                          mp.nstr(C_min, 10), mp.nstr(rat, 10),
                                          b))
    print(f"[sweep] cells={len(cells)}  PASS={counts['PASS']}  "
          f"MARGINAL={counts['MARGINAL']}  FAIL={counts['FAIL']}  "
          f"tie-cells={len(tie_cells)}", flush=True)

    # ---- reference + negative control (G1 v3) ----
    def evaluate(d, delta, Rf, Ru, eps, epsp, rere, imri, kf_scale=1):
        Rg = Rf + Ru
        C_C, C_D = c_couplings(d, delta, Rg)
        C_min = min(C_C, C_D)
        k_f = kf_scale * Kf[(float(Rf), float(rere), float(imri))]
        k_u = Ku[(float(Ru), float(rere), float(imri))]
        ceiling = 2 * Ru * ((1 + epsp) * k_u) * ((1 + eps) * k_f)
        rat = 1 - 2 * C_min * ceiling / delta
        return dict(Rg=Rg, ceiling=ceiling, C_C=C_C, C_D=C_D, C_min=C_min,
                    ratio=rat, band=band_of(rat))

    ref = evaluate(**REF)
    ref10 = evaluate(**REF, kf_scale=10)
    s_before = 1 - ref["ratio"]
    s_after = 1 - ref10["ratio"]
    print(f"[ref]  ratio={mp.nstr(ref['ratio'], 12)} band={ref['band']}  "
          f"ceiling={mp.nstr(ref['ceiling'], 10)}  C_min={mp.nstr(ref['C_min'], 10)}",
          flush=True)
    print(f"[ref]  x10: ratio={mp.nstr(ref10['ratio'], 12)} band={ref10['band']}  "
          f"shortfall {mp.nstr(s_before, 10)} -> {mp.nstr(s_after, 10)}", flush=True)

    # ---- gates ----
    gates = {}
    g0_maxsum = max(M(str(a)) + M(str(b)) for a, b in product(RADII, RADII))
    g0_maxdr = max(M(str(d)) * (M(str(a)) + M(str(b)))
                   for d in D_GRID for a, b in product(RADII, RADII))
    gates["G0"] = dict(status="PASS" if (g0_maxsum <= LOG2_HALF
                                         and g0_maxdr <= M("0.15588")
                                         and not g0_bad) else "FAIL",
                       max_Rf_plus_Ru=mp.nstr(g0_maxsum, 10),
                       log2_half=mp.nstr(LOG2_HALF, 12),
                       max_d_Rg=mp.nstr(g0_maxdr, 10))

    g1a = ref10["ratio"] < ref["ratio"]
    g1b = abs(s_after - 10 * s_before) <= G1_TOL * max(1, s_before)
    g1c = RANK[ref10["band"]] <= RANK[ref["band"]]
    gates["G1"] = dict(status="PASS" if (g1a and g1b and g1c) else "FAIL",
                       g1a_strictly_lower_ratio=bool(g1a),
                       g1b_shortfall_x10_identity=bool(g1b),
                       g1c_band_rank_nonincreasing=bool(g1c),
                       ref_ratio=mp.nstr(ref["ratio"], 12), ref_band=ref["band"],
                       inflated_ratio=mp.nstr(ref10["ratio"], 12),
                       inflated_band=ref10["band"],
                       shortfall_before=mp.nstr(s_before, 12),
                       shortfall_after=mp.nstr(s_after, 12))

    # G2 dense sweeps on the locked closed forms (float64-safe: smooth ops,
    # max argument 2*d*Rg = 0.3118, no conditioning issue).
    rg_s = [0.04 + (LOG2 / 2 - 0.04) * i / 39 for i in range(40)]
    cmin_rg = [min(c_couplings(M(str(0.05)), M(str(0.1)), M(str(r))))
               for r in rg_s]
    ds = [1e-4 + (0.45 - 1e-4) * i / 39 for i in range(40)]
    cmin_d = [min(c_couplings(M(str(x)), M("0.1"), M("0.16"))) for x in ds]
    dls = [1e-3 + (1.0 - 1e-3) * i / 39 for i in range(40)]
    cmin_dl = [min(c_couplings(M("0.05"), M(str(x)), M("0.16"))) for x in dls]
    ratio_cm = [1 - 2 * M(str(m)) * M("2") / M("0.1") for m in
                [0.01 + 0.99 * i / 39 for i in range(40)]]
    ratio_ce = [1 - 2 * M("0.3") * M(str(c)) / M("0.1") for c in
                [0.05 + 4.95 * i / 39 for i in range(40)]]
    g2_ok = all(b > a for a, b in zip(cmin_rg, cmin_rg[1:])) \
        and all(b > a for a, b in zip(cmin_d, cmin_d[1:])) \
        and all(b > a for a, b in zip(cmin_dl, cmin_dl[1:])) \
        and all(b < a for a, b in zip(ratio_cm, ratio_cm[1:])) \
        and all(b < a for a, b in zip(ratio_ce, ratio_ce[1:]))
    gates["G2"] = dict(status="PASS" if g2_ok else "FAIL",
                       strict_all_sweeps=bool(g2_ok))

    viol = g3_bad + g3b_bad
    gates["G3"] = dict(status="PASS" if not viol else "FAIL",
                       n_violations=len(viol),
                       examples=[str(v) for v in viol[:8]],
                       min_K_loc=mp.nstr(min_K, 10),
                       precision="mpmath prec=200 (~60 dps)",
                       residuals_at="<= 1e-30 locked", ties_reported=len(tie_cells))

    dT = M("1e-3")
    CC_T, CD_T = c_couplings(dT, M("0.1"), M("0.16"))
    lim_CC = 8 * mp.pi * dT ** 2 * M("0.0256") + 2 * M("0.001") * M("0.004096")
    lim_CD = mp.mpf(4) / 3 * M("0.001") * M("0.004096")
    a_ok = abs(CC_T - lim_CC) <= M("0.01") * CC_T
    b_ok = abs(CD_T - lim_CD) <= M("0.01") * CD_T
    rgs = sorted({Rf + Ru for Rf, Ru in product(RADII, RADII)})
    c_ok = all(c_couplings(dT, M(str(dl)), M(str(rg)))[1]
               < c_couplings(dT, M(str(dl)), M(str(rg)))[0]
               for dl in DELTA_GRID for rg in rgs)
    gates["G4"] = dict(status="PASS" if (a_ok and b_ok and c_ok and not g4_bad)
                       else "FAIL",
                       rel_err_C_C=mp.nstr(abs(CC_T - lim_CC) / CC_T, 6),
                       rel_err_C_D=mp.nstr(abs(CD_T - lim_CD) / CD_T, 6),
                       CD_attains_all_corners=bool(c_ok),
                       n_violations=len(g4_bad))

    gates["G5"] = dict(status="PASS" if not g5_bad else "FAIL",
                       n_violations=len(g5_bad), max_d_Rg=mp.nstr(g0_maxdr, 10))

    balance = {}
    for Ru, rr, im in product(RADII, RERE_GRID, IMRI_GRID):
        best = None
        for Rf in RADII:
            e = evaluate(M("0.05"), M("0.1"), M(str(Rf)), M(str(Ru)),
                         M("0.01"), M("0.01"), M(str(rr)), M(str(im)))
            obj = e["C_min"] * e["ceiling"]
            if best is None or obj < best[1]:
                best = (Rf, obj, e["ratio"], e["band"])
        balance[f"{Ru}|{rr}+{im}i"] = dict(Rf_star=best[0],
                                           objective=mp.nstr(best[1], 10),
                                           ratio=mp.nstr(best[2], 10),
                                           band=best[3])
    gates["G6"] = dict(status="REPORTED (no verdict weight)",
                       n=len(balance), table=balance)

    # ---- frontier / seam ----
    frontier, seam = {}, {}
    for row in cells:
        d, delta, Rf, Ru, Rg = row[0], row[1], row[2], row[3], row[4]
        b = row[12]
        k = (d, round(Rg, 6))
        if b == "PASS" and (k not in frontier or delta > frontier[k]):
            frontier[k] = delta
        if b == "FAIL":
            kk = (delta, round(Rg, 6))
            if kk not in seam or d > seam[kk]:
                seam[kk] = d
    print("[frontier] per (d, Rg) largest-PASS-delta:", flush=True)
    for k in sorted(frontier):
        print(f"  d={k[0]}  Rg={k[1]}  delta*={frontier[k]}", flush=True)
    print(f"[seam] per (delta, Rg) largest-FAIL-d, entries={len(seam)}:", flush=True)
    for k in sorted(seam):
        print(f"  delta={k[0]}  Rg={k[1]}  d_failmax={seam[k]}", flush=True)

    # ---- outputs ----
    best = max(cells, key=lambda r: mp.mpf(r[11]))
    worst = min(cells, key=lambda r: mp.mpf(r[11]))
    summary = dict(prereg="1393 v3", law65="MODEL only", n_cells=len(cells),
                   counts=counts, tie_cells=tie_cells,
                   precision="mpmath 200-bit; banding in mpf",
                   reference=dict(d=0.05, delta=0.1, Rf=0.08, Ru=0.08,
                                  eps=0.01, epsp=0.01, rho="0.75+14.134725i",
                                  ratio=mp.nstr(ref["ratio"], 12),
                                  band=ref["band"],
                                  ceiling=mp.nstr(ref["ceiling"], 12),
                                  C_min=mp.nstr(ref["C_min"], 12),
                                  C_C=mp.nstr(ref["C_C"], 12),
                                  C_D=mp.nstr(ref["C_D"], 12)),
                   reference_x10=dict(ratio=mp.nstr(ref10["ratio"], 12),
                                      band=ref10["band"],
                                      shortfall_before=mp.nstr(s_before, 12),
                                      shortfall_after=mp.nstr(s_after, 12)),
                   best_cell=dict(d=best[0], delta=best[1], Rf=best[2],
                                  Ru=best[3], ratio=best[11], band=best[12]),
                   worst_cell=dict(d=worst[0], delta=worst[1], Rf=worst[2],
                                   Ru=worst[3], ratio=worst[11], band=worst[12]),
                   frontier={f"{k[0]}|{k[1]}": v for k, v in sorted(frontier.items())},
                   seam={f"{k[0]}|{k[1]}": v for k, v in sorted(seam.items())},
                   gates=gates)
    with open("docs/proofs/1393_component5_rig_results.json", "w") as f:
        json.dump(summary, f, indent=1, default=str)
    with open("docs/proofs/1393_component5_rig_cells.tsv", "w") as f:
        f.write("d\tdelta\tRf\tRu\tRg\tK_loc_f\tK_loc_u\tceiling\tC_C\tC_D\t"
                "C_min\tratio\tband\n")
        for row in cells:
            f.write("\t".join(str(x) for x in row) + "\n")

    parts = ",".join(f"{k}:{'PASS' if gates[k]['status'] == 'PASS' else 'FAIL'}"
                     for k in ("G0", "G1", "G2", "G3", "G4", "G5"))
    print(f"DONE gates={parts}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
