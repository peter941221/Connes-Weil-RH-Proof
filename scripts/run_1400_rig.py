#!/usr/bin/env python3
"""1400 — RUNG-3 LOW-HEIGHT JOINT-WITNESS RIG (prereg
docs/proofs/1400_rung3_lowheight_joint_witness_prereg.md).

MODEL AND INSTRUMENT ARE BYTE-IDENTICAL TO THE 1398 v3 CHAIN BY IMPORT:
everything that computes a rung-3 quantity (solve_factor, Owner, F_at,
compute_A, laplace_g, gt_tier1, band_of_A with the GV margin, the
tolerance constants) comes from run_1398_rig and is NOT re-typed here —
that is the anti-drift mechanism this file's design rests on.

What 1400 changes: cell SELECTION (low zeta-zero heights im in
{14.134725, 21.022040, 25.010858}, never evaluated by 1398 which was
pinned to im=1054 by the A-blind max-ratio order), an instrument-
VISIBILITY FILTER on rung-2 conditioning (law F12 precondition), tiering
(20+10+10+head = 41), and artifact names / log identity. Zero re-locks
the 1398 v3 gate classes verbatim; the F12 audit in prereg section 5
predicts noise <= 2.4e-7 vs the 1e-5 class (40x margin).

Run from the repo root on the WSL mirror:
    python3.12 scripts/run_1400_rig.py
Law 42: committed before any rung-3 digit. RH not claimed.
"""
import hashlib
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp  # noqa: E402

mp.mp.prec = 200
import run_1398_rig as R  # noqa: E402  (the locked 1398 v3 instrument)

LOW_IMS = (14.134725, 21.022040, 25.010858)
VIS_ALPHA = 1e-11                 # prereg section 1 filter
VIS_DELTA = 100 * 2.3e-16         # prereg section 1 filter (per unit R)
EXPECT_SIZES = {LOW_IMS[0]: 180, LOW_IMS[1]: 320, LOW_IMS[2]: 320}
EXPECT_TIER1 = (0.1732, 0.08, 0.01, 0.01, 0.99, 14.134725)
T0 = time.time()


def stamp(msg):
    print(f"[{time.time() - T0:7.1f}s] {msg}", flush=True)


def select_and_filter(cand):
    """A-blind: rung-2 quantities only (alpha, delta via the imported
    1398 solve_factor — same formulas, same code path, no owner values
    returned or used)."""
    cache = {}
    vis, exl = [], []

    def fac(Rd, ep, rr, im):
        key = (Rd, ep, rr, im)
        if key not in cache:
            f = R.solve_factor(Rd, ep, [0, 0, 0, -1],
                               R.MC(str(rr), str(im)))
            cache[key] = (float(f['alpha']), float(f['delta']))
        return cache[key]

    for g in sorted(k for k in cand if k[5] in LOW_IMS):
        Rf, Ru, eps, epsp, rr, im = g
        af, df = fac(Rf, eps, rr, im)
        au, du = fac(Ru, epsp, rr, im)
        rec = (g, af, au, df, du)
        if (af >= VIS_ALPHA and au >= VIS_ALPHA
                and df >= VIS_DELTA * Rf and du >= VIS_DELTA * Ru):
            vis.append(rec)
        else:
            exl.append(rec)
    per = {}
    for im in LOW_IMS:
        gs = [r[0] for r in vis if r[0][5] == im]
        per[im] = sorted(gs, key=lambda g: (-cand[g][1], g[4], g[0],
                                            g[1], g[2], g[3]))
    return per, vis, exl, cache


def main():
    stamp("decode 1393 cells artifact (imported 1398 layer)")
    rows = R.decode_cells()
    cand = {}
    for rw in rows:
        if rw['band'] == 'PASS':
            m = cand.setdefault(rw['geo'], [0, -9.0])
            m[0] += 1
            m[1] = max(m[1], rw['ratio'])

    stamp("visibility filter + selection (rung-2 layer)")
    per, vis, exl, _cache = select_and_filter(cand)
    for im in LOW_IMS:
        assert len(per[im]) == EXPECT_SIZES[im], (im, len(per[im]))
    tier1 = per[LOW_IMS[0]][0]
    assert tier1 == EXPECT_TIER1, f"selection drift: {tier1}"
    tested = ([per[LOW_IMS[0]][0]] + per[LOW_IMS[0]][1:21]
              + per[LOW_IMS[1]][:10] + per[LOW_IMS[2]][:10])
    assert len(tested) == 41 == len(set(tested))
    stamp(f"visible {len(vis)} / excluded {len(exl)}; tested 41 = "
          f"1 + 20(im14.13) + 10(im21.02) + 10(im25.01)")

    gibad = R.gi_check(rows)
    gates = {'GI': 'PASS' if not gibad else 'FAIL'}
    stamp("GI done")

    out_cells = []
    t1 = None
    validity = ['G0', 'GI', 'GS', 'GT', 'GF', 'GD', 'GR', 'GQ']
    run_void = bool(gibad)
    if run_void:
        print(f"GI-violations {gibad[:5]}", flush=True)

    if not run_void:
        t1 = R.run_geometry(tested[0], full=True)
        gs = t1['gs_ok']
        gf = (t1['F0'].real > 0
              and abs(t1['F0'].imag) <= R.GF_IM_TOL * abs(t1['F0'].real)
              and abs(t1['F0_npw24'].real - t1['F0'].real)
              <= R.GF_RE_TOL * abs(t1['F0'].real))
        gt = (t1['gt_sym'] <= R.GT_SYM_TOL and t1['gt_pair'] <= R.GT_PAIR_TOL
              and t1['gt_jh'] <= R.GT_JH_TOL)
        gd = abs(t1['lap'] + 1) <= R.GD_TOL
        gr = abs(t1['A64'] - t1['A']) <= R.GR_TOL * abs(t1['A'])
        gq = abs(t1['A_quadr'] - 4 * t1['A']) <= R.GQ_TOL * abs(4 * t1['A'])
        g0 = True
        for name, ok in (('G0', g0), ('GS', gs), ('GT', gt), ('GF', gf),
                         ('GD', gd), ('GR', gr), ('GQ', gq)):
            gates[name] = 'PASS' if ok else 'FAIL'
        run_void = any(gates[k] != 'PASS' for k in validity)
        stamp(f"tier-1 A={t1['A']:.10e} S={t1['S']:.3e} F0={t1['F0']:.6e} "
              f"lap+1={abs(t1['lap'] + 1):.2e} gates={gates}")
        stamp(f"tier-1 extras: A64={t1['A64']:.6e} A2v={t1['A_quadr']:.6e} "
              f"gt=({t1['gt_sym']:.1e},{t1['gt_pair']:.1e},{t1['gt_jh']:.1e}) "
              f"A_alpha2={t1['A_alpha2']:.6e} A96={t1['A96']:.6e} "
              f"A_R={t1['A_R']:.6e}")
        if not run_void:
            out_cells.append(('tier1', t1, R.band_of_A(t1['A'], t1['S'])))
            for geo in tested[1:]:
                r = R.run_geometry(geo)
                bad = ((not r['gs_ok']) or not (
                    r['F0'].real > 0
                    and abs(r['F0'].imag) <= R.GF_IM_TOL * abs(r['F0'].real)
                ) or abs(r['lap'] + 1) > R.GD_TOL)
                band = 'BADCELL' if bad else R.band_of_A(r['A'], r['S'])
                out_cells.append(('tier2', r, band))
                stamp(f"cell {geo}: A={r['A']:.6e} S={r['S']:.3e} "
                      f"F0={r['F0'].real:.4e} |lap+1|={abs(r['lap']+1):.2e} "
                      f"band={band}")
            run_void = any(gates[k] != 'PASS' for k in validity)

    npos = sum(1 for _, _, b in out_cells if b == 'POS')
    sneg = sum(1 for _, _, b in out_cells if b == 'NEG')
    ntie = sum(1 for _, _, b in out_cells if b == 'TIE')
    nbad = sum(1 for _, _, b in out_cells if b == 'BADCELL')
    witness = next((r['geo'] for _, r, b in out_cells if b == 'POS'), None)
    if run_void:
        print("VERDICT jointWitness=NONE cells=VOID", flush=True)
    else:
        w = ("NONE" if witness is None else
             f"Rf={witness[0]},Ru={witness[1]},eps={witness[2]},"
             f"epsp={witness[3]},rho={witness[4]}+{witness[5]}I")
        print(f"VERDICT jointWitness={w} cells=POS:{npos},NEG:{sneg},"
              f"TIE:{ntie},BAD:{nbad}", flush=True)
    parts = ",".join(f"{k}:{gates.get(k, 'SKIP')}" for k in validity)
    print(f"DONE gates={parts}", flush=True)

    res = dict(wall_s=time.time() - T0,
               tier1=_ser(t1) if t1 is not None else None,
               candidates=len(vis) + len(exl), low_visible=len(vis),
               low_excluded=len(exl), tested=len(out_cells),
               census=dict(POS=npos, NEG=sneg, TIE=ntie, BAD=nbad),
               witness=list(witness) if witness else None,
               void=run_void, gates=gates,
               cells=[dict(kind=k, **_ser(r), band=b)
                      for k, r, b in out_cells])
    with open("docs/proofs/1400_rig_results.json", 'w') as fh:
        json.dump(res, fh, indent=1, default=str)

    with open("docs/proofs/1400_rig_cells.tsv", 'w') as fh:
        fh.write("kind\tRf\tRu\teps\tepsp\tRERHO\tIMRHO\tdelta_f\tdelta_u\t"
                 "alpha_f\talpha_u\tTB_f\tTB_u\tReF0\tImF0\tA\tS\tlap_re\t"
                 "lap_im\tband\n")
        for k, r, b in out_cells:
            g = r['geo']
            fh.write(f"{k}\t{g[0]}\t{g[1]}\t{g[2]}\t{g[3]}\t{g[4]}\t{g[5]}\t"
                     f"{r['delta_f']:.6e}\t{r['delta_u']:.6e}\t"
                     f"{r['alpha_f']:.6e}\t{r['alpha_u']:.6e}\t"
                     f"{r['TB_f']:.6e}\t{r['TB_u']:.6e}\t"
                     f"{r['F0'].real:.6e}\t{r['F0'].imag:.2e}\t"
                     f"{r['A']:.6e}\t{r['S']:.6e}\t{r['lap'].real:.6e}\t"
                     f"{r['lap'].imag:.2e}\t{b}\n")
    subprocess.run(["gzip", "-f", "docs/proofs/1400_rig_cells.tsv"],
                   check=True)
    with open("docs/proofs/1400_rig_visibility.tsv", 'w') as fh:
        fh.write("Rf\tRu\teps\tepsp\tRERHO\tIMRHO\talpha_f\talpha_u\t"
                 "delta_f\tdelta_u\tstatus\n")
        for g, af, au, df, du in sorted(vis + exl, key=lambda x: (x[0][5],
                                                                  -x[0][4])):
            st = 'TESTED' if g in tested else 'VISIBLE'
            if (af < VIS_ALPHA or au < VIS_ALPHA
                    or df < VIS_DELTA * g[0] or du < VIS_DELTA * g[1]):
                st = 'EXCLUDED'
            fh.write(f"{g[0]}\t{g[1]}\t{g[2]}\t{g[3]}\t{g[4]}\t{g[5]}\t"
                     f"{af:.4e}\t{au:.4e}\t{df:.4e}\t{du:.4e}\t{st}\n")
    for p in ("docs/proofs/1400_rig_results.json",
              "docs/proofs/1400_rig_cells.tsv.gz",
              "docs/proofs/1400_rig_visibility.tsv"):
        h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
        print(f"sha256 {p} = {h}", flush=True)
    return 0


def _ser(r):
    d = dict(r)
    for k in ('F0', 'lap', 'F0_npw24'):
        if k in d and isinstance(d[k], complex):
            d[k] = [d[k].real, d[k].imag]
    d['geo'] = list(r['geo'])
    return d


if __name__ == "__main__":
    sys.exit(main())
