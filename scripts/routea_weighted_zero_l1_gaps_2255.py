#!/usr/bin/env python3
"""2255 - Ideal-to-discrete gaps of the 2249 L1 enclosure, measured and
charged: GL phi quadrature (m doubling), the [-40,40] window (ring
extension to +-80), and the trapezoid step (0.02 -> 0.01).

Reuses the 2249 instrumented machinery module (import, same code path,
CHUNK only changes grid chunking, not arithmetic).  Three runs:

  R1  m = 12800, grid [-40,40] step 0.02   -> GL quadrature gap
  R2  m = 6400, ring |x| in [40,80] step 0.02 (with +-40 endpoint
      corrections)                          -> window gap
  R3  m = 6400, grid [-40,40] step 0.01    -> trapezoid step gap

Each gap is charged as |delta q| + the two enclosures' E-totals; the
terminal full-tail ledger of 2253 is then repriced against the
gap-adjusted certified margin.  Writes results/2255_l1_gaps.json.
"""
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_weighted_zero_l1_enclosure_2249 as r49  # noqa: E402

OUTPUT = ROOT / "results" / "2255_l1_gaps.json"
ARTIFACT_2249 = ROOT / "results" / "2249_l1_enclosure.json"
MODE = sys.argv[1] if len(sys.argv) > 1 else "all"


def run_instrumented(m, grid, chunk=64, tag=""):
    t0 = time.time()
    r49.M = m
    r49._GL_XS = None
    r49._GL_WS = None
    _, nodes, values, fam = r49.build()
    npts = grid.shape[0]
    xw_cache = {}
    xw = []
    for pair in fam:
        a = pair[0]
        if float(a) not in xw_cache:
            xw_cache[float(a)] = r49.phi_weights_cached(a)
        xw.append(xw_cache[float(a)])
    a_mat = r49.r80.family_values(fam, r49.K, np.asarray(nodes, complex), xw).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    tables = []
    for j, (a, th) in enumerate(fam):
        X, f, ef = r49.phi_terms(a, xw[j])
        tables.append((a, th, X, f, ef))
    nfam = len(fam)
    vre = np.zeros((nfam, npts))
    evre = np.zeros((nfam, npts))
    vim = np.zeros((nfam, npts))
    evim = np.zeros((nfam, npts))
    for j, (a, th, X, f, ef) in enumerate(tables):
        for lo in range(0, npts, chunk):
            hi = min(lo + chunk, npts)
            r0, er0, i0, ei0 = r49.laplace_rows(a, th, X, f, ef, grid[lo:hi])
            vre[j, lo:hi] = r0
            evre[j, lo:hi] = er0
            vim[j, lo:hi] = i0
            evim[j, lo:hi] = ei0
    lre, elre, lim, elim = r49.dot30(vre, evre, vim, evim, base)
    cre, ecre, cim, ecim = r49.dot30(vre, evre, vim, evim, corr)
    hb, ehb = r49.sq_abs(lre, elre, lim, elim)
    hc, ehc = r49.sq_abs(cre, ecre, cim, ecim)
    support = 2 * max(pair[0] for pair in fam)
    primes = r49.r59.rig.prime_powers_up_to(math.exp(support))
    kern, ekern = r49.kernel_full(grid, primes)
    rho = (0.5 + r49.DELTA) + 1j * r49.GAMMA
    p, ep = r49.p_instrumented(grid, r49.r80.counterpart_nodes(rho))
    p2, ep2 = r49.m2(p, ep, p, ep)
    g, eg = r49.m2(kern, ekern, p2, ep2)
    g, eg = r49.m2(g, eg, hb, ehb)
    g, eg = r49.m2(g, eg, hc, ehc)
    terms = [float(v) for v in g]
    eg_list = [float(v) for v in eg]
    wall = time.time() - t0
    print("[run m=%d npts=%d tag=%s] %.1fs" % (m, npts, tag, wall),
          flush=True)
    return {"grid": grid, "g": terms, "eg": eg_list, "wall": wall}


def charge_sum(terms, eg_list, weights):
    """2249-identical accounting for a weighted sum with endpoint rules."""
    builds = [float(weights[i] * terms[i]) for i in range(len(terms))]
    q = math.fsum(builds)
    e_pts = [float(weights[i] * eg_list[i]) for i in range(len(terms))]
    e_pts_round = r49.U * math.fsum([abs(v) for v in e_pts])
    e_prod = r49.U * math.fsum([abs(t) for t in builds])
    e_sum = math.fsum(e_pts) + e_pts_round + e_prod + r49.U * abs(q)
    e_total = r49.INFLATE * e_sum
    return q, e_total


def main():
    art = json.loads(ARTIFACT_2249.read_text(encoding="utf-8"))
    diag = art["diagnostics"]
    q_committed = diag["q"]
    e_committed = diag["E_total"]
    results = {"record": 2255, "date": "2026-09-30",
               "q_committed": q_committed, "E_committed": e_committed}

    if MODE in ("all", "quad"):
        grid = np.arange(-r49.XMAX, r49.XMAX + r49.STEP / 2, r49.STEP)
        run = run_instrumented(12800, grid, tag="quad")
        w = np.full(run["grid"].shape[0], 1.0 / 50.0)
        w[0] = w[-1] = 1.0 / 100.0
        q, e = charge_sum(run["g"], run["eg"], w)
        gap = abs(q - q_committed) + e + e_committed
        results["quad"] = {
            "m_new": 12800, "q": q, "E": e,
            "delta": q - q_committed, "gap_charged": gap,
            "wall_s": run["wall"]}
        print(json.dumps({"quad": results["quad"]}, indent=2), flush=True)

    if MODE in ("all", "window", "ring"):
        full = np.arange(-80.0, 80.0 + r49.STEP / 2, r49.STEP)
        ring = full[np.abs(full) >= 40.0 - 1e-9]
        run = run_instrumented(6400, ring, tag="ring")
        grid = run["grid"]
        w = np.full(grid.shape[0], 1.0 / 50.0)
        ep40 = np.abs(grid) <= 40.0 + 1e-9
        ep80 = np.abs(grid) >= 80.0 - 1e-9
        w[ep80] = 1.0 / 100.0
        w[ep40] = 0.0
        q_ring, e_ring = charge_sum(run["g"], run["eg"], w)
        # endpoint correction: +-40 change weight 1/100 -> 1/50
        idx40 = np.where(ep40)[0]
        corr_terms = [(1.0 / 50.0 - 1.0 / 100.0) * float(run["g"][i])
                      for i in idx40]
        corr_egs = [(1.0 / 100.0) * float(run["eg"][i]) for i in idx40]
        q40c = math.fsum(corr_terms)
        e40c = r49.INFLATE * (math.fsum(corr_egs)
                              + r49.U * math.fsum(
                                  [abs(t) for t in corr_terms]))
        delta = q_ring + q40c
        e_delta = (r49.INFLATE * (e_ring + e40c) + e_committed)
        gap = abs(delta) + e_delta
        results["window"] = {
            "ring_points": int(grid.shape[0]),
            "q_ring": q_ring, "E_ring": e_ring,
            "q_endpoint_correction": q40c, "E_endpoint_correction": e40c,
            "delta": delta, "gap_charged": gap,
            "g_abs_at_40": float(abs(run["g"][idx40[0]])),
            "g_abs_at_80": float(abs(run["g"][int(np.where(ep80)[0][0])])),
            "wall_s": run["wall"]}
        print(json.dumps({"window": results["window"]}, indent=2),
              flush=True)

    if MODE in ("all", "step"):
        grid = np.arange(-r49.XMAX, r49.XMAX + r49.STEP / 4, r49.STEP / 2)
        run = run_instrumented(6400, grid, tag="step")
        w = np.full(run["grid"].shape[0], 1.0 / 100.0)
        w[0] = w[-1] = 1.0 / 200.0
        q, e = charge_sum(run["g"], run["eg"], w)
        gap = abs(q - q_committed) + e + e_committed
        results["step"] = {
            "step_new": 0.01, "q": q, "E": e,
            "delta": q - q_committed, "gap_charged": gap,
            "wall_s": run["wall"]}
        print(json.dumps({"step": results["step"]}, indent=2), flush=True)

    # total ideal-to-discrete charge and repriced terminal ledger
    gaps = [results[k]["gap_charged"] for k in ("quad", "window", "step")
            if k in results]
    total_gap = sum(gaps)
    margin = -diag["q_hi"]
    margin_gap = margin - total_gap
    tail = 4894093747.764274
    known = 74601530.30234718
    charge = tail + known
    eps0 = margin_gap - charge
    results["total"] = {
        "gap_charged_quad": results.get("quad", {}).get("gap_charged"),
        "gap_charged_window": results.get("window", {}).get("gap_charged"),
        "gap_charged_step": results.get("step", {}).get("gap_charged"),
        "total_gap_charged": total_gap,
        "margin_2249": margin, "margin_gap_adjusted": margin_gap,
        "charge_full_tail": charge,
        "reading": charge / margin_gap,
        "eps0": eps0,
    }
    results["nonclaims"] = [
        "the gap charges are measured by refinement doubling (m, window, "
        "step), charged as the full difference plus both enclosures' "
        "E-totals; they are refinement estimates, not analytic error "
        "bounds",
        "the owner-list and float-solve gaps are not treated here (2254 "
        "certifies the owner list per configuration; the solve convention "
        "is 2230 convention A)",
        "no producer GO, no gate sign change, no RH claim",
    ]
    results["provenance"] = {
        "script": "scripts/routea_weighted_zero_l1_gaps_2255.py",
        "machinery": "scripts/routea_weighted_zero_l1_enclosure_2249.py",
        "artifact_2249": "results/2249_l1_enclosure.json",
    }
    OUTPUT.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"total": results["total"]}, indent=2))


if __name__ == "__main__":
    main()