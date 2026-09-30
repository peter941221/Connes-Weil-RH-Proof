"""Record 2303: certified centered-strip envelope for the corrected owner.

Record 2276 proved that the 2249/2103 pipeline's ideal integral is the
change of variable y = a x of the legacy construction, i.e. the physical
profile is

    phi_(a^2)(y) * exp(i theta y),     phi_R(y) = exp(-30/(1-(y/R)^2)),

on |y| < R = a^2, with the SAME stored coefficient vectors.  The legacy
2267 centered-strip envelope was built on u = x/a profiles and is therefore
not a supplier for this owner (2276 scoped no-go).  This record rebuilds the
envelope on the corrected profiles with the existing certified machinery:

1. directed 256-bit MPFR node values of the four channels
   (base_M0, base_D2, corr_M0, corr_D2) on the corrected grid
   x in [-a_max^2, a_max^2], NX = 240001 -- the 2234 chunk/sigma pipeline
   with the single substitution a -> a^2 at the family-radius interface
   (`o34.node_bounds` is radius-generic);
2. a directed MPFR zero-count certificate Z = 0 for the four corrected
   channels (the 2242 pavement with the corrected family list, plus the
   analytic edge arcs on (a29^2, a30^2) where only the a30 family lives);
3. the composite-EM panel (dx^2/12)(2 a_max^2) M_k(sigma) at N_risk = 0,
   with the phi^(k) ladder evaluated at the corrected radii;
4. the 2237 certified coefficient radii charged through the corrected
   ladder, and the log-derivative sigma-transfer e^{2 a_max^2 h}.

Verdict: CORRECTED-STRIP-COVERED iff the certified continuum sup of
N(sigma) = min(D2_b M_c, D2_c M_b) over [-1/2, 1/2] is at most the frozen
bUpper2243 = 9506275.102584327 (the constant consumed by the 2265/2268
producer wiring).  Every failure path emits STRIP-CONTROL-FAIL.

Modes (environment):
  MODE=recon                       numpy anchor screen (2277 reproduction)
  MODE=chunk CHUNK=k               -> results/2303_chunk_k.npz
  MODE=sigma SIGMA_INDEX=j         -> results/2303_sigma_j.json
  MODE=pave_<name>                 -> results/2303_pave_<name>.json
  MODE=edge                        -> results/2303_edge.json
  MODE=reduce                      -> results/2303_corrected_strip_envelope.json
"""
import ctypes as C
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
K = 30.0
NX = 240001
SLACK_EXP = 200
NCHUNK = 12
GRID_J = list(range(-50, 51))
HALF_STEP = 0.005
FROZEN_B = 9506275.102584327
R_BASE_2237 = 1005486.289224448
R_CORR_2237 = 2057069012.526474
OWNER_CAPTURE = R / "2275_gap_owner_audit.json"
REPLAY_OPERANDS = R / "2267_replay_operands.json"
OUT = R / "2303_corrected_strip_envelope.json"


def CHUNK(k):
    return R / f"2303_chunk_{k}.npz"


def SIGMA_JSON(j):
    return R / f"2303_sigma_{j}.json"


def PAVE_JSON(name):
    return R / f"2303_pave_{name}.json"


EDGE_JSON = R / "2303_edge.json"


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


o34 = _load("o34_2303", "routea_weighted_zero_direct_product_outward_2234.py")
p38 = _load("p38_2303", "routea_weighted_zero_panel_dx2_2238.py")
p42 = _load("p42_2303", "routea_weighted_zero_zero_count_certificate_2242.py")

UP = lambda v: math.nextafter(v, math.inf)


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def load_owner():
    """Audited 2249 owner capture, anchored against the 2267 replay operands."""
    cap = json.loads(OWNER_CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    fam = [(float.fromhex(w), float.fromhex(t)) for w, t in cap["families_hex"]]
    base = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["base_hex"]])
    corr = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["corr_hex"]])
    op = json.loads(REPLAY_OPERANDS.read_text(encoding="utf-8"))
    fam67 = [tuple(float.fromhex(v) for v in f) for f in op["families_hex"]]
    b67 = [complex(*(float.fromhex(v) for v in c)) for c in op["base_hex"]]
    c67 = [complex(*(float.fromhex(v) for v in c)) for c in op["corr_hex"]]
    anchors = {
        "families_bitwise": all(x[0] == y[0] and x[1] == y[1]
                                for x, y in zip(fam, fam67)),
        "base_bitwise": all(x == y for x, y in zip(base, b67)),
        "corr_bitwise": all(x == y for x, y in zip(corr, c67)),
        "base_md5": cap["base_md5"], "corr_md5": cap["corr_md5"],
    }
    if not all(anchors[k] for k in ("families_bitwise", "base_bitwise",
                                    "corr_bitwise")):
        raise ValueError("owner capture does not match the 2267 replay operands")
    if len(fam) != 30:
        raise ValueError("expected 30 families")
    return fam, base, corr, anchors


def corrected_fam(fam):
    """The single audited substitution: the physical radius is a^2."""
    return [(a * a, th) for a, th in fam]


def x_grid(rmax):
    return np.linspace(-rmax, rmax, NX)


def fam_par(fam, base, corr):
    return [(a, th, complex(bc), complex(cc))
            for (a, th), bc, cc in zip(fam, base, corr)]


# ----------------------------------------------------------------- numpy side
def recon():
    """Reproduce the 2277 raw screen bitwise and size the EM panel."""
    fam, base, corr, anchors = load_owner()
    cfam = corrected_fam(fam)
    rmax = max(a for a, _ in cfam)
    grid = x_grid(rmax)
    out = {"record": 2303, "mode": "recon", "anchors": anchors,
           "rmax": rmax, "dx": float(grid[1] - grid[0]), "channels": {}}
    h = {}
    for name, coef in (("base", base), ("corr", corr)):
        v, v2 = _fields(grid, cfam, coef)
        h[name + "_M0"] = np.abs(v)
        h[name + "_D2"] = np.abs(v2)
    rows = []
    for j in GRID_J:
        sigma = j / 100.0
        w = np.exp(sigma * grid)
        vals = {name: float(np.trapezoid(arr * w, grid))
                for name, arr in h.items()}
        rows.append({"j": j, "sigma": sigma, "values": vals,
                     "B": min(vals["base_D2"] * vals["corr_M0"],
                              vals["corr_D2"] * vals["base_M0"])})
    best = max(rows, key=lambda r: r["B"])
    out["raw"] = {"B_max": best["B"], "at_sigma": best["sigma"],
                  "values": best["values"], "rows": rows}
    out["screen_2277"] = {"B_upper": 337039.47691484215,
                          "match": best["B"] == 337039.47691484215}
    for name, coef in (("base", base), ("corr", corr)):
        m = p38.ladder(cfam, coef)
        out["channels"][name] = {"ladder": m}
    out["majors_control"] = majors_control()
    OUT_ = R / "2303_recon.json"
    OUT_.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"mode": "recon", "B_max": best["B"],
                      "at_sigma": best["sigma"],
                      "match_2277": out["screen_2277"]["match"],
                      "dx": out["dx"], "rmax": rmax}, indent=2), flush=True)


def majors_control():
    """Numerical control of the 2238 ladder at the corrected radii.

    For phi_R(t) = exp(-K/(1-(t/R)^2)) write u = t/R, s = 1-u^2 and
    L = log phi = -K/s; the exact u-derivatives are
      L'   = -2Ku/s^2
      L''  = -2K(s+4u^2)/s^3
      L''' = -24Ku(s+2u^2)/s^4
      L''''= -24K(s^2+12u^2 s+16u^4)/s^5,
    and phi^(k) = R^-k * psi^(k)(u) with the Bell expansions
      psi' = psi L'; psi'' = psi(L''+L'^2);
      psi''' = psi(L'''+3L'L''+L'^3);
      psi'''' = psi(L''''+4L'L'''+3L''^2+6L'^2L''+L'^4).
    sup |psi^(k)| is radius-free, so the check runs once on the master and
    is scaled by R^-k here only to exercise majorant_phi_le directly.
    """
    g = np.concatenate([np.linspace(-1.0 + 1e-9, 1.0 - 1e-9, 400001),
                        np.linspace(0.9, 0.9999, 200001),
                        np.linspace(-0.9999, -0.9, 200001)])
    u = g
    s = 1.0 - u * u
    keep = s > 1e-6
    u = u[keep]
    s = s[keep]
    psi = np.exp(-K / s)
    lp = -2.0 * K * u / s ** 2
    lpp = -2.0 * K * (s + 4.0 * u * u) / s ** 3
    lppp = -24.0 * K * u * (s + 2.0 * u * u) / s ** 4
    lpppp = -24.0 * K * (s * s + 12.0 * u * u * s + 16.0 * u ** 4) / s ** 5
    d = [psi,
         psi * lp,
         psi * (lpp + lp * lp),
         psi * (lppp + 3.0 * lp * lpp + lp ** 3),
         psi * (lpppp + 4.0 * lp * lppp + 3.0 * lpp ** 2
                + 6.0 * lp * lp * lpp + lp ** 4)]
    sup = [float(np.max(np.abs(v))) for v in d]
    out = {"sup_master": sup, "radii": {}}
    for name, a in (("base", 1.6), ("pole", 2.56)):
        rad = a * a
        rows = {}
        for k in range(5):
            maj = p38.majors(rad)[k]
            rows[k] = {"sup_over_radius^k": sup[k] / rad ** k,
                       "majorant": maj,
                       "ratio": sup[k] / rad ** k / maj}
        out["radii"][name] = {"radius": rad, "rows": rows}
    assert all(r["ratio"] <= 1.0 for v in out["radii"].values()
               for r in v["rows"].values()), "ladder control failed"
    return out


def _fields(grid, fam, coef):
    value = np.zeros(grid.shape, dtype=complex)
    second = np.zeros(grid.shape, dtype=complex)
    for c, (a, th) in zip(coef, fam):
        u = grid / a
        q = 1.0 - u * u
        m = q > 0.0
        phi = np.zeros_like(grid)
        phi[m] = np.exp(-K / q[m])
        e1 = np.zeros_like(grid)
        e1[m] = -2.0 * K * u[m] / (a * q[m] ** 2)
        e2 = np.zeros_like(grid)
        e2[m] = (-2.0 * K / a ** 2) * (q[m] ** -2 + 4.0 * u[m] ** 2 * q[m] ** -3)
        term = c * phi * np.exp(1j * th * grid)
        value += term
        second += term * (e2 + e1 * e1 + 2j * th * e1 - th * th)
    return value, second


# ------------------------------------------------------------ directed MPFR
def chunk_worker(k, nchunk=NCHUNK):
    fam, base, corr, _ = load_owner()
    cfam = corrected_fam(fam)
    rmax = max(a for a, _ in cfam)
    x = x_grid(rmax)
    n = x.shape[0]
    i0 = (n * k) // nchunk
    i1 = (n * (k + 1)) // nchunk
    wb = o34.WB(80)
    acc = [o34.M() for _ in range(8)]
    fpar = fam_par(cfam, base, corr)
    U = np.empty((4, i1 - i0))
    slack = np.zeros((4, i1 - i0))
    try:
        for row, i in enumerate(range(i0, i1)):
            xv = float(x[i])
            for o in acc:
                o34.lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), 0)
            _, mags = o34.node_bounds(wb, xv, fpar, K, acc)
            s = [up_many((2.0 ** -SLACK_EXP) * mg, 3) for mg in mags]
            b = math.hypot(acc[0].get_d(0), acc[1].get_d(0))
            b2 = math.hypot(acc[2].get_d(0), acc[3].get_d(0))
            c0 = math.hypot(acc[4].get_d(0), acc[5].get_d(0))
            c2 = math.hypot(acc[6].get_d(0), acc[7].get_d(0))
            U[0, row] = up_many(b + s[0], 3)
            U[1, row] = up_many(b2 + s[1], 3)
            U[2, row] = up_many(c0 + s[2], 3)
            U[3, row] = up_many(c2 + s[3], 3)
            for q in range(4):
                slack[q, row] = s[q]
    finally:
        for o in acc:
            o.clear()
        wb.clear()
    np.savez(CHUNK(k), i0=np.asarray(i0), i1=np.asarray(i1), U=U,
             slack=slack, rmax=np.asarray(rmax))
    print(json.dumps({"mode": "chunk", "chunk": k, "i0": int(i0),
                      "i1": int(i1), "max_U": list(U.max(axis=1)),
                      "max_slack": float(slack.max()),
                      "max_position": [float(x[i0 + int(np.argmax(U[q]))])
                                       for q in range(4)]}), flush=True)


def sigma_worker(j):
    sigma = j / 100.0
    fam, _, _, _ = load_owner()
    rmax = max(a * a for a, _ in fam)
    x = x_grid(rmax)
    parts = []
    n_total = 0
    for k in range(NCHUNK):
        z = np.load(CHUNK(k))
        parts.append((int(z["i0"]), int(z["i1"]), z["U"]))
        n_total += z["U"].shape[1]
        assert float(z["rmax"]) == rmax
    wb = o34.WB(8)
    accs = [o34.M() for _ in range(4)]
    try:
        for o in accs:
            o34.lib.mpfr_set_d(C.byref(o.x), C.c_double(0.0), 0)
        for i0, _i1, U in sorted(parts):
            for row in range(U.shape[1]):
                i = i0 + row
                w = wb.exp(wb.t[0], wb.mul(wb.t[1], wb.set(wb.t[2], sigma),
                                           wb.set(wb.t[3], float(x[i]))))
                tw = 1.0 if (i == 0 or i == NX - 1) else 2.0
                for q in range(4):
                    term = wb.mul(wb.t[4],
                                  wb.set(wb.t[5], float(U[q, row]) * tw), w)
                    o34.lib.mpfr_add(C.byref(accs[q].x), C.byref(accs[q].x),
                                     C.byref(term.x), 0)
        dx = 2.0 * rmax / (NX - 1)
        factor = up_many(dx / 2.0, 4)
        out = {"record": 2303, "mode": "sigma", "sigma": sigma,
               "sigma_index": j, "nodes": n_total, "values": {}}
        for name, o in zip(("base_M0", "base_D2", "corr_M0", "corr_D2"), accs):
            out["values"][name] = up_many(o.get_d(0) * factor, 4)
    finally:
        wb.clear()
        for o in accs:
            o.clear()
    SIGMA_JSON(j).write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"sigma": sigma, "values": out["values"]}), flush=True)


def pave_worker(name):
    """Z = 0 pavement for one corrected channel (2242 machinery, a -> a^2)."""
    import time
    t0 = time.time()
    fam, base, corr, _ = load_owner()
    cfam = corrected_fam(fam)
    coef = base if name.startswith("base") else corr
    k = 0 if name.endswith("M0") else 2
    a29, a30, on_arc = p42.arc_geometry(cfam)
    kern = p42.Kernel(cfam, coef, k)
    anchors = [0.0]
    for a, _ in cfam:
        if float(a) < a29:
            anchors.extend([float(a), -float(a)])
    xs, ratio = p42.ratio_profile(cfam, coef, k, a29)
    boxes0 = p42.initial_boxes(a29, anchors, xs, ratio)
    assert len(boxes0) < 200000, "walk exploded"
    queue = [(lo, hi, 0) for lo, hi in boxes0]
    n_init = len(queue)
    n_pass_first = n_bis = n_fail = 0
    max_depth = 0
    hist = {}
    min_floor = None
    processed = 0
    while queue:
        lo, hi, d = queue.pop()
        ok, _ends, floor = kern.eval_box(lo, hi)
        processed += 1
        if processed % 5000 == 0:
            print(json.dumps({"part": name, "processed": processed,
                              "queued": len(queue),
                              "elapsed_s": round(time.time() - t0, 1)}),
                  flush=True)
        if ok:
            hist[d] = hist.get(d, 0) + 1
            if d == 0:
                n_pass_first += 1
            if floor > 0.0 and (min_floor is None or floor < min_floor[0]):
                min_floor = (floor, lo, hi)
            continue
        if d >= p42.MAXDEPTH:
            n_fail += 1
            continue
        m = 0.5 * (lo + hi)
        if not (lo < m < hi):
            n_fail += 1
            continue
        n_bis += 1
        max_depth = max(max_depth, d + 1)
        queue.append((lo, m, d + 1))
        queue.append((m, hi, d + 1))
    out = {"record": 2303, "part": "pave", "channel": name, "k": k,
           "region": [-a29, a29], "a29": a29, "a30": a30,
           "families_on_edge_arc": on_arc,
           "n_boxes_initial": n_init, "n_boxes_final": sum(hist.values()),
           "n_pass_first": n_pass_first, "n_bisections": n_bis,
           "max_depth": max_depth,
           "depth_histogram": {str(d): c for d, c in sorted(hist.items())},
           "n_failures": n_fail,
           "min_floor": None if min_floor is None
           else {"value": min_floor[0], "box": [min_floor[1], min_floor[2]]},
           "method": "directed 256-bit MPFR natural interval extension on the "
                     "corrected width-a^2 families, final 4-vector hull "
                     "expanded %d ulp; pass iff one coordinate interval "
                     "excludes 0" % p42.NOZERO_ULPS,
           "elapsed_s": round(time.time() - t0, 1),
           "verdict": "ZERO-FREE-CERTIFIED" if n_fail == 0 else "OPEN"}
    PAVE_JSON(name).write_text(json.dumps(out, indent=2) + "\n",
                               encoding="utf-8")
    print(json.dumps({key: out[key] for key in
                      ("verdict", "n_boxes_final", "n_failures", "max_depth",
                       "min_floor", "elapsed_s")}), flush=True)


def edge_worker():
    """Analytic zero-free certificate on the corrected edge arcs.

    On |y| in (a29^2, a30^2) only the largest-radius family is active.
    k = 0: F = c phi e^{i theta y} with c != 0 and phi > 0.
    k = 2: F'' = c phi e^{i theta y} B2(y); the exact factorization
    e1^2 + e2 = (2K/R^2) G2(q) q^-4, G2(q) = 2K - (2K+4) q + 3 q^2, and
    d/dq [G2(q) q^-4] = q^-5 (-240 + 192 q - 6 q^2) < 0 on q <= q_c
    (q_c = q(a29^2) for the a30 family), so
    B2_re >= (2K/R^2) G2(q_c) q_c^-4 - theta^2 > 0 certifies |B2| > 0.
    """
    fam, base, corr, _ = load_owner()
    cfam = corrected_fam(fam)
    a29, a30, on_arc = p42.arc_geometry(cfam)
    if not len(on_arc) == 1:
        raise ValueError("edge arc must carry exactly one family")
    r30, th30 = on_arc[0]
    idx = [i for i, (a, _) in enumerate(cfam)
           if float(a) == float(r30)][0]
    q_c = 1.0 - (a29 / r30) ** 2
    g2 = 2.0 * K - (2.0 * K + 4.0) * q_c + 3.0 * q_c * q_c
    lb_d2 = (2.0 * K / r30 ** 2) * g2 * q_c ** -4 - th30 ** 2
    dq_slope = -240.0 + 192.0 * q_c - 6.0 * q_c * q_c
    out = {"record": 2303, "part": "edge", "a29": a29, "a30": a30,
           "family": {"radius": r30, "theta": th30, "index": idx},
           "q_c": q_c, "G2_qc": g2, "monotone_slope": dq_slope,
           "B2_re_lower": lb_d2,
           "coef_nonzero": {
               "base": [complex(base[idx]).real, complex(base[idx]).imag],
               "corr": [complex(corr[idx]).real, complex(corr[idx]).imag]},
           "verdict": None}
    ok = (q_c > 0.0 and q_c < 1.0 and lb_d2 > 0.0 and dq_slope < 0.0
          and abs(complex(base[idx])) > 0.0 and abs(complex(corr[idx])) > 0.0
          and float(r30) == max(float(a) for a, _ in cfam))
    out["verdict"] = "EDGE-ZERO-FREE-CERTIFIED" if ok else "OPEN"
    EDGE_JSON.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verdict": out["verdict"], "q_c": q_c,
                      "B2_re_lower": lb_d2, "slope": dq_slope},
                     indent=2), flush=True)


# ------------------------------------------------------------------ reduce
def panel_em_sym(channel, sigma, m):
    """Composite-EM panel with N_risk = 0, sigma-symmetric weight."""
    k = 0 if channel.endswith("M0") else 2
    s = abs(sigma)
    return (dx_of() ** 2 / 12.0) * (2.0 * rmax_of()) * math.exp(
        s * rmax_of()) * (m[k + 2] + 2.0 * s * m[k + 1] + sigma * sigma * m[k])


def rmax_of():
    fam, _, _, _ = load_owner()
    return max(a * a for a, _ in fam)


def dx_of():
    return 2.0 * rmax_of() / (NX - 1)


def coeff_infl_sym(coef, fam, sigma, radius, order):
    s = abs(sigma)
    acc = 0.0
    for (a, _th), _coef in zip(fam, coef):
        acc += 2.0 * a * math.exp(s * rmax_of()) * o34.majorant_phi_le(
            order, K, a)
    return radius * acc


def reduce_worker():
    fam, base, corr, anchors = load_owner()
    cfam = corrected_fam(fam)
    rmax = max(a for a, _ in cfam)
    dx = 2.0 * rmax / (NX - 1)
    ladder = {"base": p38.ladder(cfam, base), "corr": p38.ladder(cfam, corr)}
    pave = {}
    for name in ("base_M0", "base_D2", "corr_M0", "corr_D2"):
        p = PAVE_JSON(name)
        pave[name] = json.loads(p.read_text(encoding="utf-8")) if p.exists() \
            else {"verdict": "MISSING"}
    edge = (json.loads(EDGE_JSON.read_text(encoding="utf-8"))
            if EDGE_JSON.exists() else {"verdict": "MISSING"})
    zero_free = (all(v["verdict"] == "ZERO-FREE-CERTIFIED"
                     for v in pave.values())
                 and edge["verdict"] == "EDGE-ZERO-FREE-CERTIFIED")
    rows = []
    for j in GRID_J:
        p = SIGMA_JSON(j)
        assert p.exists(), p
        point = json.loads(p.read_text(encoding="utf-8"))
        if (point["sigma_index"] != j or point["nodes"] != NX):
            raise ValueError(f"invalid sigma input: {p.name}")
        v = point["values"]
        sigma = j / 100.0
        pb = panel_em_sym("base_M0", sigma, ladder["base"])
        pb2 = panel_em_sym("base_D2", sigma, ladder["base"])
        pc = panel_em_sym("corr_M0", sigma, ladder["corr"])
        pc2 = panel_em_sym("corr_D2", sigma, ladder["corr"])
        eb = coeff_infl_sym(base, cfam, sigma, R_BASE_2237, 0)
        eb2 = coeff_infl_sym(base, cfam, sigma, R_BASE_2237, 2)
        ec = coeff_infl_sym(corr, cfam, sigma, R_CORR_2237, 0)
        ec2 = coeff_infl_sym(corr, cfam, sigma, R_CORR_2237, 2)
        mb = up_many(up_many(up_many(v["base_M0"] + pb, 2) * (1.0 + eb), 3), 3)
        db = up_many(up_many(up_many(v["base_D2"] + pb2, 2) * (1.0 + eb2), 3), 3)
        mc = up_many(up_many(up_many(v["corr_M0"] + pc, 2) * (1.0 + ec), 3), 3)
        dc = up_many(up_many(up_many(v["corr_D2"] + pc2, 2) * (1.0 + ec2), 3), 3)
        tp2 = up_many((2.0 * math.pi) ** 2, 3)
        c1 = up_many(up_many(db * mc, 3) / tp2, 3)
        c2 = up_many(up_many(dc * mb, 3) / tp2, 3)
        rows.append({"j": j, "sigma": sigma, "point": v,
                     "panel": {"base_M0": pb, "base_D2": pb2,
                               "corr_M0": pc, "corr_D2": pc2},
                     "infl": {"base_M0": eb, "base_D2": eb2,
                              "corr_M0": ec, "corr_D2": ec2},
                     "norms": {"base_M0": mb, "base_D2": db,
                               "corr_M0": mc, "corr_D2": dc},
                     "C_channel_a": c1, "C_channel_b": c2,
                     "C_upper": min(c1, c2),
                     "binding": "a" if c1 <= c2 else "b",
                     "B_point": up_many(up_many(tp2 * min(c1, c2), 3), 3)})
    raw = json.loads((R / "2303_recon.json").read_text(encoding="utf-8"))["raw"]
    raw_by_sigma = {r["j"]: r for r in raw["rows"]}
    for r in rows:
        rr = raw_by_sigma[r["j"]]
        r["raw_check"] = {"raw_B": rr["B"],
                          "v_min_over_raw": min(r["norms"]["base_D2"]
                                                * r["norms"]["corr_M0"],
                                                r["norms"]["corr_D2"]
                                                * r["norms"]["base_M0"])
                          / rr["B"]}
    raw_upper_ok = all(r["raw_check"]["v_min_over_raw"] >= 1.0 for r in rows)
    raw_rel_max = max(abs(r["raw_check"]["v_min_over_raw"] - 1.0) for r in rows)
    max_row = max(rows, key=lambda r: r["B_point"])
    transfer = up_many(math.exp(2.0 * rmax * HALF_STEP), 4)
    sup_cert = up_many(up_many(max_row["B_point"] * transfer, 3), 3)
    anchors_ok = bool(raw_upper_ok and zero_free and
                      all(anchors[k] for k in ("families_bitwise",
                                               "base_bitwise", "corr_bitwise")))
    status = ("CORRECTED-STRIP-COVERED" if (anchors_ok and sup_cert <= FROZEN_B)
              else "STRIP-CONTROL-FAIL")
    result = {
        "record": 2303, "status": status,
        "owner": {"capture": OWNER_CAPTURE.name, "anchors": anchors,
                  "physical_profile": "phi_(a^2)(y) exp(i theta y)",
                  "families": 30, "rmax": rmax},
        "gate": {"zero_count": {k: v["verdict"] for k, v in pave.items()},
                 "edge": edge["verdict"], "zero_free": zero_free},
        "panel": {"law": "composite-EM (dx^2/12)(2 rmax) M_k(sigma), N_risk=0",
                  "ladder_base": ladder["base"], "ladder_corr": ladder["corr"]},
        "inflation": {"radii": {"base": R_BASE_2237, "corr": R_CORR_2237},
                      "law": "r * sum_f 2 a_f e^{|sigma| rmax} sup|phi^(k)|, "
                             "corrected radii"},
        "grid": {"x_nodes": NX, "dx": dx, "sigma_nodes": len(rows),
                 "half_step": HALF_STEP, "transfer": transfer},
        "centered": {"max_point_sigma": max_row["sigma"],
                     "max_point_B": max_row["B_point"],
                     "max_point_binding": max_row["binding"],
                     "sup_certified": sup_cert, "frozen": FROZEN_B,
                     "covered": sup_cert <= FROZEN_B,
                     "margin": FROZEN_B / sup_cert if sup_cert > 0 else None},
        "anchor_raw": {"rel_max": raw_rel_max, "upper_ok": raw_upper_ok},
        "grid_rows": rows,
        "nonclaims": [
            "artifact-grade reduction replay in the 2234/2242/2243 standard, "
            "not a Lean certificate",
            "the sigma-transfer is the log-derivative law |d/dsigma log N| "
            "<= 2 rmax at half-step 0.005; the certified sup is a grid "
            "maximum times e^{2 rmax h}, valid on the continuum but not tight",
            "the coefficient radii are the 2237 certified ones for the "
            "STORED coefficient vector; the corrected owner uses the same "
            "stored coefficients (2276)",
            "hgap, the infinite tail, the selected-owner readback and the "
            "signed producer margin remain open; no producer GO, no RH claim"],
        "provenance": {
            "script": "scripts/routea_corrected_strip_envelope_2303.py",
            "machinery": ["routea_weighted_zero_direct_product_outward_2234.py",
                          "routea_weighted_zero_panel_dx2_2238.py",
                          "routea_weighted_zero_zero_count_certificate_2242.py"],
            "owner": "results/2275_gap_owner_audit.json",
            "operands_anchor": "results/2267_replay_operands.json",
            "scale_audit": "docs/proofs/2276_routea_owner_scale_price.md"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "sup_certified": sup_cert,
                      "frozen": FROZEN_B, "covered": sup_cert <= FROZEN_B,
                      "margin": FROZEN_B / sup_cert,
                      "max_point_sigma": max_row["sigma"],
                      "max_point_binding": max_row["binding"],
                      "zero_free": zero_free,
                      "raw_rel_max": raw_rel_max,
                      "raw_upper_ok": raw_upper_ok,
                      "anchors_ok": anchors_ok}, indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "reduce")
    if mode == "recon":
        recon()
    elif mode == "chunk":
        chunk_worker(int(os.environ["CHUNK"]),
                     int(os.environ.get("NCHUNK", NCHUNK)))
    elif mode == "sigma":
        sigma_worker(int(os.environ["SIGMA_INDEX"]))
    elif mode.startswith("pave_"):
        pave_worker(mode[len("pave_"):])
    elif mode == "edge":
        edge_worker()
    elif mode == "reduce":
        reduce_worker()
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()