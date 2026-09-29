"""Record 2237: certified generation channel of the 2197 direct-product
system.

Record 2236 charged the coefficient channel at the solve floor
Ainv (resid + gamma_30 A_inf c_inf) and left the *generation* channel
screened at eta = 1e-12 (a relative screen on the matrix entries).  This
record replaces the screen with a measured per-entry bound.

Under convention A (record 2230) the operands are the stored binary64
tuple; the embedded-float ideal of a matrix entry is the exact real
arithmetic of the family_values formula on those stored inputs:

    A*[i, j] = a_j sum_p exp(-K/(1-(X_p/a_j)^2)) W_p exp(a_j (node_i
               + i theta_j) X_p)

where X_p, W_p are the stored composite-Gauss-Legendre nodes/weights and
node_i the stored owner node.  Every entry is recomputed in 256-bit MPFR
(RNDN terms, directed RNDU/RNDD accumulation, plus a 2^-200 magnitude-sum
slack), giving an outward interval around A*.  The measured deviation

    delta[i, j] = max(|Re A_bin64 - Re A*|, |Im A_bin64 - Im A*|)

(computed as a difference in MPFR, so no binary64 cancellation) is charged
through the coefficient channel as

    ||delta c_gen||_inf <= Ainv_inf * max_i sum_j |delta A[i, j]| |c_j|

and added to the 2236 solve floor:

    r_c = Ainv_inf (resid + gamma_30 A_inf c_inf
                    + (1 + guard) max_i sum_j |delta A[i,j]| |c_j|)

where guard covers the ||A*^-1||-vs-||A_b^-1|| gap (cond_inf times the
relative entry deviation).  The repriced envelope is written by the 2235
run_reduce machinery under both coefficient radii.

Modes (environment):
  MODE=dump                -> results/2237_operand_dump.npz (30 families,
                              nodes/values/a/theta/X/W; local-only, gitignored)
  MODE=family FAMILY_INDEX=j
                           -> results/2237_fam_j.json (column j: per-node
                              delta, magnitude sums, interval widths, and the
                              stored binary64 column for the bitwise gate)
  MODE=reduce              -> results/2237_generation_certificate.json

The reduce asserts the stored columns are bitwise those of the rebuilt
2197 matrix before any charging (A2 discipline).
"""
import ctypes as C
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
RNDN, RNDD, RNDU = 0, 3, 2
SLACK_EXP = -200
ETA_SCREEN = 1e-12
NGRID = 38400


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


m23 = _load("mpfr2223u", "routea_weighted_zero_mpfr_exp_binding_2223.py")
lib = m23._lib
M = m23.M
for name in ("mpfr_add", "mpfr_sub", "mpfr_mul", "mpfr_div"):
    getattr(lib, name).argtypes = [m23._P, m23._P, m23._P, C.c_int]
lib.mpfr_abs.argtypes = [m23._P, m23._P, C.c_int]


def dump_operands():
    """Rebuild the 2197 construction and dump the stored operand tuple."""
    s97 = _load("s97w", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    nodes, values, fam = s97.owner_family()
    xs, ws = [], []
    for a, _th in fam:
        X, W = s97.r59.phi_weights(a, panels=6, m=s97.M)
        assert X.shape[0] == NGRID
        xs.append(X)
        ws.append(W)
    out = R / "2237_operand_dump.npz"
    np.savez(out,
             nodes=np.asarray(nodes, complex),
             values=np.asarray(values, complex),
             fam_a=np.asarray([a for a, _ in fam], float),
             fam_theta=np.asarray([t for _, t in fam], float),
             X=np.asarray(xs), W=np.asarray(ws))
    print(json.dumps({"status": "OPERAND-DUMP-WRITTEN", "families": len(fam),
                      "grid": int(np.asarray(xs).shape[1]),
                      "md5": hashlib.md5(out.read_bytes()).hexdigest()}),
          flush=True)


def family_worker(fi):
    """Certified column fi of the 2197 matrix."""
    s97 = _load("s97f", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    z = np.load(R / "2237_operand_dump.npz")
    nodes = np.asarray(z["nodes"], complex)
    a = float(z["fam_a"][fi])
    th = float(z["fam_theta"][fi])
    X = np.asarray(z["X"][fi], float)
    W = np.asarray(z["W"][fi], float)
    K = float(s97.K)
    # stored binary64 column, bitwise the family_values call
    v_col = a * s97.r59.phi_laplace(a, K, a * (nodes + 1j * th), XW=(X, W))
    # objects
    Xm = [M() for _ in range(NGRID)]
    gm = [M() for _ in range(NGRID)]
    bX = [C.byref(o.x) for o in Xm]
    bg = [C.byref(o.x) for o in gm]
    t = [M() for _ in range(12)]
    bt = [C.byref(o.x) for o in t]
    acc = [M() for _ in range(5)]
    bacc = [C.byref(o.x) for o in acc]
    one = M()
    mK = M()
    slack_c = M()
    a_mp = M()
    b_slack = C.byref(slack_c.x)
    b_amp = C.byref(a_mp.x)
    Xl = X.tolist()
    Wl = W.tolist()
    mul, sub, div, ex, sn, cs, add = (lib.mpfr_mul, lib.mpfr_sub,
                                      lib.mpfr_div, lib.mpfr_exp,
                                      lib.mpfr_sin, lib.mpfr_cos,
                                      lib.mpfr_add)
    setd = lib.mpfr_set_d
    zero = C.c_double(0.0)
    try:
        setd(C.byref(one.x), C.c_double(1.0), RNDN)
        setd(C.byref(mK.x), C.c_double(-K), RNDN)
        setd(bt[10], C.c_double(a), RNDN)
        for p in range(NGRID):
            setd(bX[p], C.c_double(Xl[p]), RNDN)
            setd(bg[p], C.c_double(Wl[p]), RNDN)
            # u = X/a; d = 1 - u^2; g = exp(-K/d) * W
            div(bt[0], bX[p], bt[10], RNDN)
            mul(bt[1], bt[0], bt[0], RNDN)
            sub(bt[2], C.byref(one.x), bt[1], RNDN)
            div(bt[3], C.byref(mK.x), bt[2], RNDN)
            ex(bt[4], bt[3], RNDN)
            mul(bg[p], bg[p], bt[4], RNDN)
        # per node: z_re = a Re(node), z_im = a (Im(node) + theta)
        rows = []
        for i in range(30):
            node = complex(nodes[i])
            setd(bt[5], C.c_double(node.real), RNDN)
            mul(bt[6], bt[5], bt[10], RNDN)    # z_re
            setd(bt[7], C.c_double(node.imag + th), RNDN)
            mul(bt[8], bt[7], bt[10], RNDN)    # z_im
            for o in acc:
                setd(C.byref(o.x), zero, RNDN)
            for p in range(NGRID):
                mul(bt[0], bt[6], bX[p], RNDN)  # z_re X
                ex(bt[1], bt[0], RNDN)          # exp
                mul(bt[2], bt[8], bX[p], RNDN)  # z_im X
                sn(bt[3], bt[2], RNDN)
                cs(bt[4], bt[2], RNDN)
                mul(bt[0], bg[p], bt[1], RNDN)  # g exp
                mul(bt[1], bt[0], bt[4], RNDN)  # t_re
                mul(bt[2], bt[0], bt[3], RNDN)  # t_im
                add(bacc[0], bacc[0], bt[1], RNDD)
                add(bacc[1], bacc[1], bt[1], RNDU)
                add(bacc[2], bacc[2], bt[2], RNDD)
                add(bacc[3], bacc[3], bt[2], RNDU)
                mul(bt[3], bt[1], bt[1], RNDN)
                mul(bt[4], bt[2], bt[2], RNDN)
                add(bacc[4], bacc[4], bt[3], RNDU)
                add(bacc[4], bacc[4], bt[4], RNDU)
            s2 = acc[4].get_d(RNDU)
            # entry = a * sum; scale the directed accumulators (a > 0)
            mul(bacc[0], bacc[0], bt[10], RNDD)
            mul(bacc[1], bacc[1], bt[10], RNDU)
            mul(bacc[2], bacc[2], bt[10], RNDD)
            mul(bacc[3], bacc[3], bt[10], RNDU)
            # sum |t| <= a sqrt(N) sqrt(sum t^2); inflate
            s_bound = up_many(up_many(math.sqrt(NGRID), 2)
                              * up_many(math.sqrt(up_many(s2, 2)), 2), 2)
            s_bound = up_many(s_bound * a, 2)
            slack = up_many(up_many(s_bound, 2) * 2.0 ** SLACK_EXP, 2)
            setd(b_slack, C.c_double(slack), RNDN)
            # interval widths (MPFR differences, no cancellation)
            sub(bt[0], bacc[1], bacc[0], RNDN)
            sub(bt[1], bacc[3], bacc[2], RNDN)
            w_re = t[0].get_d(RNDU)
            w_im = t[1].get_d(RNDU)
            re_bin = float(v_col[i].real)
            im_bin = float(v_col[i].imag)
            setd(b_amp, C.c_double(re_bin), RNDN)
            # d1 = |a_bin - (re_lo - slack)|; d2 = |(re_up + slack) - a_bin|
            sub(bt[2], bacc[0], b_slack, RNDN)
            sub(bt[3], b_amp, bt[2], RNDN)
            lib.mpfr_abs(bt[4], bt[3], RNDN)
            add(bt[2], bacc[1], b_slack, RNDN)
            sub(bt[3], bt[2], b_amp, RNDN)
            lib.mpfr_abs(bt[3], bt[3], RNDN)
            d_re = max(t[4].get_d(RNDU), t[3].get_d(RNDU))
            setd(b_amp, C.c_double(im_bin), RNDN)
            sub(bt[2], bacc[2], b_slack, RNDN)
            sub(bt[3], b_amp, bt[2], RNDN)
            lib.mpfr_abs(bt[4], bt[3], RNDN)
            add(bt[2], bacc[3], b_slack, RNDN)
            sub(bt[3], bt[2], b_amp, RNDN)
            lib.mpfr_abs(bt[3], bt[3], RNDN)
            d_im = max(t[4].get_d(RNDU), t[3].get_d(RNDU))
            rows.append({
                "node": i,
                "delta": max(d_re, d_im),
                "delta_re": d_re, "delta_im": d_im,
                "S_bound": s_bound,
                "width_re": w_re, "width_im": w_im,
                "re_bin": re_bin, "im_bin": im_bin,
            })
    finally:
        for o in t + acc + [one, mK, slack_c, a_mp]:
            o.clear()
        for o in Xm + gm:
            o.clear()
    out = {"record": 2237, "family": fi, "a": a, "theta": th,
           "status": "MATRIX-COLUMN-CERTIFIED",
           "reading": "delta = |A_bin64 - exact real arithmetic of the "
                      "family_values formula on the stored inputs|, all in "
                      "256-bit MPFR; RNDN terms, RNDU/RNDD accumulation, "
                      "2^-200 magnitude-sum slack",
           "rows": rows}
    (R / f"2237_fam_{fi}.json").write_text(json.dumps(out, indent=2) + "\n",
                                           encoding="utf-8")
    print(json.dumps({"family": fi,
                      "delta_max": max(r["delta"] for r in rows),
                      "S_max": max(r["S_bound"] for r in rows)}), flush=True)


def load_system():
    """Rebuild the 2197 system; scales + coefficient vectors."""
    s97 = _load("s97s", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    z = np.load(R / "2237_operand_dump.npz")
    nodes = np.asarray(z["nodes"], complex)
    values = np.asarray(z["values"], complex)
    fam = list(zip(z["fam_a"].tolist(), z["fam_theta"].tolist()))
    xs = z["X"]
    ws = z["W"]
    for j, (a, _t) in enumerate(fam):
        Xr, Wr = s97.r59.phi_weights(a, panels=6, m=s97.M)
        assert np.array_equal(Xr, xs[j]) and np.array_equal(Wr, ws[j])
    XW = [(np.asarray(xs[j], float), np.asarray(ws[j], float))
          for j in range(len(fam))]
    a_mat = s97.r80.family_values(fam, s97.K, nodes, XW).T
    base = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr = np.linalg.solve(a_mat, np.asarray(values, complex))
    return fam, a_mat, base, corr


def reduce_worker():
    rp = _load("rp2235g", "routea_weighted_zero_direct_product_reprice_2235.py")
    fam, a_mat, base, corr = load_system()
    scales = rp.system_radii()
    assert float(np.linalg.norm(a_mat, ord=np.inf)) == scales["a_inf"]
    assert float(np.linalg.norm(base, ord=np.inf)) == scales["base_c_inf"]
    assert float(np.linalg.norm(corr, ord=np.inf)) == scales["corr_c_inf"]
    values = np.asarray(np.load(R / "2237_operand_dump.npz")["values"], complex)
    assert float(np.linalg.norm(a_mat @ base
                                - np.ones(30, complex),
                                ord=np.inf)) == scales["resid_base"]
    assert float(np.linalg.norm(a_mat @ corr - values,
                                ord=np.inf)) == scales["resid_corr"]
    mod = np.zeros((30, 30))
    wmax = 0.0
    s_over_abs = 0.0
    delta_max = 0.0
    argmax_delta = [0, 0]
    for fi in range(30):
        d = json.loads((R / f"2237_fam_{fi}.json").read_text(encoding="utf-8"))
        rows = d["rows"]
        assert len(rows) == 30
        re_bin = np.asarray([r["re_bin"] for r in rows], float)
        im_bin = np.asarray([r["im_bin"] for r in rows], float)
        assert np.array_equal(re_bin, a_mat[:, fi].real), ("bitwise gate", fi)
        assert np.array_equal(im_bin, a_mat[:, fi].imag), ("bitwise gate", fi)
        for r in rows:
            i = r["node"]
            mod[i, fi] = up_many(math.hypot(r["delta_re"], r["delta_im"]), 2)
            wmax = max(wmax, r["width_re"], r["width_im"])
            ab = math.hypot(r["re_bin"], r["im_bin"])
            if ab > 0:
                s_over_abs = max(s_over_abs, r["S_bound"] / ab)
            if r["delta"] > delta_max:
                delta_max = r["delta"]
                argmax_delta = [i, fi]
    abs_base = np.asarray([up_many(math.hypot(c.real, c.imag), 1)
                           for c in base])
    abs_corr = np.asarray([up_many(math.hypot(c.real, c.imag), 1)
                           for c in corr])
    row_b = mod @ abs_base
    row_c = mod @ abs_corr
    v_base = up_many(up_many(float(np.max(row_b)), 2) * (1.0 + 1e-12), 3)
    v_corr = up_many(up_many(float(np.max(row_c)), 2) * (1.0 + 1e-12), 3)
    imax_b = int(np.argmax(row_b))
    imax_c = int(np.argmax(row_c))
    a_inf = scales["a_inf"]
    gamma_lu_base = scales["gamma30"] * a_inf * scales["base_c_inf"]
    gamma_lu_corr = scales["gamma30"] * a_inf * scales["corr_c_inf"]
    v_screen_base = ETA_SCREEN * a_inf * scales["base_c_inf"]
    v_screen_corr = ETA_SCREEN * a_inf * scales["corr_c_inf"]
    rel_dev = delta_max / a_inf
    guard = up_many(1.0 + 10.0 * scales["cond_inf"] * (rel_dev
                                                       + scales["gamma30"]), 3)
    ainv = scales["ainv_inf"]
    gen_base = up_many(ainv * up_many(v_base * guard, 3), 3)
    gen_corr = up_many(ainv * up_many(v_corr * guard, 3), 3)
    radii = {"r_base": up_many(scales["r_base_floor"] + gen_base, 3),
             "r_corr": up_many(scales["r_corr_floor"] + gen_corr, 3)}
    extra = {
        "generation_certificate": {
            "reading": "delta = |A_bin64 - A*| per entry; A* = exact real "
                       "arithmetic of family_values on the stored binary64 "
                       "inputs (X, W, a, theta, node, K); 256-bit MPFR, "
                       "RNDN terms, RNDU/RNDD accumulation, 2^-200 "
                       "magnitude-sum slack",
            "entries": 900,
            "delta_max": delta_max,
            "delta_max_at": argmax_delta,
            "delta_max_over_a_inf": rel_dev,
            "S_over_abs_max": s_over_abs,
            "interval_halfwidth_max": wmax,
            "slack_scale": 2.0 ** SLACK_EXP,
            "v_base": v_base, "v_corr": v_corr,
            "v_base_argmax_node": imax_b,
            "v_corr_argmax_node": imax_c,
            "v_screen_eta_1e_12_base": v_screen_base,
            "v_screen_eta_1e_12_corr": v_screen_corr,
            "cert_over_screen_base": v_base / v_screen_base,
            "cert_over_screen_corr": v_corr / v_screen_corr,
            "gamma_lu_term_base": gamma_lu_base,
            "gamma_lu_term_corr": gamma_lu_corr,
            "gen_radius_base": gen_base,
            "gen_radius_corr": gen_corr,
            "floor_base": scales["r_base_floor"],
            "floor_corr": scales["r_corr_floor"],
            "radius_guard": guard,
        },
        "bitwise_columns_verified": 30,
        "system": {k: scales[k] for k in
                   ("a_inf", "ainv_inf", "cond_inf", "base_c_inf",
                    "corr_c_inf", "resid_base", "resid_corr", "gamma30")},
    }
    result = rp.run_reduce(radii, 2237,
                           "certified generation channel: measured per-entry "
                           "|A_bin64 - A*| charged through the coefficient "
                           "radius on top of the 2236 solve floor",
                           "2237_generation_certificate.json",
                           "DIRECT-PRODUCT-GENERATION-CERTIFIED", extra=extra)
    print(json.dumps({"status": result["status"],
                      "C_upper": result["screen"]["C_upper"],
                      "tail_over_margin":
                          result["screen"]["tail_upper_over_margin"],
                      "delta_max": delta_max, "v_corr": v_corr,
                      "cert_over_screen_corr": v_corr / v_screen_corr},
                     indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "reduce")
    if mode == "dump":
        dump_operands()
    elif mode == "family":
        family_worker(int(os.environ["FAMILY_INDEX"]))
    elif mode == "reduce":
        reduce_worker()
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()