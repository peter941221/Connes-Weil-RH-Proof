"""Record 2225: MPFR interval certificate for q construction at node 2.

Every scalar operation in q=-K/(1-(x/a)^2)+z*x is enclosed with MPFR
directed rounding from binary64 inputs. The resulting q radius is propagated
through the analytic exp Lipschitz bound.
"""
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "mpfr2223", ROOT / "scripts" / "routea_weighted_zero_mpfr_exp_binding_2223.py")
m = importlib.util.module_from_spec(sp)
sp.loader.exec_module(m)
lib = m._lib
for name in ("mpfr_add", "mpfr_sub", "mpfr_div"):
    getattr(lib, name).argtypes = [m._P, m._P, m._P, m.C.c_int]
parent = m.parent
NODE_INDEX = int(os.environ.get("NODE_INDEX", "2"))
OUT = ROOT / "results" / os.environ.get(
    "Q_OUT", "2225_q_mpfr_interval_binding.json")
RECORD = int(os.environ.get("RECORD", "2225"))
NSEG, NPAN = 1100, 12


def _op_bounds(fn, aa, bb, scratch):
    lows, highs = [], []
    for x in aa:
        for y in bb:
            scratch[0].set_d(x)
            scratch[1].set_d(y)
            fn(m.C.byref(scratch[2].x), m.C.byref(scratch[0].x),
               m.C.byref(scratch[1].x), m.RNDD)
            lows.append(scratch[2].get_d(m.RNDD))
            fn(m.C.byref(scratch[2].x), m.C.byref(scratch[0].x),
               m.C.byref(scratch[1].x), m.RNDU)
            highs.append(scratch[2].get_d(m.RNDU))
    return (math.nextafter(min(lows), -math.inf),
            math.nextafter(max(highs), math.inf))


def q_interval(K, a, theta, node, x, scratch):
    p = lambda v: (float(v), float(v))
    add, sub, mul, div = (lib.mpfr_add, lib.mpfr_sub,
                          lib.mpfr_mul, lib.mpfr_div)
    ratio = _op_bounds(div, p(x), p(a), scratch)
    square = _op_bounds(mul, ratio, ratio, scratch)
    den = _op_bounds(sub, p(1.0), square, scratch)
    term = _op_bounds(div, p(-K), den, scratch)
    theta_sum = _op_bounds(add, p(float(np.imag(node))), p(theta), scratch)
    zre = _op_bounds(mul, p(a), p(float(np.real(node))), scratch)
    zim = _op_bounds(mul, p(a), theta_sum, scratch)
    prod_re = _op_bounds(mul, zre, p(x), scratch)
    prod_im = _op_bounds(mul, zim, p(x), scratch)
    return _op_bounds(add, term, prod_re, scratch), prod_im


def radius(iv, value):
    return math.nextafter(max(abs(value - iv[0]), abs(iv[1] - value)), math.inf)


def exp_difference_bound(qr, delta):
    """All-delta bound for |exp(q+δ)-exp(q)|, avoiding the δ<=1 lemma."""
    if delta == 0.0:
        return 0.0
    if delta < 1.0:
        return math.nextafter(2.0 * math.exp(qr) * delta, math.inf)
    # exp(qr) * expm1(delta), evaluated in the log domain to avoid a false
    # overflow/underflow verdict at the endpoint panels.
    log_expm1 = delta if delta > 50.0 else math.log(math.expm1(delta))
    log_bound = qr + log_expm1
    if log_bound < math.log(float.fromhex("0x0.0000000000001p-1022")):
        return 0.0
    if log_bound > math.log(float.fromhex("0x1.fffffffffffffp1023")):
        return math.inf
    return math.nextafter(math.exp(log_bound), math.inf)


def main():
    nodes, fam, A0, _b, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    node = nodes[NODE_INDEX]
    xw = [parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
          for a, _ in fam]
    scratch = [m.M() for _ in range(3)]
    total_charge = 0.0
    max_qre = max_qim = 0.0
    failures = terms = 0
    rows = []
    try:
        for fi, (c, (a, theta), (X, W)) in enumerate(zip(coeff, fam, xw)):
            z = a * (node + 1j * theta)
            gl = 0.0
            for x, w in zip(X, W):
                q = -parent.v.q.r.K / (1.0 - (x / a) ** 2) + z * x
                qr, qi = float(np.real(q)), float(np.imag(q))
                ir, ii = q_interval(parent.v.q.r.K, a, theta, node, float(x), scratch)
                rr, ri = radius(ir, qr), radius(ii, qi)
                failures += not (ir[0] <= qr <= ir[1] and ii[0] <= qi <= ii[1])
                gl += abs(c) * abs(w) * exp_difference_bound(qr, rr + ri)
                max_qre, max_qim = max(max_qre, rr), max(max_qim, ri)
            sim = 0.0
            lo_all, hi_all = -a * (1.0 - parent.DELTA), a * (1.0 - parent.DELTA)
            for panel in range(NPAN):
                lo = lo_all + (hi_all - lo_all) * panel / NPAN
                hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
                xx = np.linspace(lo, hi, 2 * NSEG + 1)
                weights = np.ones(len(xx))
                weights[1:-1:2] = 4.0
                weights[2:-1:2] = 2.0
                local = 0.0
                for x, weight in zip(xx, weights):
                    q = -parent.v.q.r.K / (1.0 - (x / a) ** 2) + z * x
                    qr, qi = float(np.real(q)), float(np.imag(q))
                    ir, ii = q_interval(parent.v.q.r.K, a, theta, node, float(x), scratch)
                    rr, ri = radius(ir, qr), radius(ii, qi)
                    failures += not (ir[0] <= qr <= ir[1] and ii[0] <= qi <= ii[1])
                    local += float(weight) * exp_difference_bound(qr, rr + ri)
                    max_qre, max_qim = max(max_qre, rr), max(max_qim, ri)
                sim += abs(c) * float((hi - lo) / (2 * NSEG) / 3.0) * local
            total_charge += gl + sim
            terms += len(X) + NPAN * (2 * NSEG + 1)
            rows.append({"family": fi, "gl": gl, "simpson": sim, "total": gl + sim})
            print(f"family={fi} total={gl + sim:.17e}", flush=True)
    finally:
        for x in scratch:
            x.clear()
    result = {
        "record": RECORD,
        "status": "MPFR-Q-INTERVAL-BINDING-NODE",
        "backend": {"library": "libmpfr.so.6", "precision_bits": m.PREC,
                    "rounding": "RNDD/RNDU; binary64 conversion directed"},
        "scope": {"node_index": NODE_INDEX, "families": len(fam),
                  "NSEG": NSEG, "panels": NPAN, "terms": terms},
        "q_interval": {"operation": "IEEE correctly-rounded scalar operations",
                        "failures": failures, "max_real_radius": max_qre,
                        "max_imag_radius": max_qim},
        "exp_lipschitz_charge": total_charge, "rows": rows,
        "nonclaims": ["binary64 inputs are taken as exact operands",
                      "finite-sum accumulation and other nodes remain open",
                      "no complete-owner transfer and no RH claim"],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "theorem_interface": "2212/2213 exp perturbation bound"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": RECORD, "status": result["status"],
                      "failures": failures,
                      "exp_lipschitz_charge": total_charge,
                      "max_q_radius": max(max_qre, max_qim)}, indent=2), flush=True)


if __name__ == "__main__":
    main()
