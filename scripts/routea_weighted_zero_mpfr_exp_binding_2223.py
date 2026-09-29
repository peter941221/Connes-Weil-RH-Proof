"""Record 2223: MPFR directed-rounding exp radius on the binding node.

The MPFR shared library is called directly through its stable C ABI.  All
exp/sin/cos calls use directed rounding at 256-bit precision; conversion to
binary64 bounds is also directed.  Scope: all 30 families, all GL and
Simpson points, binding node 2.  Input construction and summation remain
separate obligations.
"""
import ctypes as C
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sp = importlib.util.spec_from_file_location(
    "full2206", ROOT / "scripts" / "routea_weighted_zero_vector_split_full_refinement_2206.py")
parent = importlib.util.module_from_spec(sp)
sp.loader.exec_module(parent)

OUT = ROOT / "results" / "2223_mpfr_exp_binding.json"
NODE_INDEX = 2
PREC = 256
RNDD, RNDU = 3, 2
NSEG = 1100
NPAN = 12


class _M(C.Structure):
    _fields_ = [("prec", C.c_long), ("sign", C.c_int),
                ("exp", C.c_long), ("digits", C.POINTER(C.c_ulong))]


_P = C.POINTER(_M)
_lib = C.CDLL("libmpfr.so.6")
_lib.mpfr_init2.argtypes = [_P, C.c_long]
_lib.mpfr_clear.argtypes = [_P]
_lib.mpfr_set_d.argtypes = [_P, C.c_double, C.c_int]
_lib.mpfr_exp.argtypes = [_P, _P, C.c_int]
_lib.mpfr_sin.argtypes = [_P, _P, C.c_int]
_lib.mpfr_cos.argtypes = [_P, _P, C.c_int]
_lib.mpfr_mul.argtypes = [_P, _P, _P, C.c_int]
_lib.mpfr_get_d.argtypes = [_P, C.c_int]
_lib.mpfr_get_d.restype = C.c_double


class M:
    def __init__(self):
        self.x = _M()
        _lib.mpfr_init2(C.byref(self.x), PREC)

    def set_d(self, x):
        _lib.mpfr_set_d(C.byref(self.x), C.c_double(x), 0)

    def get_d(self, rnd):
        return float(_lib.mpfr_get_d(C.byref(self.x), rnd))

    def clear(self):
        _lib.mpfr_clear(C.byref(self.x))


def _unary(out, src, fn):
    fn(C.byref(out.x), C.byref(src.x), RNDD)
    lo = out.get_d(RNDD)
    fn(C.byref(out.x), C.byref(src.x), RNDU)
    hi = out.get_d(RNDU)
    return lo, hi


def _product_bounds(a, b, tmp):
    # a,b are (lower,upper) MPFR objects; return directed binary64 bounds of
    # their product interval by checking all endpoint products.
    vals_lo, vals_hi = [], []
    for x in a:
        for y in b:
            _lib.mpfr_mul(C.byref(tmp.x), C.byref(x.x), C.byref(y.x), RNDD)
            vals_lo.append(tmp.get_d(RNDD))
            _lib.mpfr_mul(C.byref(tmp.x), C.byref(x.x), C.byref(y.x), RNDU)
            vals_hi.append(tmp.get_d(RNDU))
    return min(vals_lo), max(vals_hi)


def _radius_pair(qr, qi, out_re, out_im, work):
    qre, qim, elo, ehi, clo, chi, slo, shi, tmp = work
    qre.set_d(qr)
    qim.set_d(qi)
    # Use two MPFR objects for each directed endpoint so products retain the
    # high-precision MPFR enclosure until final directed conversion.
    _lib.mpfr_exp(C.byref(elo.x), C.byref(qre.x), RNDD)
    _lib.mpfr_exp(C.byref(ehi.x), C.byref(qre.x), RNDU)
    _lib.mpfr_cos(C.byref(clo.x), C.byref(qim.x), RNDD)
    _lib.mpfr_cos(C.byref(chi.x), C.byref(qim.x), RNDU)
    _lib.mpfr_sin(C.byref(slo.x), C.byref(qim.x), RNDD)
    _lib.mpfr_sin(C.byref(shi.x), C.byref(qim.x), RNDU)
    re_lo, re_hi = _product_bounds((elo, ehi), (clo, chi), tmp)
    im_lo, im_hi = _product_bounds((elo, ehi), (slo, shi), tmp)
    vr, vi = float(np.real(out_re)), float(np.imag(out_im))
    rr = max(abs(vr - re_lo), abs(re_hi - vr))
    ri = max(abs(vi - im_lo), abs(im_hi - vi))
    # One outward binary64 step protects the subtraction/addition used to
    # form the radius itself.
    return math.nextafter(rr, math.inf), math.nextafter(ri, math.inf)


def main():
    nodes, fam, A0, _b, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    node = nodes[NODE_INDEX]
    xw = [parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
          for a, _ in fam]
    work = [M() for _ in range(9)]
    gl_charge = sim_charge = 0.0
    max_rr = max_ri = 0.0
    total_terms = 0
    family_rows = []
    try:
        for fi, (c, (a, theta), (X, W)) in enumerate(zip(coeff, fam, xw)):
            z = a * (node + 1j * theta)
            gl = 0.0
            for x, w in zip(X, W):
                q = -parent.v.q.r.K / (1.0 - (x / a) ** 2) + z * x
                f = np.exp(q)
                rr, ri = _radius_pair(float(np.real(q)), float(np.imag(q)),
                                      f, f, work)
                gl += abs(float(c)) * abs(float(w)) * (rr + ri)
                max_rr, max_ri = max(max_rr, rr), max(max_ri, ri)
            sim = 0.0
            lo_all, hi_all = -a * (1.0 - parent.DELTA), a * (1.0 - parent.DELTA)
            for panel in range(NPAN):
                lo = lo_all + (hi_all - lo_all) * panel / NPAN
                hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
                xx = np.linspace(lo, hi, 2 * NSEG + 1)
                hh = (hi - lo) / (2 * NSEG)
                weights = np.ones(len(xx))
                weights[1:-1:2] = 4.0
                weights[2:-1:2] = 2.0
                local = 0.0
                for x, weight in zip(xx, weights):
                    q = -parent.v.q.r.K / (1.0 - (x / a) ** 2) + z * x
                    f = np.exp(q)
                    rr, ri = _radius_pair(float(np.real(q)), float(np.imag(q)),
                                          f, f, work)
                    local += float(weight) * (rr + ri)
                    max_rr, max_ri = max(max_rr, rr), max(max_ri, ri)
                sim += abs(float(c)) * float(hh / 3.0) * local
            gl_charge += gl
            sim_charge += sim
            total_terms += len(X) + NPAN * (2 * NSEG + 1)
            family_rows.append({"family": fi, "gl_charge": gl,
                                "simpson_charge": sim, "total": gl + sim})
            print(f"family={fi} total={gl + sim:.17e}", flush=True)
    finally:
        for x in work:
            x.clear()
    result = {
        "record": 2223,
        "status": "MPFR-DIRECTED-EXP-RADIUS-BINDING-NODE",
        "backend": {"library": "libmpfr.so.6", "precision_bits": PREC,
                    "exp_sin_cos_rounding": "RNDD/RNDU",
                    "binary64_conversion": "RNDD/RNDU"},
        "scope": {"node_index": NODE_INDEX, "families": len(fam),
                  "NSEG": NSEG, "panels": NPAN, "terms": total_terms},
        "charge": {"gl": gl_charge, "simpson": sim_charge,
                    "total": gl_charge + sim_charge},
        "max_component_radius": {"real": max_rr, "imag": max_ri},
        "families": family_rows,
        "nonclaims": [
            "input exponent construction is not certified",
            "finite-sum accumulation is not certified",
            "other nodes and complete-owner transfer remain open",
            "no RH claim",
        ],
        "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)),
                       "target": "2220/2222 implementation-radius route"},
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 2223, "status": result["status"],
                      "charge": result["charge"],
                      "max_component_radius": result["max_component_radius"]},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()
