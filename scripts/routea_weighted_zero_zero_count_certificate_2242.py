"""Record 2242: certified zero count Z = 0 for the four channel functions.

The 2238 composite-trapezoid identity prices the panel over [x_0, x_N] as

    |T - I| <= (dx^2/12) ( sum_{kinks of g'} J + TV(g') ),
    TV(g') <= int |g''| + sum J,   J <= 2 |h_k'(x*)| e^{sigma x*},

where g = |h_k| e^{sigma x} and the kinks sit at the real zeros x* of
h_k.  The 2238 record could only certify zero-free cells through the global
node test |h_k(x_p)| > dx m_{k+1}, a wall that left 76-87% of cells as
risk cells.  This record certifies, in directed 256-bit MPFR, that each of
the four channel functions

    h_0 = F   = sum_j c_j phi(x/a_j) e^{i theta_j x}
    h_2 = F'' = sum_j c_j phi(x/a_j) B2_j(x) e^{i theta_j x},
    B2_j = e1_j^2 + e2_j + 2 i theta_j e1_j - theta_j^2,

has NO real zero in (-a30, a30), a30 = max a_j.  Z = 0 removes every kink
from the composite-trapezoid identity: |h_k| is C^infinity on R, and the
panel collapses to the clean composite-EM term (dx^2/12)(2 a_max) M_k
(priced in record 2243).

Method:
  * interior pavement on [-a29, a29] (a29 the second largest distinct a_j):
    natural interval extension of h_k over boxes, all arithmetic in
    directed 256-bit MPFR (RNDD/RNDU), constants RNDN (about half an ulp);
    the final hull is expanded 32 ulp to absorb constant rounding, then a
    certified no-zero box needs the real or the imaginary interval to
    exclude 0.  Boxes are bisected on failure.  For h_2 the e1^2 + e2
    cancellation is removed by the exact factorization

      e1^2 + e2 = (2K/a^2) G2(q) q^{-4},  G2(q) = 2K - (2K+4) q + 3 q^2,

    and every phi-carrying piece is bounded by its monotone (sup at q_hi)
    form, so no interval blows up at the breakpoints.
  * edge arcs (+-)(a29, a30): the only active family is a30 (all others
    have support |x| <= a29), phi > 0 strictly on the open arc, so
      - k = 0: h_0 = c30 phi e^{i theta x} != 0 whenever c30 != 0;
      - k = 2: B2_re(q) = (2K/a^2) G2(q) q^{-4} - theta^2 is decreasing
        in q on the arc (verified), so the single scalar bound
        LB = (2K/a30^2) G2(q29u) q29u^{-4} - theta^2 > 0 with
        q29u >= q(+-a29) certifies B2 != 0 on the whole open arc,
        including arbitrary slivers at +-a30.
  * boundary zeros at +-a30 are flat (all phi derivatives vanish at
    |u| = 1, the C^infinity extension), so g'(+-a_max) = 0 exactly and
    they contribute no kink mass (the 2238 identity already uses this).

The float64 denormal artifacts near |x| ~ 2.5079 (the phi-tail crossing of
the a = 2.56 family, e^{-K/q} ~ 1e-310) sit inside the edge arc and are
bypassed by the analytic edge certificate; the pavement never touches
them.  The float64 arrays are used for sizing only.

Modes (environment):
  MODE=smoke         -> results/2242_smoke.json (identity + containment)
  MODE=pave_<name>   -> results/2242_pave_<name>.json   (4 channels)
  MODE=edge          -> results/2242_edge.json
  MODE=reduce        -> results/2242_zero_count_certificate.json
"""
import bisect
import ctypes as C
import importlib.util
import json
import math
import os
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
RNDN, RNDD, RNDU = 0, 3, 2
K_BIND = 30.0
MAXDEPTH = 48
NXW = 240001


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------- MPFR glue
m23 = _load("mpfr2223z", "routea_weighted_zero_mpfr_exp_binding_2223.py")
lib = m23._lib
M = m23.M
_P = m23._P
for _n in ("mpfr_add", "mpfr_sub", "mpfr_mul", "mpfr_div"):
    getattr(lib, _n).argtypes = [_P, _P, _P, C.c_int]
for _n in ("mpfr_set", "mpfr_neg", "mpfr_sqrt", "mpfr_abs"):
    getattr(lib, _n).argtypes = [_P, _P, C.c_int]
lib.mpfr_cmp.argtypes = [_P, _P]
lib.mpfr_cmp.restype = C.c_int
lib.mpfr_nextbelow.argtypes = [_P]
lib.mpfr_nextabove.argtypes = [_P]
ADD, SUB = lib.mpfr_add, lib.mpfr_sub
MUL, DIV = lib.mpfr_mul, lib.mpfr_div
SET, NEG, SQRT = lib.mpfr_set, lib.mpfr_neg, lib.mpfr_sqrt
EXP, SIN, COS = lib.mpfr_exp, lib.mpfr_sin, lib.mpfr_cos
CMP = lib.mpfr_cmp
BR = C.byref
NOZERO_ULPS = 32
# Public binary64 endpoints need a separately priced outward margin.  This is
# intentionally a named knob: the mpmath containment control is allowed to
# decide whether the current margin is sufficient.
PUBLIC_HULL_ULPS = 4


def mk(v):
    o = M()
    o.set_d(float(v))
    return o


ZERO = mk(0.0)
ONE = mk(1.0)
MK30 = mk(-K_BIND)
SIXTY = mk(60.0)
C64 = mk(64.0)
THREE = mk(3.0)
EIGHTH = mk(0.125)
ONE_P = mk(1.0 + 2.0 ** -100)
EPS200 = mk(2.0 ** -200)


def icmp(a, b):
    return CMP(BR(a.x), BR(b.x))


def imin(out, a, b):
    SET(BR(out.x), BR((a if icmp(a, b) <= 0 else b).x), RNDN)


def imax(out, a, b):
    SET(BR(out.x), BR((a if icmp(a, b) >= 0 else b).x), RNDN)


def iprod(lo, hi, alo, ahi, blo, bhi, T):
    """Outward interval product [alo,ahi]*[blo,bhi] -> (lo, hi)."""
    t0, t1, t2, t3 = T[60], T[61], T[62], T[63]
    MUL(BR(t0.x), BR(alo.x), BR(blo.x), RNDD)
    MUL(BR(t1.x), BR(alo.x), BR(bhi.x), RNDD)
    MUL(BR(t2.x), BR(ahi.x), BR(blo.x), RNDD)
    MUL(BR(t3.x), BR(ahi.x), BR(bhi.x), RNDD)
    imin(lo, t0, t1)
    imin(lo, lo, t2)
    imin(lo, lo, t3)
    MUL(BR(t0.x), BR(alo.x), BR(blo.x), RNDU)
    MUL(BR(t1.x), BR(alo.x), BR(bhi.x), RNDU)
    MUL(BR(t2.x), BR(ahi.x), BR(blo.x), RNDU)
    MUL(BR(t3.x), BR(ahi.x), BR(bhi.x), RNDU)
    imax(hi, t0, t1)
    imax(hi, hi, t2)
    imax(hi, hi, t3)


def ciprod(rlo, rhi, ilo, ihi, alo, ahi, blo, bhi, plo, phi, qlo, qhi, T):
    """Outward complex interval product (A+iB)(P+iQ) -> (rlo..ihi)."""
    p1, p2, q1, q2 = T[52], T[53], T[54], T[55]
    iprod(p1, p2, alo, ahi, plo, phi, T)
    iprod(q1, q2, blo, bhi, qlo, qhi, T)
    SUB(BR(rlo.x), BR(p1.x), BR(q2.x), RNDD)
    SUB(BR(rhi.x), BR(p2.x), BR(q1.x), RNDU)
    iprod(p1, p2, alo, ahi, qlo, qhi, T)
    iprod(q1, q2, blo, bhi, plo, phi, T)
    ADD(BR(ilo.x), BR(p1.x), BR(q1.x), RNDD)
    ADD(BR(ihi.x), BR(p2.x), BR(q2.x), RNDU)


class Kernel:
    """Certified interval evaluator for one channel (k in {0, 2})."""

    def __init__(self, fam, coef, k):
        self.k = k
        self.recs = []
        for (a, th), c in zip(fam, coef):
            cr, ci = float(np.real(c)), float(np.imag(c))
            if cr == 0.0 and ci == 0.0:
                continue
            rec = {"a": mk(a), "th": mk(th), "th_abs": mk(abs(th)),
                   "cre": mk(cr), "cim": mk(ci)}
            d_lo = M()
            d_hi = M()
            MUL(BR(d_lo.x), BR(rec["a"].x), BR(rec["a"].x), RNDD)
            MUL(BR(d_hi.x), BR(rec["a"].x), BR(rec["a"].x), RNDU)
            s2a2_lo = M()
            s2a2_hi = M()
            DIV(BR(s2a2_lo.x), BR(SIXTY.x), BR(d_hi.x), RNDD)
            DIV(BR(s2a2_hi.x), BR(SIXTY.x), BR(d_lo.x), RNDU)
            rec["s2a2_lo"] = s2a2_lo
            rec["s2a2_hi"] = s2a2_hi
            invd = M()
            DIV(BR(invd.x), BR(ONE.x), BR(rec["a"].x), RNDD)
            rec["inv_d"] = invd
            invu = M()
            DIV(BR(invu.x), BR(ONE.x), BR(rec["a"].x), RNDU)
            rec["inv_u"] = invu
            if k == 2:
                t2_lo = M()
                t2_hi = M()
                MUL(BR(t2_lo.x), BR(rec["th"].x), BR(rec["th"].x), RNDD)
                MUL(BR(t2_hi.x), BR(rec["th"].x), BR(rec["th"].x), RNDU)
                rec["t2_lo"] = t2_lo
                rec["t2_hi"] = t2_hi
                mr_lo = M()
                mr_hi = M()
                t120 = mk(-120.0)
                MUL(BR(mr_lo.x), BR(t120.x), BR(rec["th"].x), RNDD)
                MUL(BR(mr_hi.x), BR(t120.x), BR(rec["th"].x), RNDU)
                fq_lo = M()
                fq_hi = M()
                DIV(BR(fq_lo.x), BR(mr_lo.x), BR(rec["a"].x), RNDD)
                DIV(BR(fq_hi.x), BR(mr_hi.x), BR(rec["a"].x), RNDU)
                rec["fq_lo"] = fq_lo
                rec["fq_hi"] = fq_hi
            self.recs.append(rec)
        self.T = [M() for _ in range(64)]
        self.acc = [M() for _ in range(4)]

    def eval_box(self, xlo, xhi, geometry_cache=None):
        """Return (no_zero, (rlo, rhi, ilo, ihi) as floats, floor)."""
        T = self.T
        acc = self.acc
        k = self.k
        for o in acc:
            SET(BR(o.x), BR(ZERO.x), RNDN)
        xlo_m, xhi_m = T[0], T[1]
        xlo_m.set_d(xlo)
        xhi_m.set_d(xhi)
        u_lo, u_hi = T[2], T[3]
        absl, absh = T[4], T[5]
        amax_, amin_ = T[6], T[7]
        smax, smin = T[8], T[9]
        tq, qL, qH = T[10], T[11], T[12]
        philo, phihi = T[13], T[14]
        cLo, cHi, sLo, sHi = T[34], T[35], T[36], T[37]
        # |endpoints|
        if xlo < 0.0:
            NEG(BR(absl.x), BR(xlo_m.x), RNDN)
        else:
            SET(BR(absl.x), BR(xlo_m.x), RNDN)
        if xhi < 0.0:
            NEG(BR(absh.x), BR(xhi_m.x), RNDN)
        else:
            SET(BR(absh.x), BR(xhi_m.x), RNDN)
        imax(amax_, absl, absh)
        imin(amin_, absl, absh)
        for rec_index, rec in enumerate(self.recs):
            cached = (geometry_cache[rec_index]
                      if geometry_cache is not None else None)
            if cached is None:
                if xlo >= 0.0:
                    MUL(BR(u_lo.x), BR(xlo_m.x), BR(rec["inv_d"].x), RNDD)
                else:
                    MUL(BR(u_lo.x), BR(xlo_m.x), BR(rec["inv_u"].x), RNDD)
                if xhi >= 0.0:
                    MUL(BR(u_hi.x), BR(xhi_m.x), BR(rec["inv_u"].x), RNDU)
                else:
                    MUL(BR(u_hi.x), BR(xhi_m.x), BR(rec["inv_d"].x), RNDU)
                MUL(BR(smax.x), BR(amax_.x), BR(rec["inv_u"].x), RNDU)
                MUL(BR(smin.x), BR(amin_.x), BR(rec["inv_d"].x), RNDD)
                MUL(BR(tq.x), BR(smax.x), BR(smax.x), RNDU)
                SUB(BR(qL.x), BR(ONE.x), BR(tq.x), RNDD)
                if xlo <= 0.0 <= xhi:
                    SET(BR(qH.x), BR(ONE.x), RNDN)
                else:
                    MUL(BR(tq.x), BR(smin.x), BR(smin.x), RNDD)
                    SUB(BR(qH.x), BR(ONE.x), BR(tq.x), RNDU)
                if icmp(qH, ZERO) <= 0:
                    if geometry_cache is not None:
                        geometry_cache[rec_index] = None
                    continue
                DIV(BR(tq.x), BR(MK30.x), BR(qH.x), RNDU)
                EXP(BR(phihi.x), BR(tq.x), RNDU)
                if icmp(qL, ZERO) > 0:
                    DIV(BR(tq.x), BR(MK30.x), BR(qL.x), RNDD)
                    EXP(BR(philo.x), BR(tq.x), RNDD)
                else:
                    SET(BR(philo.x), BR(ZERO.x), RNDN)
                # arc of e^{i theta x} over the box (endpoints + delta)
                p1, p2 = T[15], T[16]
                MUL(BR(p1.x), BR(rec["th"].x), BR(xlo_m.x), RNDD)
                # The second endpoint is the upper side of the product
                # enclosure.  Using RNDD here leaves the exact endpoint
                # outside the angle interval at a point box, which is
                # visible only at cancellation-scale imaginary parts.
                MUL(BR(p2.x), BR(rec["th"].x), BR(xhi_m.x), RNDU)
                thmin, thmax = T[17], T[18]
                imin(thmin, p1, p2)
                imax(thmax, p1, p2)
                c1d, c2d, c1u, c2u = T[19], T[20], T[21], T[22]
                s1d, s2d, s1u, s2u = T[23], T[24], T[25], T[26]
                COS(BR(c1d.x), BR(thmin.x), RNDD)
                COS(BR(c2d.x), BR(thmax.x), RNDD)
                COS(BR(c1u.x), BR(thmin.x), RNDU)
                COS(BR(c2u.x), BR(thmax.x), RNDU)
                SIN(BR(s1d.x), BR(thmin.x), RNDD)
                SIN(BR(s2d.x), BR(thmax.x), RNDD)
                SIN(BR(s1u.x), BR(thmin.x), RNDU)
                SIN(BR(s2u.x), BR(thmax.x), RNDU)
                cLo_p, cHi_p = T[27], T[28]
                sLo_p, sHi_p = T[29], T[30]
                imin(cLo_p, c1d, c2d)
                imax(cHi_p, c1u, c2u)
                imin(sLo_p, s1d, s2d)
                imax(sHi_p, s1u, s2u)
                xw, tw, dlt = T[31], T[32], T[33]
                SUB(BR(xw.x), BR(xhi_m.x), BR(xlo_m.x), RNDU)
                MUL(BR(tw.x), BR(rec["th_abs"].x), BR(xw.x), RNDU)
                MUL(BR(dlt.x), BR(tw.x), BR(tw.x), RNDU)
                MUL(BR(dlt.x), BR(dlt.x), BR(EIGHTH.x), RNDU)
                MUL(BR(dlt.x), BR(dlt.x), BR(ONE_P.x), RNDU)
                ADD(BR(dlt.x), BR(dlt.x), BR(EPS200.x), RNDU)
                SUB(BR(cLo.x), BR(cLo_p.x), BR(dlt.x), RNDD)
                ADD(BR(cHi.x), BR(cHi_p.x), BR(dlt.x), RNDU)
                SUB(BR(sLo.x), BR(sLo_p.x), BR(dlt.x), RNDD)
                ADD(BR(sHi.x), BR(sHi_p.x), BR(dlt.x), RNDU)
                if geometry_cache is not None:
                    geometry_cache[rec_index] = (
                        u_lo.get_d(RNDD), u_hi.get_d(RNDU),
                        qL.get_d(RNDD), qH.get_d(RNDU),
                        philo.get_d(RNDD), phihi.get_d(RNDU),
                        cLo.get_d(RNDD), cHi.get_d(RNDU),
                        sLo.get_d(RNDD), sHi.get_d(RNDU))
            else:
                (u_lo_v, u_hi_v, qL_v, qH_v, philo_v, phihi_v,
                 cLo_v, cHi_v, sLo_v, sHi_v) = cached
                u_lo.set_d(u_lo_v)
                u_hi.set_d(u_hi_v)
                qL.set_d(qL_v)
                qH.set_d(qH_v)
                philo.set_d(philo_v)
                phihi.set_d(phihi_v)
                cLo.set_d(cLo_v)
                cHi.set_d(cHi_v)
                sLo.set_d(sLo_v)
                sHi.set_d(sHi_v)
            if k == 0:
                reL, reH, imL, imH = T[38], T[39], T[40], T[41]
                iprod(reL, reH, cLo, cHi, philo, phihi, T)
                iprod(imL, imH, sLo, sHi, philo, phihi, T)
                trl, trh, til, tih = T[42], T[43], T[44], T[45]
                ciprod(trl, trh, til, tih, rec["cre"], rec["cre"],
                       rec["cim"], rec["cim"], reL, reH, imL, imH, T)
            else:
                q2, q4 = T[38], T[39]
                f2L, f2H, f4L, f4H = T[40], T[41], T[42], T[43]
                MUL(BR(q2.x), BR(qH.x), BR(qH.x), RNDD)
                DIV(BR(f2H.x), BR(phihi.x), BR(q2.x), RNDU)
                MUL(BR(q4.x), BR(q2.x), BR(q2.x), RNDD)
                DIV(BR(f4H.x), BR(phihi.x), BR(q4.x), RNDU)
                if icmp(qL, ZERO) > 0:
                    MUL(BR(q2.x), BR(qL.x), BR(qL.x), RNDU)
                    DIV(BR(f2L.x), BR(philo.x), BR(q2.x), RNDD)
                    MUL(BR(q4.x), BR(q2.x), BR(q2.x), RNDU)
                    DIV(BR(f4L.x), BR(philo.x), BR(q4.x), RNDD)
                else:
                    SET(BR(f2L.x), BR(ZERO.x), RNDN)
                    SET(BR(f4L.x), BR(ZERO.x), RNDN)
                g2lo, g2hi = T[44], T[45]
                MUL(BR(tq.x), BR(C64.x), BR(qH.x), RNDU)
                SUB(BR(g2lo.x), BR(SIXTY.x), BR(tq.x), RNDD)
                if icmp(qL, ZERO) > 0:
                    MUL(BR(tq.x), BR(C64.x), BR(qL.x), RNDD)
                    SUB(BR(g2hi.x), BR(SIXTY.x), BR(tq.x), RNDU)
                    MUL(BR(tq.x), BR(qL.x), BR(qL.x), RNDD)
                else:
                    SET(BR(g2hi.x), BR(SIXTY.x), RNDN)
                    SET(BR(tq.x), BR(ZERO.x), RNDN)
                MUL(BR(tq.x), BR(THREE.x), BR(tq.x), RNDD)
                ADD(BR(g2lo.x), BR(g2lo.x), BR(tq.x), RNDD)
                MUL(BR(tq.x), BR(qH.x), BR(qH.x), RNDU)
                MUL(BR(tq.x), BR(THREE.x), BR(tq.x), RNDU)
                ADD(BR(g2hi.x), BR(g2hi.x), BR(tq.x), RNDU)
                prL, prH = T[46], T[47]
                iprod(prL, prH, g2lo, g2hi, f4L, f4H, T)
                P_lo, P_hi = T[48], T[49]
                iprod(P_lo, P_hi, rec["s2a2_lo"], rec["s2a2_hi"],
                      prL, prH, T)
                iprod(q2, q4, rec["t2_lo"], rec["t2_hi"],
                      philo, phihi, T)
                SUB(BR(P_lo.x), BR(P_lo.x), BR(q2.x), RNDD)
                SUB(BR(P_hi.x), BR(P_hi.x), BR(q4.x), RNDU)
                rl_, rh_ = T[50], T[51]
                iprod(rl_, rh_, u_lo, u_hi, f2L, f2H, T)
                Q_lo, Q_hi = T[46], T[47]
                iprod(Q_lo, Q_hi, rec["fq_lo"], rec["fq_hi"],
                      rl_, rh_, T)
                reL, reH, imL, imH = T[38], T[39], T[40], T[41]
                ciprod(reL, reH, imL, imH, cLo, cHi, sLo, sHi,
                       P_lo, P_hi, Q_lo, Q_hi, T)
                trl, trh, til, tih = T[42], T[43], T[44], T[45]
                ciprod(trl, trh, til, tih, rec["cre"], rec["cre"],
                       rec["cim"], rec["cim"], reL, reH, imL, imH, T)
            ADD(BR(acc[0].x), BR(acc[0].x), BR(trl.x), RNDD)
            ADD(BR(acc[1].x), BR(acc[1].x), BR(trh.x), RNDU)
            ADD(BR(acc[2].x), BR(acc[2].x), BR(til.x), RNDD)
            ADD(BR(acc[3].x), BR(acc[3].x), BR(tih.x), RNDU)
        # Preserve the hull direction: lower endpoints move downward and
        # upper endpoints move upward.  Moving every accumulator below can
        # narrow the returned box at cancellation-scale values.
        for o in (acc[0], acc[2]):
            for _ in range(NOZERO_ULPS):
                lib.mpfr_nextbelow(o.x)
        for o in (acc[1], acc[3]):
            for _ in range(NOZERO_ULPS):
                lib.mpfr_nextabove(o.x)
        # The public evaluator returns binary64 endpoints.  MPFR ulps are
        # far finer than a binary64 ulp at cancellation-scale values, so the
        # directed MPFR-to-float conversion needs one explicit outward step
        # after get_d; otherwise the rounded double can still undercut the
        # exact high-precision value by a few 1e-33.
        lo_r = acc[0].get_d(RNDD)
        hi_r = acc[1].get_d(RNDU)
        lo_i = acc[2].get_d(RNDD)
        hi_i = acc[3].get_d(RNDU)
        for _ in range(PUBLIC_HULL_ULPS):
            lo_r = float(np.nextafter(lo_r, -np.inf))
            hi_r = float(np.nextafter(hi_r, np.inf))
            lo_i = float(np.nextafter(lo_i, -np.inf))
            hi_i = float(np.nextafter(hi_i, np.inf))
        ok = (icmp(acc[0], ZERO) > 0 or icmp(acc[1], ZERO) < 0
              or icmp(acc[2], ZERO) > 0 or icmp(acc[3], ZERO) < 0)
        # floor: distance of the hull to the origin (lower bound of |h|)
        dr, di = None, None
        if icmp(acc[0], ZERO) > 0:
            dr = acc[0]
        elif icmp(acc[1], ZERO) < 0:
            dr = T[57]
            NEG(BR(dr.x), BR(acc[1].x), RNDN)
        if icmp(acc[2], ZERO) > 0:
            di = acc[2]
        elif icmp(acc[3], ZERO) < 0:
            di = T[58]
            NEG(BR(di.x), BR(acc[3].x), RNDN)
        if dr is None and di is None:
            floor = 0.0
        else:
            if dr is None:
                SET(BR(T[56].x), BR(ZERO.x), RNDN)
                dr = T[56]
            if di is None:
                SET(BR(T[59].x), BR(ZERO.x), RNDN)
                di = T[59]
            MUL(BR(T[56].x), BR(dr.x), BR(dr.x), RNDD)
            MUL(BR(T[57].x), BR(di.x), BR(di.x), RNDD)
            ADD(BR(T[56].x), BR(T[56].x), BR(T[57].x), RNDD)
            SQRT(BR(T[58].x), BR(T[56].x), RNDD)
            floor = T[58].get_d(RNDD)
        return ok, (lo_r, hi_r, lo_i, hi_i), floor


# ------------------------------------------------------------- float64 side
def build_construction():
    o34 = _load("o34z", "routea_weighted_zero_direct_product_outward_2234.py")
    return o34.build_construction()


def channel_arrays(fam, coef, k, x):
    """float64 h_k and h_k' (k=2 derivative misses the B2' term: sizing)."""
    x = np.asarray(x, float)
    H = np.zeros(x.shape, complex)
    D1 = np.zeros(x.shape, complex)
    for (a, th), c in zip(fam, coef):
        u = x / a
        q = 1.0 - u * u
        m = q > 0.0
        if not m.any():
            continue
        qs = np.where(m, q, 1.0)
        phi = np.where(m, np.exp(-K_BIND / qs), 0.0)
        e1 = np.where(m, -(2.0 * K_BIND / a) * u / (qs * qs), 0.0)
        L = e1 + 1j * th
        if k == 0:
            B = np.ones(x.shape)
        else:
            e2 = np.where(m, -(2.0 * K_BIND / (a * a))
                          * (1.0 / (qs * qs) + 4.0 * u * u / (qs ** 3)), 0.0)
            B = e2 + L * L
        W = phi * np.exp(1j * th * x)
        H += c * W * B
        D1 += c * W * L * B
    return H, D1


def arc_geometry(fam):
    vals = sorted(set(float(a) for a, _ in fam))
    a29, a30 = vals[-2], vals[-1]
    on_arc = [(float(a), float(th)) for a, th in fam if float(a) > a29]
    return a29, a30, on_arc


def ratio_profile(fam, coef, k, a29):
    x = np.linspace(-a29, a29, NXW)
    H, D1 = channel_arrays(fam, coef, k, x)
    aH = np.abs(H)
    r = np.abs(D1) / np.maximum(aH, 1e-300)
    # guard: below 1e-200 the float64 |h| is underflow territory; that
    # region cannot exist inside [-a29, a29] (min ~ 1e-63), and if it did
    # the certification would fail and bisect (fail-safe).
    r = np.where(aH > 1e-200, r, 1.0)
    return x, r


def initial_boxes(a29, anchors, xs, ratio, safety=0.05, wmax=0.02,
                  wmin=5e-8):
    h = xs[1] - xs[0]
    anch = sorted(set(float(t) for t in anchors))
    boxes = []
    cur = -a29
    while cur < a29:
        i = int(round((cur + a29) / h))
        i = min(max(i, 0), xs.shape[0] - 1)
        r = float(ratio[i])
        w = safety / r if r > 0.0 else wmax
        w = min(max(w, wmin), wmax)
        nxt = cur + w
        j = bisect.bisect_right(anch, cur + 1e-15)
        if j < len(anch):
            nxt = min(nxt, anch[j])
        nxt = min(nxt, a29)
        if not nxt > cur:
            nxt = min(cur + wmin, a29)
        boxes.append((cur, float(nxt)))
        cur = float(nxt)
    if boxes and boxes[-1][1] < a29:
        boxes[-1] = (boxes[-1][0], a29)
    return boxes


# ------------------------------------------------------------------- modes
def pave_worker(name):
    t_start = time.time()
    fam, base, corr, a_max = build_construction()
    coef = base if name.startswith("base") else corr
    k = 0 if name.endswith("M0") else 2
    a29, a30, on_arc = arc_geometry(fam)
    kern = Kernel(fam, coef, k)
    anchors = [0.0]
    for a, _ in fam:
        a = float(a)
        if a < a29:
            anchors.extend([a, -a])
    xs, ratio = ratio_profile(fam, coef, k, a29)
    boxes0 = initial_boxes(a29, anchors, xs, ratio)
    assert len(boxes0) < 200000, "walk exploded"
    queue = [(lo, hi, 0) for lo, hi in boxes0]
    n_init = len(queue)
    n_pass_first = 0
    n_bis = 0
    n_fail = 0
    max_depth = 0
    hist = {}
    min_floor = None
    processed = 0
    while queue:
        lo, hi, d = queue.pop()
        ok, ends, floor = kern.eval_box(lo, hi)
        processed += 1
        if processed % 3000 == 0:
            print(json.dumps({"part": name, "processed": processed,
                              "passed": sum(hist.values()),
                              "queued": len(queue),
                              "elapsed_s": round(time.time() - t_start, 1)}),
                  flush=True)
        if ok:
            hist[d] = hist.get(d, 0) + 1
            if d == 0:
                n_pass_first += 1
            if floor > 0.0 and (min_floor is None or floor < min_floor[0]):
                min_floor = (floor, lo, hi)
            continue
        if d >= MAXDEPTH:
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
    out = {
        "record": 2242, "part": "pave", "channel": name, "k": k,
        "coef_source": "base" if name.startswith("base") else "corr",
        "region": [-a29, a29], "a29": a29, "a30": a30,
        "families_on_edge_arc": on_arc,
        "n_boxes_initial": n_init,
        "n_boxes_final": sum(hist.values()),
        "n_pass_first": n_pass_first,
        "n_bisections": n_bis,
        "max_depth": max_depth,
        "depth_histogram": {str(d): c for d, c in sorted(hist.items())},
        "n_failures": n_fail,
        "min_floor": None if min_floor is None
        else {"value": min_floor[0], "box": [min_floor[1], min_floor[2]]},
        "walk": {"safety": 0.05, "wmax": 0.02, "wmin": 5e-8,
                 "grid": NXW, "n_anchors": len(set(float(t)
                                                   for t in anchors))},
        "method": "directed 256-bit MPFR natural interval extension, "
                  "final hull expanded %d ulp; pass iff one coordinate "
                  "interval excludes 0" % NOZERO_ULPS,
        "elapsed_s": round(time.time() - t_start, 1),
        "verdict": "ZERO-FREE-CERTIFIED" if n_fail == 0 else "OPEN",
    }
    (R / ("2242_pave_%s.json" % name)).write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k2: out[k2] for k2 in
                      ("verdict", "n_boxes_final", "n_failures",
                       "max_depth", "min_floor", "elapsed_s")}), flush=True)


def edge_worker():
    fam, base, corr, a_max = build_construction()
    a29, a30, on_arc = arc_geometry(fam)
    assert len(on_arc) == 1, "edge arc must carry exactly one family"
    a30f, th30 = on_arc[0]
    assert abs(a30f - a30) < 1e-15
    T = [M() for _ in range(12)]
    a29m, a30m = T[0], T[1]
    a29m.set_d(a29)
    a30m.set_d(a30)
    th30m = T[2]
    th30m.set_d(th30)
    r = T[3]
    DIV(BR(r.x), BR(a29m.x), BR(a30m.x), RNDD)
    MUL(BR(r.x), BR(r.x), BR(r.x), RNDD)
    q29u = T[4]
    SUB(BR(q29u.x), BR(ONE.x), BR(r.x), RNDU)
    q29d = T[5]
    DIV(BR(T[6].x), BR(a29m.x), BR(a30m.x), RNDU)
    MUL(BR(T[6].x), BR(T[6].x), BR(T[6].x), RNDU)
    SUB(BR(q29d.x), BR(ONE.x), BR(T[6].x), RNDD)
    g2lo = T[7]
    MUL(BR(T[8].x), BR(C64.x), BR(q29u.x), RNDU)
    SUB(BR(g2lo.x), BR(SIXTY.x), BR(T[8].x), RNDD)
    MUL(BR(T[8].x), BR(q29u.x), BR(q29u.x), RNDD)
    MUL(BR(T[8].x), BR(THREE.x), BR(T[8].x), RNDD)
    ADD(BR(g2lo.x), BR(g2lo.x), BR(T[8].x), RNDD)
    q2 = T[9]
    MUL(BR(q2.x), BR(q29u.x), BR(q29u.x), RNDU)
    MUL(BR(q2.x), BR(q2.x), BR(q2.x), RNDU)
    inv4 = T[10]
    DIV(BR(inv4.x), BR(ONE.x), BR(q2.x), RNDD)
    d30 = T[11]
    MUL(BR(d30.x), BR(a30m.x), BR(a30m.x), RNDN)
    s2a2 = mk(0.0)
    DIV(BR(s2a2.x), BR(SIXTY.x), BR(d30.x), RNDN)
    # deflate by 2^-200 so the RNDN constant cannot lift the bound above
    # the true infimum of B2_re over the arc
    defl = mk(1.0 - 2.0 ** -200)
    MUL(BR(s2a2.x), BR(s2a2.x), BR(defl.x), RNDD)
    LB = mk(0.0)
    MUL(BR(LB.x), BR(s2a2.x), BR(g2lo.x), RNDD)
    MUL(BR(LB.x), BR(LB.x), BR(inv4.x), RNDD)
    t2u = mk(0.0)
    abth = mk(abs(th30))
    MUL(BR(t2u.x), BR(abth.x), BR(abth.x), RNDU)
    SUB(BR(LB.x), BR(LB.x), BR(t2u.x), RNDD)
    lb_positive = icmp(LB, ZERO) > 0
    g2_positive = icmp(g2lo, ZERO) > 0
    c30 = {"base": [0.0, 0.0], "corr": [0.0, 0.0]}
    c30_nonzero = {}
    for nm, cf in (("base", base), ("corr", corr)):
        cval = None
        for (a, th), c in zip(fam, cf):
            if abs(float(a) - a30) < 1e-15:
                cval = complex(c)
        assert cval is not None
        c30[nm] = [cval.real, cval.imag]
        c30_nonzero[nm] = not (cval.real == 0.0 and cval.imag == 0.0)
    out = {
        "record": 2242, "part": "edge",
        "a29": a29, "a30": a30,
        "families_on_edge_arc": on_arc,
        "n_families_beyond_a29": 1,
        "q29_upper": q29u.get_d(RNDU),
        "q29_lower": q29d.get_d(RNDD),
        "G2_lower_bound_at_q29u": g2lo.get_d(RNDD),
        "G2_positive": bool(g2_positive),
        "inv_q4_lower_bound": inv4.get_d(RNDD),
        "B2_re_lower_bound": LB.get_d(RNDD),
        "B2_re_positive": bool(lb_positive),
        "c30": c30, "c30_nonzero": c30_nonzero,
        "arcs": ["(a29, a30)", "(-a30, -a29)"],
        "phi_positive": "phi = exp(-K/q) > 0 for q > 0, i.e. |x| < a30, "
                        "strictly; holds on both open arcs including "
                        "arbitrary slivers at +-a30",
        "verdict_by_channel": {
            "base_M0": bool(c30_nonzero["base"]),
            "corr_M0": bool(c30_nonzero["corr"]),
            "base_D2": bool(c30_nonzero["base"] and lb_positive
                            and g2_positive),
            "corr_D2": bool(c30_nonzero["corr"] and lb_positive
                            and g2_positive),
        },
        "boundary_zeros_flat": "h_k(+-a30) = 0 with all one-sided "
                               "derivatives 0 (flat C-infinity extension "
                               "of phi at |u| = 1); g'(+-a_max) = 0 "
                               "exactly, no kink mass (2238 identity)",
        "all_pass": bool(lb_positive and g2_positive
                         and c30_nonzero["base"] and c30_nonzero["corr"]),
    }
    for o in T + [s2a2, LB, t2u, abth, defl]:
        o.clear()
    (R / "2242_edge.json").write_text(json.dumps(out, indent=2) + "\n",
                                      encoding="utf-8")
    print(json.dumps({k2: out[k2] for k2 in
                      ("all_pass", "B2_re_lower_bound", "q29_upper",
                       "c30_nonzero", "verdict_by_channel")}), flush=True)


def smoke():
    fam, base, corr, a_max = build_construction()
    a29, a30, on_arc = arc_geometry(fam)
    out = {"record": 2242, "part": "smoke", "a29": a29, "a30": a30,
           "families_on_edge_arc": on_arc}
    # 1) float64 factored-identity check for the k=2 pieces
    worst = 0.0
    worst_at = None
    for (a, th), c in zip(fam[::5], base[::5]):
        for x in np.linspace(-a * 0.97, a * 0.97, 13):
            u = x / a
            q = 1.0 - u * u
            if q <= 1e-3:
                continue
            phi = math.exp(-30.0 / q)
            P = ((60.0 / (a * a)) * (60.0 - 64.0 * q + 3.0 * q * q)
                 * phi / q ** 4 - th * th * phi)
            Q = -120.0 * th / a * u * phi / (q * q)
            e1 = -(60.0 / a) * u / (q * q)
            e2 = -(60.0 / (a * a)) * (1.0 / (q * q) + 4.0 * u * u / q ** 3)
            ref = phi * (e2 + (e1 + 1j * th) ** 2)
            d = abs((P + 1j * Q) - ref) / max(abs(ref), 1e-320)
            if d > worst:
                worst = d
                worst_at = [float(a), float(x)]
    out["factor_identity_rel_max"] = worst
    out["factor_identity_at"] = worst_at
    # 2) containment: certified hull must contain the float64 point values
    samples = []
    for x0 in (-1.5621, 1.5638, -1.5960, 1.5977, 0.0, 1.639, -1.639,
               2.31, -2.31, 2.319, 1.84, -1.84, 1.0, -2.0, 0.5):
        for w in (2e-3, 1e-4):
            samples.append((max(x0 - w, -a29), min(x0 + w, a29)))
    samples.append((-a29, a29 * 0.999))
    samples.append((a29 * 0.999, a29))
    samples.append((-2.33, -a29))
    result_rows = {}
    for name, coef, k in (("base_M0", base, 0), ("base_D2", base, 2),
                          ("corr_M0", corr, 0), ("corr_D2", corr, 2)):
        kern = Kernel(fam, coef, k)
        rows = []
        worst_rel = 0.0
        for lo, hi in samples:
            ok, ends, floor = kern.eval_box(lo, hi)
            xr = np.linspace(lo, hi, 9)
            H = channel_arrays(fam, coef, k, xr)[0]
            re = np.real(H)
            im = np.imag(H)
            viol = max(0.0,
                       float(np.max(ends[0] - re)), float(np.max(re - ends[1])),
                       float(np.max(ends[2] - im)), float(np.max(im - ends[3])))
            scale = max(1e-300, float(np.max(np.abs(H))),
                        abs(ends[0]), abs(ends[1]), abs(ends[2]),
                        abs(ends[3]))
            rel = viol / scale
            worst_rel = max(worst_rel, rel)
            rows.append({"box": [lo, hi], "no_zero": bool(ok),
                         "hull_scale": scale, "containment_rel_viol": rel})
        result_rows[name] = {"worst_rel_viol": worst_rel, "rows": rows}
        print(name, "worst containment rel viol %.3e" % worst_rel,
              flush=True)
    out["containment"] = result_rows
    # 3) mini-pave pass-rate probe on the real walk
    probes = {}
    for name, coef, k in (("base_M0", base, 0), ("base_D2", base, 2),
                          ("corr_M0", corr, 0), ("corr_D2", corr, 2)):
        kern = Kernel(fam, coef, k)
        anchors = [0.0]
        for a, _ in fam:
            a = float(a)
            if a < a29:
                anchors.extend([a, -a])
        xs, ratio = ratio_profile(fam, coef, k, a29)
        boxes = initial_boxes(a29, anchors, xs, ratio)
        n = len(boxes)
        t0 = time.time()
        probe = boxes[:: max(1, n // 400)][:400]
        npass = sum(1 for lo, hi in probe if kern.eval_box(lo, hi)[0])
        probes[name] = {"n_walk_boxes": n,
                        "probe_size": len(probe),
                        "probe_pass": npass,
                        "probe_pass_rate": npass / len(probe),
                        "probe_s": round(time.time() - t0, 1),
                        "est_total_boxes": int(n / max(npass / len(probe),
                                                       1e-9))}
        print(name, probes[name], flush=True)
    out["walk_probe"] = probes
    (R / "2242_smoke.json").write_text(json.dumps(out, indent=2) + "\n",
                                       encoding="utf-8")


def reduce_worker():
    parts = {}
    for name in ("base_M0", "base_D2", "corr_M0", "corr_D2"):
        parts[name] = json.loads(
            (R / ("2242_pave_%s.json" % name)).read_text(encoding="utf-8"))
    edge = json.loads((R / "2242_edge.json").read_text(encoding="utf-8"))
    ok = (all(p["n_failures"] == 0 for p in parts.values())
          and edge["all_pass"])
    channels = {}
    for name, p in parts.items():
        channels[name] = {
            "k": p["k"], "region": p["region"],
            "n_boxes_final": p["n_boxes_final"],
            "n_pass_first": p["n_pass_first"],
            "n_bisections": p["n_bisections"],
            "max_depth": p["max_depth"],
            "n_failures": p["n_failures"],
            "min_floor": p["min_floor"],
            "verdict": p["verdict"],
        }
    result = {
        "record": 2242,
        "status": "ZERO-COUNT-CERTIFIED" if ok else "ZERO-COUNT-OPEN",
        "claim": "Z = 0 for each of the four channel functions on the open "
                 "interval (-a30, a30): no real zeros, hence |h_k| is "
                 "C-infinity on R and the composite-trapezoid identity "
                 "carries no kink term (the 2238 risk-cell wall drops)",
        "a29": edge["a29"], "a30": edge["a30"],
        "families_on_edge_arc": edge["families_on_edge_arc"],
        "channels": channels,
        "edge_arcs": edge,
        "consequence": {
            "panel_cem": "(dx^2/12)(2 a_max) M_k(sigma) with N_risk = 0 "
                         "(priced in record 2243)",
            "identity": "T - I = (dx^2/12) sum_p Delta_p - (dx^2/2) sum_p "
                        "int_0^1 B_2 dg'; with Z = 0 the Delta sum "
                        "telescopes to g'(x_N) - g'(x_0) = 0 and "
                        "TV(g') <= int |g''| (2238)",
        },
        "boundary_zeros_flat": edge["boundary_zeros_flat"],
        "nonclaims": [
            "the pavement certifies h_k(x) != 0 per box through outward "
            "interval hulls; it is not a sampling or scan",
            "float64 arrays are used for box sizing only; every acceptance "
            "decision is made in directed 256-bit MPFR with a 32-ulp hull "
            "inflation absorbing constant rounding",
            "the edge-arc certificate is the analytic single-family bound "
            "(phi > 0; k=2: B2_re lower bound LB > 0 on the whole arc)",
            "the four channels are exactly the 2234 node_bounds channels "
            "(h_0 = F, h_2 = F'')",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_zero_count_certificate_2242.py",
            "mpfr": "libmpfr.so.6 via ctypes, 256-bit precision, "
                    "RNDD/RNDU directed rounding",
            "construction": "results/2234_build_cache.npz (local-only)",
            "pave_parts": ["results/2242_pave_%s.json" % n for n in parts],
            "edge_part": "results/2242_edge.json",
        },
    }
    (R / "2242_zero_count_certificate.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "min_floor": {n: (c["min_floor"] or {}).get("value")
                                    for n, c in channels.items()},
                      "max_depth": {n: c["max_depth"]
                                    for n, c in channels.items()},
                      "boxes": {n: c["n_boxes_final"]
                                for n, c in channels.items()}},
                     indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "smoke")
    if mode == "smoke":
        smoke()
    elif mode == "edge":
        edge_worker()
    elif mode == "reduce":
        reduce_worker()
    elif mode.startswith("pave_"):
        pave_worker(mode[len("pave_"):])
    else:
        raise SystemExit("unknown MODE=%s" % mode)


if __name__ == "__main__":
    main()
