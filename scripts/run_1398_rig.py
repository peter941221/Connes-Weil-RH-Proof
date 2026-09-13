#!/usr/bin/env python3
"""Record 1398 - rung-3 joint-witness rig (MODEL evidence, one-sided).

Implements docs/proofs/1398_rung3_joint_witness_prereg_v2_gateS_fix.md
(which re-locks v1 sections 1-8 verbatim except the GV scale clause):
the deterministic route-alpha owner pipeline (prereg section 1, the
C1WindowTaperLift/Core/Assembly + C1RouteAlphaOwner transcription), the
(J1)-PASS cell decode of section 2, the gates of section 3, outputs of
section 4.  Law 42: no line here may deviate from the prereg; a change
costs a NEW prereg.

Instrument reading notes (recorded in v2): npw = 32/64 means quadrature
NODES PER PERIOD, 16-node GL panels (so <= 2 periods/panel holds with
slack).  The 1393 (J1) formula layer is IMPORTED (main-guarded module)
so the GI recompute cannot drift from the committed artifact.

Stack: python3.12 + numpy + mpmath; mp 200-bit factor layer (1393 G3
class), float64 owner/quadrature layer.
"""

import sys, os, json, math, time, gzip, hashlib, subprocess
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_1393_rig as r13                      # verbatim 1393 formulas

T0 = time.time()
mp.mp.prec = 200
M, MC = mp.mpf, mp.mpc

D_GRID, DELTA_GRID, RADII = r13.D_GRID, r13.DELTA_GRID, r13.RADII
EPS_GRID, RERE_GRID, IMRI_GRID = r13.EPS_GRID, r13.RERE_GRID, r13.IMRI_GRID
NGEOM = len(RERE_GRID) * len(IMRI_GRID)          # 20

LOG2 = math.log(2.0)
EULER = 0.5772156649015328606
LOG4PI_G = math.log(4.0 * math.pi) + EULER       # (log 4pi + gamma)

# ---------------------------------------------------------- locked tolerances
GI_TOL, GS_TOL = 1e-9, M(1e-30)
GT_SYM_TOL, GT_PAIR_TOL, GT_JH_TOL = 1e-40, 1e-10, 1e-12
GF_IM_TOL, GF_RE_TOL = 1e-6, 1e-8
GD_TOL, GR_TOL, GQ_TOL, GV_TIE = 1e-6, 1e-8, 1e-9, 1e-6
Y0 = 1e-3
J_EDGE = 1.0 / 256.0     # below this S(1-v) = 1 within 1e-111 (prereg 1.4)
NPW_DEFAULT = 32         # prereg section 3 binding reading

_GL16X, _GL16W = np.polynomial.legendre.leggauss(16)


def stamp(msg):
    print(f"[{time.time() - T0:8.1f}s] {msg}", flush=True)


# ------------------------------------------------------- S / J (prereg 1.3/1.4)
def S_mp(t):
    if t <= 0:
        return M(0)
    if t >= 1:
        return M(1)
    a = mp.exp(-1 / t)
    b = mp.exp(-1 / (1 - t))
    return a / (a + b)


def j_edges():
    es = [0.0, J_EDGE]
    e = J_EDGE
    while e < 0.5:
        e *= 2
        es.append(e)
    es.append(0.5)
    g = 0.75
    while g < 1.0:
        es.append(min(g, 1.0))
        g = 1 - (1 - g) / 2
    es.append(1.0)
    return sorted(set(es))


_JE = j_edges()


def J_master(beta, which):
    """J(beta)  = int_0^1 S(1-v) e^{beta v} dv  ('J')
       J2(beta) = int_0^1 S(v)   e^{beta v} dv  ('J2')
    Graded GL-16 panels in mp; the [0, J_EDGE] piece is closed:
    J gets int e^{beta v} (S(1-v)=1 up to 1e-111), J2 gets 0."""
    beta = MC(beta)
    acc = MC(0)
    for a, b in zip(_JE[:-1], _JE[1:]):
        if b <= a:
            continue
        if a == 0.0:
            if which == 'J':
                acc += (mp.e ** (beta * b) - 1) / beta if beta != 0 else M(b)
            continue
        mid, half = (a + b) / 2, (b - a) / 2
        for xk, wk in zip(_GL16X, _GL16W):
            v = mid + half * M(str(xk))
            s = S_mp(v) if which == 'J2' else S_mp(1 - v)
            acc += M(str(wk)) * half * s * mp.e ** (beta * v)
    return acc


def _S_np(t):
    t = np.asarray(t, dtype=np.float64)
    return np.where(t <= 0, 0.0,
                    np.where(t >= 1, 1.0,
                             np.exp(-1.0 / np.where((t > 0) & (t < 1),
                                                    np.where(t > 0, t, 1.0),
                                                    1.0))))


def _expdiff(w, a, b):
    """(e^{wb} - e^{wa})/w vectorized; branches w = 0 and small |w(b-a)|."""
    a = np.asarray(a, dtype=np.float64)
    b = np.asarray(b, dtype=np.float64)
    if w == 0:
        return (b - a).astype(np.complex128)
    z = w * (b - a)
    small = np.abs(z) < 1e-4
    zs = np.where(small, z, 1.0)
    ratio = np.where(small, np.sinh(zs / 2) / (zs / 2), 1.0)
    big = np.where(small, 1.0, (np.exp(w * np.where(small, 0.0, b))
                                - np.exp(w * np.where(small, 0.0, a))) / w)
    return np.where(small,
                    (b - a) * np.exp(w * 0.5 * (a + b)) * ratio, big)


# -------------------------------------------------------- mp factor layer (1.2)
def lambda_min_mp(G):
    lo, hi = M(0), M(mp.re(sum(G[i, i] for i in range(4))))

    def ld_pd(mu):
        A = mp.zeros(4, 4)
        for i in range(4):
            for j in range(4):
                A[i, j] = G[i, j]
            A[i, i] -= mu
        for c in range(4):
            for r in range(c + 1, 4):
                f = A[r, c] / A[c, c]
                for k in range(c, 4):
                    A[r, k] -= f * A[c, k]
        return all(mp.re(A[i, i]) > 0 for i in range(4))

    assert ld_pd(lo)
    for _ in range(150):
        mu = (lo + hi) / 2
        if ld_pd(mu):
            lo = mu
        else:
            hi = mu
    return lo


def solve_factor(R, eps, pattern, rho_mpc, alpha_scale=1):
    """Prereg 1.2 (a)-(g).  alpha_scale is the GT tier-1 variant only."""
    nodes = [M(0), M("0.5"), M(1), rho_mpc]
    G = r13.gram(M(str(R)), nodes)                        # verbatim 1393 1.3
    alpha = lambda_min_mp(G) * M(str(alpha_scale))
    TB = sum(mp.exp(mp.fabs(n) * M(str(R))) for n in nodes)   # Lift.lean:143
    Delta = M(str(eps)) * alpha / (4 * (1 + M(str(eps))) * TB ** 2)
    delta = min(M(str(R)) / 2, Delta)
    rIn, rOut = M(str(R)) - delta, M(str(R)) - delta / 2
    p = [MC(pattern[i]) for i in range(4)]
    T = mp.zeros(4, 4)
    jc = {}
    betas = []
    for i in range(4):
        for j in range(4):
            A = nodes[i] + mp.conj(nodes[j])
            if A == 0:
                T[i, j] = 2 * rIn + delta / 2
            else:
                b1, b2 = A * delta / 2, -A * delta / 2
                for bb in (b1, b2):
                    if bb not in jc:
                        jc[bb] = J_master(bb, 'J')
                    betas.append(bb)
                T[i, j] = (2 * mp.sinh(A * rIn) / A
                           + (delta / 2) * (mp.e ** (A * rIn) * jc[b1]
                                            + mp.e ** (-A * rIn) * jc[b2]))
    coeff = mp.lu_solve(T, mp.matrix(4, 1, p))
    resid = max(abs(sum(T[i, j] * coeff[j, 0] for j in range(4)) - p[i])
                for i in range(4))
    return dict(nodes=nodes, G=G, alpha=alpha, TB=TB, Delta=Delta,
                delta=delta, rIn=rIn, rOut=rOut, T=T, coeff=coeff,
                resid=resid, betas=betas,
                c64=np.array([complex(coeff[i, 0]) for i in range(4)]),
                rIn64=float(rIn), rOut64=float(rOut), delta64=float(delta),
                R=R, eps=eps, pattern=pattern, alpha_scale=alpha_scale)


# ------------------------------------------------ float64 owner evaluator (1.4)
class Owner:
    """g(x) = sum_{p,q} (c_p b_q) e^{conj s_p x} K_pq(x); K_pq is the
    closed piecewise integral int tau_u(t) tau_f(x-t) e^{w t} dt:
    plateau pieces exact, FULL sliver pieces via the master J, partial
    slivers by 16-node GL in scaled coordinates (mass <= 1e-4*delta/2,
    prereg 1.4).  Piece templates are per-Cg-segment (the state machine
    is constant between the ~25 critical points; g is C-infinity so
    boundary template choice is value-immaterial)."""

    def __init__(self, fu, ff):
        self.u, self.f = fu, ff
        self.nodes = ff['nodes']
        self.rO_u, self.rI_u = fu['rOut64'], fu['rIn64']
        self.rO_f, self.rI_f = ff['rOut64'], ff['rIn64']
        self.d_u, self.d_f = fu['delta64'], ff['delta64']
        self.Rs = self.rO_u + self.rO_f
        self.Rg = fu['R'] + ff['R']
        self.mode = np.array([np.conj(complex(n)) for n in self.nodes])
        self.wl = np.array([self.mode[q] - self.mode[p]
                            for p in range(4) for q in range(4)])
        self.pf = np.array([fu['c64'][q] * ff['c64'][p]
                            for p in range(4) for q in range(4)])
        C = set()
        for eu in (-self.rO_u, -self.rI_u, self.rI_u, self.rO_u):
            for ef in (self.rO_f, self.rI_f):
                C.add(eu - ef)
                C.add(eu + ef)
        C.add(0.0)
        self.Cg = np.array(sorted(c for c in C if abs(c) <= 2.05 * self.Rs))
        self.seg_mid = 0.5 * (self.Cg[:-1] + self.Cg[1:])
        self.seg_templates = {}
        self._jc = {}

    # ---- (slope, const) edge bookkeeping at a template x ----
    def _edge_sets(self, x):
        lo = max(((0.0, -self.rO_u), (1.0, -self.rO_f)),
                 key=lambda e: e[0] * x + e[1])
        hi = min(((0.0, self.rO_u), (1.0, self.rO_f)),
                 key=lambda e: e[0] * x + e[1])
        lo_v, hi_v = lo[0] * x + lo[1], hi[0] * x + hi[1]
        inner = []
        for e in ((0.0, -self.rI_u), (0.0, self.rI_u),
                  (1.0, -self.rI_f), (1.0, self.rI_f)):
            v = e[0] * x + e[1]
            if lo_v < v < hi_v and v - lo_v > 1e-15 and hi_v - v > 1e-15:
                inner.append(e)
        inner.sort(key=lambda e: e[0] * x + e[1])
        return lo, hi, inner

    def _template(self, seg, pair):
        key = (seg, pair)
        tm = self.seg_templates.get(key)
        if tm is not None:
            return tm
        p, q = pair
        x = float(self.seg_mid[seg])
        w = self.wl[4 * p + q]
        lo, hi, inner = self._edge_sets(x)
        edges = [lo] + inner + [hi]
        pieces = []
        for e1, e2 in zip(edges[:-1], edges[1:]):
            v1, v2 = e1[0] * x + e1[1], e2[0] * x + e2[1]
            if v2 <= v1:
                continue
            mid = 0.5 * (v1 + v2)
            su = 0 if abs(mid) < self.rI_u else 1
            sf = 0 if abs(x - mid) < self.rI_f else 1
            kind = (su, sf, e1, e2)
            closed = None
            if su == 1 and sf == 0 and self._u_full(e1, e2):
                closed = ('u', e1, e2)
            elif su == 0 and sf == 1 and self._f_full(e1, e2):
                closed = ('f', e1, e2)
            pieces.append((kind, closed))
        self.seg_templates[key] = (w, pieces)
        return (w, pieces)

    def _u_full(self, e1, e2):
        t = 1e-14
        return ((abs(e1[0]) < 1e-300 and abs(e2[0]) < 1e-300)
                and ((abs(e1[1] + self.rO_u) < t and abs(e2[1] + self.rI_u) < t)
                     or (abs(e1[1] - self.rI_u) < t and abs(e2[1] - self.rO_u) < t)))

    def _f_full(self, e1, e2):
        t = 1e-14
        return ((abs(e1[0] - 1) < 1e-300 and abs(e2[0] - 1) < 1e-300)
                and ((abs(e1[1] + self.rO_f) < t and abs(e2[1] + self.rI_f) < t)
                     or (abs(e1[1] - self.rI_f) < t and abs(e2[1] - self.rO_f) < t)))

    def _Jc(self, beta, which):
        k = (complex(beta), which)
        if k not in self._jc:
            self._jc[k] = complex(J_master(MC(beta), which))
        return self._jc[k]

    def _slu_closed(self, w, e1, e2):
        d2 = self.d_u / 2
        if e1[1] < 0:   # left sliver [-rO_u,-rI_u]: profile S(v)
            return d2 * np.exp(-w * self.rO_u) * self._Jc(w * d2, 'J2')
        return d2 * np.exp(w * self.rI_u) * self._Jc(w * d2, 'J')

    def _slf_closed(self, w, e1, e2):
        d2 = self.d_f / 2
        if e1[1] < e2[1]:  # left sliver (x-rO_f, x-rI_f): profile S(v)
            return ('L', d2 * self._Jc(w * d2, 'J2'), -self.rO_f)
        return ('R', d2 * self._Jc(w * d2, 'J'), self.rI_f)

    def _gl(self, w, xs, aa, bb, su, sf):
        """16-node GL on scaled coords over per-x intervals (partial
        slivers / doubles); bounded by 1e-4 * delta/2 relative mass."""
        mid, half = 0.5 * (aa + bb), 0.5 * (bb - aa)
        acc = np.zeros(xs.shape, dtype=np.complex128)
        for xk, wk in zip(_GL16X, _GL16W):
            t = mid + half * xk
            tu = 1.0 if su == 0 else \
                _S_np((self.rO_u - np.abs(t)) / max(self.d_u / 2, 1e-300))
            tf = 1.0 if sf == 0 else \
                _S_np((self.rO_f - np.abs(xs - t)) / max(self.d_f / 2, 1e-300))
            acc += wk * half * tu * tf * np.exp(w * t)
        return acc

    def g(self, xs):
        xs = np.asarray(xs, dtype=np.float64)
        scalar = xs.ndim == 0
        if scalar:
            xs = xs.reshape(1)
        out = np.zeros(xs.shape, dtype=np.complex128)
        segs = np.searchsorted(self.Cg, xs, side='right') - 1
        nseg = len(self.seg_mid)
        for si in np.unique(segs):
            if si < 0 or si >= nseg:
                continue
            m = segs == si
            xv = xs[m]
            acc = np.zeros(xv.shape, dtype=np.complex128)
            for p in range(4):
                for q in range(4):
                    pref = self.pf[4 * p + q]
                    if pref == 0:
                        continue
                    acc += pref * np.exp(self.mode[p] * xv) * \
                        self._K_seg(int(si), (p, q), xv)
            out[m] = acc
        return out[0] if scalar else out

    def _K_seg(self, seg, pair, xv):
        p, q = pair
        w, pieces = self._template(seg, pair)
        out = np.zeros(xv.shape, dtype=np.complex128)
        for (su, sf, e1, e2), closed in pieces:
            aa = e1[0] * xv + e1[1]
            bb = e2[0] * xv + e2[1]
            ok = bb > aa
            if not np.any(ok):
                continue
            xs, a_, b_ = xv[ok], aa[ok], bb[ok]
            if su == 0 and sf == 0:
                out[ok] += _expdiff(w, a_, b_)
            elif closed is not None and closed[0] == 'u':
                out[ok] += self._slu_closed(w, e1, e2)
            elif closed is not None and closed[0] == 'f':
                side, const, off = self._slf_closed(w, e1, e2)
                out[ok] += const * np.exp(w * (xs + off))
            else:
                out[ok] += self._gl(w, xs, a_, b_, su, sf)
        return out


# ------------------------------------------------------ F / A / lap (1.5 / 3)
def _panels(edges, freq, npw):
    """Nodes/weights: npw nodes per period, 16-node GL panels, merge
    guard for subinterval float64 collapse (prereg section 3)."""
    outx, outw = [], []
    for a, b in zip(edges[:-1], edges[1:]):
        L = b - a
        if L <= 0 or L < 1e-12:
            continue
        per = freq * L / (2 * math.pi)
        npn = max(1, int(math.ceil(npw * per / 16)))
        for k in range(npn):
            pa, pb = a + L * k / npn, a + L * (k + 1) / npn
            if pb <= pa or (pb - pa) < 1e-12:
                continue
            mid, half = 0.5 * (pa + pb), 0.5 * (pb - pa)
            outx.append(mid + half * _GL16X)
            outw.append(half * _GL16W)
    if not outx:
        return np.array([]), np.array([])
    return np.concatenate(outx), np.concatenate(outw)


def F_at(owner, y, npw):
    """F(y) = int conj(g(-t)) g(y-t) dt, partitioned at -Cg and y - Cg."""
    Rs = owner.Rs
    lo, hi = max(-Rs, y - Rs), min(Rs, y + Rs)
    if hi - lo < 1e-12:
        return 0.0 + 0.0j
    bps = sorted(({lo, hi}
                  | {float(c) for c in -owner.Cg if lo < c < hi}
                  | {float(c) for c in (y - owner.Cg) if lo < c < hi}))
    freq = 2.0 * abs(np.imag(owner.nodes[3])) + 2.0
    xn, wn = _panels(bps, freq, npw)
    if xn.size == 0:
        return 0.0 + 0.0j
    return complex(np.sum(wn * np.conj(owner.g(-xn)) * owner.g(y - xn)))


def gv_scale(reF0, Rg):
    """1398 v2 GV scale: S = |log4pi_g * reF0| + |2 reF0| * I with
    I = int_{y0}^{2Rg} dy/(e^y - e^{-y}) = 0.5*(ln tanh(Rg) - ln tanh(y0/2))."""
    I = 0.5 * (math.log(math.tanh(Rg)) - math.log(math.tanh(Y0 / 2)))
    return abs(LOG4PI_G * reF0) + abs(2.0 * reF0) * I


def compute_A(owner, npw=NPW_DEFAULT):
    """Returns (A_real, F0, S) per prereg 1.5 + v2 GV."""
    Rg = owner.Rg
    F0 = F_at(owner, 0.0, npw)
    reF0 = float(np.real(F0))
    freq = 2.0 * abs(np.imag(owner.nodes[3])) + 2.0
    ks = set()
    for c1 in owner.Cg:
        for c2 in owner.Cg:
            for v in (abs(c1 + c2), abs(c1 - c2)):
                if 1e-9 < v < 2 * Rg:
                    ks.add(v)
    for c in owner.Cg:
        if 1e-9 < abs(c) < 2 * Rg:
            ks.add(abs(c))
    ys = sorted(ks)
    ys = [0.0] + [y for y in ys if y > Y0] + [2.0 * Rg]
    if Y0 < 2 * Rg:
        ys = sorted(set(ys) | {Y0})
    integ = 0.0 + 0.0j
    for a, b in zip(ys[:-1], ys[1:]):
        xn, wn = _panels([a, b], freq, npw)
        if xn.size == 0:
            continue
        Fy = np.array([F_at(owner, float(t), npw) for t in xn])
        num = np.exp(xn / 2) * 2 * np.real(Fy) - 2 * reF0
        den = np.exp(xn) - np.exp(-xn)
        integ += complex(np.sum(wn * num / den))
    A = complex(LOG4PI_G * F0 + integ + reF0 * math.log(math.tanh(Rg)))
    return A.real, F0, gv_scale(reF0, Rg)


def laplace_g(owner, rho, npw=NPW_DEFAULT):
    """GD end-to-end: int g(x) e^{rho x} dx over (-Rs, Rs) at Cg panels."""
    Rs = owner.Rs
    bps = sorted({-Rs, Rs} | {float(c) for c in owner.Cg if -Rs < c < Rs})
    freq = 3.0 * abs(np.imag(rho)) + 2.0
    xn, wn = _panels(bps, freq, npw)
    return complex(np.sum(wn * owner.g(xn) * np.exp(rho * xn)))


# --------------------------------------------------------------- gt battery
def gt_tier1(fac_f, fac_u):
    sym = max(abs(S_mp(M(t) / 100) + S_mp(1 - M(t) / 100) - 1)
              for t in range(101))
    pair = M(0)
    jh = M(0)
    anyh = False
    for fac in (fac_f, fac_u):
        for bb in fac['betas']:
            rhs = ((mp.e ** bb - 1) / bb) if bb != 0 else M(1)
            pair = max(pair, abs(J_master(bb, 'J') + J_master(bb, 'J2') - rhs))
            if abs(bb) <= M(1e-14):
                anyh = True
                jh = max(jh, abs(J_master(bb, 'J') - M(0.5)))
    return float(sym), float(pair), float(jh) if anyh else 0.0


# ----------------------------------------------------- (J1) decode (prereg 2)
def decode_cells():
    path = "docs/proofs/1393_component5_rig_cells.tsv.gz"
    with gzip.open(path, 'rt') as f:
        lines = f.read().splitlines()
    hdr = lines[0].split('\t')
    assert hdr == ['d', 'delta', 'Rf', 'Ru', 'Rg', 'K_loc_f', 'K_loc_u',
                   'ceiling', 'C_C', 'C_D', 'C_min', 'ratio', 'band'], hdr
    rows = []
    for i, ln in enumerate(lines[1:]):
        c = ln.split('\t')
        r = i
        di, r = divmod(r, 6 * 5 * 5 * 2 * 2 * NGEOM)
        dli, r = divmod(r, 5 * 5 * 2 * 2 * NGEOM)
        rfi, r = divmod(r, 5 * 2 * 2 * NGEOM)
        rui, r = divmod(r, 2 * 2 * NGEOM)
        ei, r = divmod(r, 2 * NGEOM)
        epi, ri = divmod(r, NGEOM)
        rri, imi = divmod(ri, len(IMRI_GRID))
        geo = (RADII[rfi], RADII[rui], EPS_GRID[ei], EPS_GRID[epi],
               RERE_GRID[rri], IMRI_GRID[imi])
        rows.append(dict(d=D_GRID[di], delta=DELTA_GRID[dli], geo=geo,
                         cols=c, band=c[12], ratio=float(c[11])))
    assert len(rows) == (len(D_GRID) * len(DELTA_GRID) * 25 * 4 * NGEOM), \
        len(rows)
    for rw in rows:
        assert float(rw['cols'][0]) == rw['d']
        assert float(rw['cols'][1]) == rw['delta']
        assert float(rw['cols'][2]) == rw['geo'][0]
        assert float(rw['cols'][3]) == rw['geo'][1]
    return rows


def gi_check(rows):
    """GI: recompute sampled decoded rows through the verbatim 1393 layer."""
    kc = {}

    def kloc(R, rr, im, tag):
        key = (R, rr, im, tag)
        if key not in kc:
            s = [M(0), M("0.5"), M(1), MC(str(rr), str(im))]
            z = [M(1)] * 4 if tag == 'v' else [M(0), M(0), M(0), M(-1)]
            kc[key] = r13.kloc_with_diag(M(str(R)), s, z)[0]
        return kc[key]

    bad = []
    to_check = sorted(set(range(0, len(rows), 1000))
                      | {i for i, rw in enumerate(rows) if rw['band'] == 'PASS'})
    for i in to_check:
        rw = rows[i]
        Rf, Ru, eps, epsp, rr, im = rw['geo']
        Kf = kloc(Rf, rr, im, 'f')
        Ku = kloc(Ru, rr, im, 'v')
        d, dl = M(str(rw['d'])), M(str(rw['delta']))
        Cc, Cd = r13.c_couplings(d, dl, M(str(Rf)) + M(str(Ru)))
        Cm = min(Cc, Cd)
        ceil = 2 * M(str(Ru)) * ((1 + M(str(epsp))) * Ku) * \
            ((1 + M(str(eps))) * Kf)
        rat = 1 - 2 * Cm * ceil / dl
        b = r13.band_of(rat)
        for col, val in ((5, Kf), (6, Ku), (7, ceil), (8, Cc), (9, Cd),
                         (10, Cm), (11, rat)):
            a = M(rw['cols'][col])
            den = max(abs(a), abs(val))
            if den == 0:
                continue
            if abs(val - a) / den > M(str(GI_TOL)):
                bad.append((i, col))
                break
        if b != rw['cols'][12]:
            bad.append((i, 'band'))
        if len(bad) > 5:
            break
    return bad


# --------------------------------------------------------------- per-cell run
def band_of_A(A, S):
    if A > GV_TIE * S:
        return 'POS'
    if A < -GV_TIE * S:
        return 'NEG'
    return 'TIE'


def run_geometry(geo, full=False):
    Rf, Ru, eps, epsp, rr, im = geo
    assert Rf + Ru <= LOG2 / 2 + 1e-15, "G0"
    rho_mpc = MC(str(rr), str(im))
    rho = complex(rho_mpc)
    f = solve_factor(Rf, eps, [0, 0, 0, -1], rho_mpc)
    u = solve_factor(Ru, epsp, [1, 1, 1, 1], rho_mpc)
    own = Owner(u, f)
    A, F0, S = compute_A(own)
    out = dict(geo=geo, A=float(A), F0=complex(F0), S=float(S),
               lap=laplace_g(own, rho),
               gs_ok=bool(f['resid'] <= GS_TOL and u['resid'] <= GS_TOL),
               alpha_f=float(f['alpha']), alpha_u=float(u['alpha']),
               delta_f=float(f['delta']), delta_u=float(u['delta']),
               TB_f=float(f['TB']), TB_u=float(u['TB']),
               Delta_f=float(f['Delta']), Delta_u=float(u['Delta']),
               resid_f=float(f['resid']), resid_u=float(u['resid']))
    if not full:
        return out
    # GF second path: F(0) at npw 24
    out['F0_npw24'] = F_at(own, 0.0, 24)
    # GR: npw 64
    A64, _, S64 = compute_A(own, 64)
    out['A64'] = float(A64)
    # GQ: p_u -> 2 p_u
    u2 = solve_factor(Ru, epsp, [2, 2, 2, 2], rho_mpc)
    A2, _, _ = compute_A(Owner(u2, f))
    out['A_quadr'] = float(A2)
    # GT battery
    sym, pair, jh = gt_tier1(f, u)
    out['gt_sym'], out['gt_pair'], out['gt_jh'] = sym, pair, jh
    # GT alpha/2 sensitivity variant (informational)
    f2 = solve_factor(Rf, eps, [0, 0, 0, -1], rho_mpc, alpha_scale=0.5)
    u2s = solve_factor(Ru, epsp, [1, 1, 1, 1], rho_mpc, alpha_scale=0.5)
    A_half, F0_half, _ = compute_A(Owner(u2s, f2))
    out['A_alpha2'] = float(A_half)
    out['delta_f_alpha2'] = float(f2['delta'])
    out['delta_u_alpha2'] = float(u2s['delta'])
    return out


# ----------------------------------------------------------------- main
def main():
    gates, out_cells, t1 = {}, [], None
    stamp("decode 1393 cells artifact")
    rows = decode_cells()
    stamp(f"decoded {len(rows)} rows")

    cand = {}
    for rw in rows:
        if rw['band'] == 'PASS':
            m = cand.setdefault(rw['geo'], [0, -9.0])
            m[0] += 1
            m[1] = max(m[1], rw['ratio'])
    stamp(f"candidate geometries with >=1 PASS row: {len(cand)}")
    tier1 = (0.02, 0.02, 0.01, 0.01, 0.99, 1054.0)
    assert tier1 in cand, "1394 witness geometry must decode as a candidate"

    order = sorted(cand, key=lambda g: (-cand[g][1], g[5], g[4], g[0], g[1],
                                        g[2], g[3]))
    order.remove(tier1)
    tested = [tier1] + order[:40]

    gibad = gi_check(rows)
    gates['GI'] = 'PASS' if not gibad else 'FAIL'
    if gibad:
        print(f"GI-violations {gibad[:5]}", flush=True)
    stamp("GI done")

    validity = ['G0', 'GI', 'GS', 'GT', 'GF', 'GD', 'GR', 'GQ']
    run_void = bool(gibad)

    if not run_void:
        t1 = run_geometry(tier1, full=True)
        gs = t1['gs_ok']
        gf = (t1['F0'].real > 0
              and abs(t1['F0'].imag) <= GF_IM_TOL * abs(t1['F0'].real)
              and abs(t1['F0_npw24'].real - t1['F0'].real)
              <= GF_RE_TOL * abs(t1['F0'].real))
        gt = (t1['gt_sym'] <= GT_SYM_TOL and t1['gt_pair'] <= GT_PAIR_TOL
              and t1['gt_jh'] <= GT_JH_TOL)
        gd = abs(t1['lap'] + 1) <= GD_TOL
        gr = abs(t1['A64'] - t1['A']) <= GR_TOL * abs(t1['A'])
        gq = abs(t1['A_quadr'] - 4 * t1['A']) <= GQ_TOL * abs(4 * t1['A'])
        g0 = True
        for name, ok in (('G0', g0), ('GS', gs), ('GT', gt), ('GF', gf),
                         ('GD', gd), ('GR', gr), ('GQ', gq)):
            gates[name] = 'PASS' if ok else 'FAIL'
        run_void = any(gates[k] != 'PASS' for k in validity)
        stamp(f"tier-1 A={t1['A']:.10e} S={t1['S']:.3e} F0={t1['F0']:.6e} "
              f"lap+1={abs(t1['lap'] + 1):.2e} gates={gates}")
        stamp(f"tier-1 extras: A64={t1['A64']:.6e} A2v={t1['A_quadr']:.6e} "
              f"gt=({t1['gt_sym']:.1e},{t1['gt_pair']:.1e},{t1['gt_jh']:.1e}) "
              f"A_alpha2={t1['A_alpha2']:.6e}")
        if not run_void:
            out_cells.append(('tier1', t1, band_of_A(t1['A'], t1['S'])))
            for geo in tested[1:]:
                r = run_geometry(geo)
                if not r['gs_ok']:
                    gates['GS'] = 'FAIL'
                    run_void = True
                if not (r['F0'].real > 0
                        and abs(r['F0'].imag) <= GF_IM_TOL * abs(r['F0'].real)):
                    gates['GF'] = 'FAIL'
                if abs(r['lap'] + 1) > GD_TOL:
                    gates['GD'] = 'FAIL'
                out_cells.append(('tier2', r, band_of_A(r['A'], r['S'])))
                stamp(f"cell {geo}: A={r['A']:.6e} S={r['S']:.3e} "
                      f"F0={r['F0'].real:.4e} |lap+1|={abs(r['lap']+1):.2e} "
                      f"band={out_cells[-1][2]}")
            run_void = run_void or any(gates[k] != 'PASS' for k in validity)

    npos = sum(1 for _, _, b in out_cells if b == 'POS')
    sneg = sum(1 for _, _, b in out_cells if b == 'NEG')
    ntie = sum(1 for _, _, b in out_cells if b == 'TIE')
    witness = next((r['geo'] for _, r, b in out_cells if b == 'POS'), None)
    if run_void:
        print("VERDICT jointWitness=NONE cells=VOID", flush=True)
    else:
        w = ("NONE" if witness is None else
             f"Rf={witness[0]},Ru={witness[1]},eps={witness[2]},"
             f"epsp={witness[3]},rho={witness[4]}+{witness[5]}I")
        print(f"VERDICT jointWitness={w} cells=POS:{npos},NEG:{sneg},"
              f"TIE:{ntie}", flush=True)
    parts = ",".join(f"{k}:{gates.get(k, 'SKIP')}" for k in validity)
    print(f"DONE gates={parts}", flush=True)

    res = dict(wall_s=time.time() - T0, tier1=_ser(t1) if t1 is not None else None,
               candidates=len(cand), tested=len(out_cells),
               untested=len(cand) - len(out_cells),
               census=dict(POS=npos, NEG=sneg, TIE=ntie),
               witness=list(witness) if witness else None,
               void=run_void, gates=gates,
               cells=[dict(kind=k, **_ser(r), band=b)
                      for k, r, b in out_cells])
    with open("docs/proofs/1398_rig_results.json", 'w') as fh:
        json.dump(res, fh, indent=1, default=str)
    with open("docs/proofs/1398_rig_cells.tsv", 'w') as fh:
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
    subprocess.run(["gzip", "-f", "docs/proofs/1398_rig_cells.tsv"], check=True)
    for p in ("docs/proofs/1398_rig_results.json",
              "docs/proofs/1398_rig_cells.tsv.gz"):
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
