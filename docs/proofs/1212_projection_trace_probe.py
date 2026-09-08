"""1212 - Projection-trace renormalization probe (MODEL, preregistered).

Implements record 1212's preregistration: the finite-window projection
owner T_n = Re tr(C_n^* K C_n) with

    cutoffRadius g n = supportRadius g + n + 1
    C_n u            = 1_{[-R_n, R_n]}(t) * (g~ (*) u)(t)   (root factor,
                       output zero extension)
    K                = P_r P_f P_r - P_V                   (stage-3 kernel)

and reads the renormalized finite part

    s_n = T_n - tr(W),   W = C_n^* C_n,

against qw(g) = poleTerm - archTerm - primeSum of F = g (*) g~* (the 1211
exit A: a divergent counterterm in the insertion trace).

Verbatim Lean objects implemented:
  P_r  = multiplication by 1_{t >= log lambda}
  HT   = FT^{-1} . [phi(xi) -> m(xi) phi(-xi)] . FT,
         m(xi) = Gamma(1/2 - 2 pi i xi) / conj(...)  (2-pi FT convention,
         pinned by the Lean readback lemma's Gamma argument)
  E_p  = u - p^{-1/2} * tau_{-log p} u,  (tau_b u)(t) = u(t + b)
  T_S  = E_S . HT . E_S^{-1};  T_S is an INVOLUTION (HT is one and
         conjugation preserves it), so T_S^{-1} = T_S.
  P_f  = orthogonal projection onto ker((I - P_r) T_S), applied as
         I - T_S^* (I-P_r) [ (I-P_r) T_S T_S^* (I-P_r) ]^{-1} (I-P_r) T_S.
         T_S is NOT unitary (E_S is not), so P_f is NOT T_S^{-1} P_r T_S;
         the Gram correction is exactly the "gramCorrected" content.
  P_V  = orthogonal projection onto ran(P_r) cap ran(P_f) by von Neumann
         alternating projections (both are star projections).

W = C_n^* C_n = A^* M_w A is NOT the windowed-diagonal autocorrelation;
its kernel is the sandwich K(t,s) = int conj(g~(r-t)) 1_w(r) g~(r-s) dr.
Because the sampled detector is compactly supported strictly inside the
window, the DISCRETE trace of W is exact and closed-form:
    tr(W) = N_w * sum |g~|^2        (N_w = sampled window cardinality),
so the spectral tail check |tr(W) - sum(top eigenvalues)| / tr(W) is an
exact identity check, not an estimate.  All traces are PLAIN matrix
traces (no dt weight); s_n * dt is the continuum-normalized readout.

Trace method: tr(P_r P_f P_r W) = sum_i lam_i <P_f P_r u_i, P_r u_i> and
tr(P_V W) = lim_k tr((P_r P_f)^k P_r W) are computed on the top-RANK
eigenpairs of W (eigenvalues decay fast; tail gap is monitored against
the exact closed form).  A dense-matrix path validates the spectral path
at a small rung (S0.5).  tr((P_f P_r)^k P_r W) is monotone decreasing in
k (contractions), so the von Neumann stop is one-sided.

Model dials (registered, reported in 1213): lambda = 1, S = {2, 3, 5};
detector = the 1116 k=1 twin at delta = 0 (MODEL, law 65).

Certifies nothing; RH NOT claimed.
"""
import json
import math
import os
import time

import mpmath
import numpy as np
import scipy.special as sp
from scipy.sparse.linalg import LinearOperator, eigsh

mpmath.mp.dps = 80
HERE = os.path.dirname(os.path.abspath(__file__))

# ------------------------------------------------------------------ #
# registered model dials                                             #
# ------------------------------------------------------------------ #
# defaults are the 1213 registered values; the 1224 sec.3a sweep overrides
# them through PROBE_LAMBDA / PROBE_S (MODEL-labeled probe, law 65).
LAMBDA = float(os.environ.get("PROBE_LAMBDA", "1.0"))
S_PRIMES = [int(x) for x in os.environ.get("PROBE_S", "2,3,5").split(",")]
LOG_P = [math.log(p) for p in S_PRIMES]
C_P = [1.0 / math.sqrt(p) for p in S_PRIMES]

R0 = 10.05
NS = [8, 16, 32, 64]
N_COARSE, N_FINE = 8192, 16384
PAD = 24.0
RANK = 320                 # spectral-trace rank
TRACE_TOL = 1e-10          # eigsh relative tolerance
VN_TOL = 1e-11             # von Neumann trace stabilization (relative)
VN_MAX = 60
VN_CHECK = 12              # alternating-projection cross-check length
DENSE_N = 2048             # dense validation rung (S0.5)
PV_TAU = 1e-8              # spectral pseudo-inverse threshold (G_C split)

# 1116 qw-side conventions (verbatim: constants, quadrature grades,
# float64-vs-mpmath split of the correction solve, Simpson arch term)
LOG4PI_GAMMA = float(mpmath.log(4 * mpmath.pi) + mpmath.euler)
NEXP = 9
A_DET = NEXP + 1
QL = 28.0
NQ = 1 << 15
DQ = 2 * QL / NQ
QS = (np.arange(NQ) - NQ // 2) * DQ
M_GL, M_CHK = 900, 1400
_GLX, _GLW = np.polynomial.legendre.leggauss(M_GL)
_MOMW = None  # set after chi() is defined


def chi1(u):
    return math.exp(-1.0 / (1.0 - u * u)) if -1.0 < u < 1.0 else 0.0


def simpson_uniform(y, dx):
    """Composite Simpson on a uniform grid (last interval falls back to
    trapezoid when the sample count is even)."""
    n = len(y)
    if n % 2 == 0:
        tail = 0.5 * dx * (y[-1] + y[-2])
        y = y[:-1]
    else:
        tail = 0.0
    y3 = y.reshape(-1, 3)
    return float(tail + (dx / 3.0)
                 * (y3[:, 0] + 4.0 * y3[:, 1] + y3[:, 2]).sum())


def moment_rows(zs, M):
    """(nz, M) float64 rows of B^(m)(z) = sum w chi x^m e^{z x}."""
    E = np.exp(np.outer(np.asarray(zs, dtype=complex), _GLX))
    xf = _MOMW.copy()
    out = np.empty((E.shape[0], M), dtype=complex)
    for m in range(M):
        out[:, m] = E @ xf
        xf = xf * _GLX
    return out


def moment_row_mp(z, M):
    x, w = np.polynomial.legendre.leggauss(M_CHK)
    zm = mpmath.mpc(z)
    xm = [mpmath.mpf(v) for v in x]
    wm = [mpmath.mpf(w[k]) * mpmath.mpf(chi1(x[k])) for k in range(len(x))]
    Em = [mpmath.exp(zm * xm[k]) for k in range(len(x))]
    row, powers = [], [mpmath.mpf(1)] * len(x)
    for _ in range(M):
        row.append(mpmath.fsum(wm[k] * powers[k] * Em[k]
                               for k in range(len(x))))
        powers = [powers[k] * xm[k] for k in range(len(x))]
    return row


# ------------------------------------------------------------------ #
# the 1116 k=1 detector at delta = 0 (verbatim machinery)             #
# ------------------------------------------------------------------ #
def chi(u):
    v = np.asarray(u, dtype=float)
    out = np.zeros_like(v)
    m = (v > -1.0) & (v < 1.0)
    out[m] = np.exp(-1.0 / (1.0 - v[m] ** 2))
    return out


_MOMW = _GLW * chi(_GLX)


def circular_conv_centered(p, q):
    pp = np.fft.ifftshift(p)
    qq = np.fft.ifftshift(q)
    return np.fft.fftshift(np.fft.ifft(np.fft.fft(pp) * np.fft.fft(qq))) * DQ


def load_gammas():
    return [float(mpmath.im(mpmath.zetazero(j))) for j in range(1, 10)]


def build_g_delta0():
    """1116 correction solve (mpmath, verbatim solve path) + float64
    assembly of g = e^{x/2} (chi^{*NEXP} (*) corr) on the qw grid."""
    rho = complex(0.5, load_gammas()[0])
    R = 18.0 + abs(2 - rho)
    nodes = []

    def add(z, v):
        for wz, _ in nodes:
            if abs(wz - z) < 1e-12:
                return
        nodes.append((complex(z), complex(v)))

    add(rho, 1)
    add(1 - np.conj(rho), -1)
    add(np.conj(rho), 0)
    add(1 - rho, 0)
    add(rho + 0.5, -1)
    add(0.5, 0)
    add(1.0, 0)
    add(1.5, 0)
    for gm in load_gammas():
        for sgn in (1, -1):
            z = 0.5 + 1j * sgn * gm
            if abs(z - rho) <= R:
                add(z, 0)
    assert len(nodes) == 13, f"node structure changed: {len(nodes)}"
    zs = [z for z, _ in nodes]
    Ms = len(nodes)
    A = mpmath.zeros(Ms, Ms)
    for i, z in enumerate(zs):
        for m, v in enumerate(moment_row_mp(z, Ms)):
            A[i, m] = v
    Bz = moment_rows(zs, Ms)[:, 0]          # float64, verbatim 1116 path
    rhs = mpmath.matrix([mpmath.mpc(v) / mpmath.power(mpmath.mpc(b), NEXP)
                         for (_, v), b in zip(nodes, Bz)])
    sol = mpmath.lu_solve(A, rhs)
    res = float(mpmath.norm(A * sol - rhs) / max(mpmath.norm(rhs), 1))
    a = np.array([complex(sol[m]) for m in range(Ms)])
    base = chi(QS)
    corr = np.zeros(NQ, dtype=complex)
    xp = np.ones_like(QS)
    for am in a:
        corr += am * xp * base
        xp = xp * QS
    h = corr
    for _ in range(NEXP):
        h = circular_conv_centered(h, base)
    return h * np.exp(QS / 2), dict(residual=res,
                                    max_abs_a=float(np.abs(a).max()))


def qw_terms(g):
    """qw(g) = pole - arch - prime of F = g (*) g~* (1116 machinery)."""
    cvec = np.conj(g[(-np.arange(NQ)) % NQ])
    F = circular_conv_centered(g, cvec)
    f0 = float((np.abs(g) ** 2).sum() * DQ)
    pos0 = NQ // 2
    yp = QS[pos0:]
    Fp = F[pos0:]
    Fm = F[(NQ - np.arange(pos0, NQ)) % NQ]
    num = np.exp(yp / 2) * (Fp + Fm) - 2 * f0
    integ = np.empty_like(num)
    integ[1:] = num[1:] / (2 * np.sinh(yp[1:]))
    integ[0] = f0 / 2.0
    tail = f0 * math.log(math.tanh(yp[-1] / 2))
    arch = LOG4PI_GAMMA * f0 + simpson_uniform(integ.real, DQ) + tail
    qmax = int(math.exp(2.0 * A_DET))
    N = (qmax - 1) // 2
    sieve = np.ones(N, dtype=bool)
    sieve[0] = False
    for p in range(3, int(math.isqrt(qmax)) + 1, 2):
        if sieve[(p - 1) // 2]:
            sieve[(p * p - 1) // 2::p] = False
    primes = np.concatenate(([2], np.nonzero(sieve)[0] * 2 + 1))
    lq = np.log(primes.astype(float))
    psum = float((lq / np.sqrt(primes) * (
        np.interp(lq, QS, F.real) + np.interp(-lq, QS, F.real))).sum())
    for pr in primes:
        pr = int(pr)
        if pr * pr > qmax:
            break
        pk, lp = pr * pr, math.log(pr)
        while pk <= qmax:
            lv = math.log(pk)
            psum += lp / math.sqrt(pk) * (
                float(np.interp(lv, QS, F.real))
                + float(np.interp(-lv, QS, F.real)))
            pk *= pr
    pole = float(np.real(np.trapezoid(np.exp(QS / 2) * F, dx=DQ)
                         + np.trapezoid(np.exp(-QS / 2) * F, dx=DQ)))
    return dict(f0=f0, arch=arch, prime=psum, pole=pole,
                qw=pole - arch - psum)


# ------------------------------------------------------------------ #
# operator machinery on a centered box                               #
# ------------------------------------------------------------------ #
def scattering_phase(xi):
    # unit-modulus phase Gamma(1/2 - 2 pi i xi) / conj(...): computed via
    # exp(2i arg) because the raw quotient 0/0-overflows at fine grids
    # (|Gamma| ~ e^{-pi |xi|} underflows below 1e-308 for |2 pi xi| >~ 400,
    # i.e. exactly the official fine-ladder frequencies); there the
    # detector's spectral weight is e^{-400}, so the angle(0)=0 -> phase 1
    # convention is numerically inert.
    g = sp.gamma(0.5 - 2j * np.pi * np.asarray(xi, dtype=float))
    return np.exp(2j * np.angle(g))


class Grid:
    """Centered box [-B, B], N samples, TORUS conventions.

    Lean tau_b u(t) = u(t+b) equals a Fourier-multiplier shift
    e^{+2 pi i xi b}; E_p = 1 - c_p tau_{-log p} is therefore DIAGONAL
    in Fourier with multiplier e(xi) = prod_p (1 - c_p e^{-2 pi i xi lp}).
    Every E/HT/T_S action below is one FT + pointwise multiplier (+ the
    reflected readback for HT), so adjoints are EXACT (conj multiplier)
    and T_S is an exact involution on the torus to roundoff.  |e| is
    bounded in [prod(1-c_p), prod(1+c_p)] ~ [0.25, 3.9], so no blowup.
    """

    def __init__(self, B, N):
        self.B, self.N = B, N
        self.dt = 2 * B / N
        self.t = (np.arange(N) - N // 2) * self.dt
        self.freq = np.fft.fftshift(np.fft.fftfreq(N, d=self.dt))
        # 1224 sec.3a: P_r = 1_{t >= log lambda}; at the 1213 registered
        # lambda = 1.0 this is the committed t >= 0 threshold verbatim.
        self.pos = self.t >= math.log(LAMBDA)
        self.neg = ~self.pos
        self.phase = scattering_phase(self.freq)
        e_mult = np.ones_like(self.freq, dtype=complex)
        for cp, lp in zip(C_P, LOG_P):
            e_mult = e_mult * (1.0 - cp * np.exp(-2j * np.pi * self.freq * lp))
        self.e_mult = e_mult

    def ft(self, U):
        return np.fft.fftshift(
            np.fft.fft(np.fft.ifftshift(U, axes=0), axis=0), axes=0) * self.dt

    def ift(self, PHI):
        return np.fft.fftshift(
            np.fft.ifft(np.fft.ifftshift(PHI, axes=0), axis=0), axes=0) / self.dt

    def ht(self, U):
        """(HTu)^(xi) = m(xi) phi(-xi); the reflected-index map on the
        centered grid is k -> (-k) mod N = roll(reverse, 1) (the bare
        [::-1] is off by one bin and breaks the involution)."""
        phi = self.ft(U)
        return self.ift(self.phase[:, None] * np.roll(phi[::-1], 1, axis=0))

    def apply_e(self, U, inverse=False, adjoint=False):
        """E_S (diag e), E_S^{-1} (diag 1/e), adjoints (conj)."""
        mult = 1.0 / self.e_mult if inverse else self.e_mult
        if adjoint:
            mult = np.conj(mult)
        return self.ift(mult[:, None] * self.ft(U))

    def apply_ts(self, U, adjoint=False):
        """T_S = E_S . HT . E_S^{-1}:  u^(xi) -> d(xi) u^(-xi) with
        d(xi) = m(xi) e(xi)/e(-xi)  (the ratio must pair with xi AFTER
        the reflection).  The adjoint of a reflected multiplier is the
        reflected conjugate:  d*(xi) = conj(d(-xi))."""
        Uf = self.ft(U)
        e_rev = np.roll(self.e_mult[::-1], 1)   # e(-xi), same off-by-one
        d = self.phase * (self.e_mult / e_rev)
        if adjoint:
            d = np.conj(np.roll(d[::-1], 1))
        return self.ift(d[:, None] * np.roll(Uf[::-1], 1, axis=0))


class Cn:
    """Root factor C_n = M_w A with zero-extension linear convolution,
    its adjoint, and W = C_n^* C_n = A^* M_w A (sandwich, matrix-free).

    Embedding: re-center via ifftshift (t=0 at index 0), then zero-pad
    the MIDDLE (|t| in [B, 2B) = the padding), convolve at length 2N,
    and crop+re-center by concatenating the two time-halves back.  The
    adjoint kernel is conj g~(-t) in centered coords
    (= roll(conj(g~[::-1]), 1), the same half-sample reflection fix as
    the HT), evaluated in the SAME embedding, so A^* is exact."""

    def __init__(self, grid, gt, win):
        self.grid = grid
        self.win = win[:, None]          # cutoff window 1_{|t| <= Rn}
        self.N = N = grid.N
        self.half = half = N // 2

        def to_padded(arr):
            s = np.fft.ifftshift(arr)
            return np.concatenate([s[:half], np.zeros(N), s[half:]])

        self.Kf = np.fft.fft(to_padded(gt))
        self.Kaf = np.fft.fft(to_padded(np.roll(np.conj(gt[::-1]), 1)))

    def _conv(self, U, KF):
        N, half = self.N, self.half
        Us = np.fft.ifftshift(U, axes=0)
        U2 = np.zeros((2 * N, U.shape[1]), dtype=complex)
        U2[:half] = Us[:half]
        U2[N + half:] = Us[half:]
        r2 = np.fft.ifft(np.fft.fft(U2, axis=0) * KF[:, None], axis=0)
        return np.concatenate([r2[N + half:], r2[:half]], axis=0)

    def fwd(self, U):
        return self.win * self._conv(U, self.Kf)

    def adj(self, V):
        return self._conv(V, self.Kaf)

    def Wmv(self, U):
        return self.adj(self.win * self._conv(U, self.Kf))


class PfEngine:
    """Matrix-free P_f = I - T_S^* (I-P_r) G^{-1} (I-P_r) T_S with
    G = (I-P_r) T_S T_S^* (I-P_r), Cholesky pre-factorized."""

    def __init__(self, grid, chunk=64):
        self.grid = grid
        neg = grid.neg
        idx = np.nonzero(neg)[0]
        m = len(idx)
        Gm = np.empty((m, m), dtype=complex)
        for j0 in range(0, m, chunk):
            cols = idx[j0:j0 + chunk]
            E = np.zeros((grid.N, len(cols)), dtype=complex)
            E[cols, np.arange(len(cols))] = 1.0
            # G = P_neg T_S T_S^* P_neg: NO projection between the two
            # T_S factors (the sandwich would be a different, singular
            # operator); only the outer P_negs.
            V = grid.apply_ts(E, adjoint=True)
            Gm[:, j0:j0 + chunk] = (grid.apply_ts(V) * neg[:, None])[neg, :]
        Gm = (Gm + Gm.conj().T) / 2
        dg = np.abs(np.diag(Gm))
        scale = float(dg.max())
        reg = 1e-12
        try:
            self.L = np.linalg.cholesky(Gm + reg * scale * np.eye(m))
        except np.linalg.LinAlgError:
            reg = 1e-8
            self.L = np.linalg.cholesky(Gm + reg * scale * np.eye(m))
        self.reg = reg * scale
        self.neg = neg
        self.cond_hint = float(dg.max() / max(dg.min(), 1e-300))

    def apply(self, U):
        neg = self.neg
        W = self.grid.apply_ts(U) * neg[:, None]
        V = np.zeros_like(W)
        V[neg, :] = np.linalg.solve(self.L.conj().T,
                                    np.linalg.solve(self.L, W[neg, :]))
        return U - self.grid.apply_ts(V, adjoint=True)


class PvEngine:
    """Matrix-free DIRECT projector onto ran(P_r) cap ran(P_f):

        P_V = I - C^* (C C^*)^dagger C,   C = P_neg . T_S . P_r,

    with the Moore-Penrose pseudo-inverse of the Gram G_C = C C^*
    realized by a SPECTRAL SPLIT: G_C is measured rank-deficient
    (eigenvalues either ~1e0 or ~1e-16 in scale, nothing in between
    over 12+ decades), so thresholding at PV_TAU . scale realizes the
    exact pseudo-inverse and I - C^* G_C^dagger C is EXACTLY the
    orthogonal projector onto ker(C) (standard SVD identity).  A plain
    regularized inverse (G_C + reg)^{-1} is NOT a projector on the
    rank-deficient Gram (idempotency error ~ reg / lambda_small, which
    is exactly the 1.7e-4 smoke failure that motivated this change).
    This replaces the von Neumann alternating iteration (measured
    Friedrichs rate ~0.998/iter: 1e-11 would need ~1.3e4 iterations);
    the projected object is identical, and the alternating sequence is
    retained as a one-sided cross-check in dense_validation."""

    def __init__(self, grid, chunk=64):
        self.grid = grid
        neg = grid.neg
        idx = np.nonzero(neg)[0]
        m = len(idx)
        Gm = np.empty((m, m), dtype=complex)
        for j0 in range(0, m, chunk):
            cols = idx[j0:j0 + chunk]
            E = np.zeros((grid.N, len(cols)), dtype=complex)
            E[cols, np.arange(len(cols))] = 1.0
            V = grid.pos[:, None] * grid.apply_ts(E, adjoint=True)
            Gm[:, j0:j0 + chunk] = (grid.apply_ts(V) * neg[:, None])[neg, :]
        Gm = (Gm + Gm.conj().T) / 2
        ev, Q = np.linalg.eigh(Gm)
        ev = ev.real
        scale = float(ev.max())
        keep = ev > PV_TAU * scale
        self.rank = int(keep.sum())
        self.ev_keep = ev[keep]
        self.Q = Q[:, keep]
        # spectral-gap health: smallest kept / |largest dropped|
        # (eigh is ASCENDING; kept = top `rank`, so the largest dropped
        # sits at index m - rank - 1, not rank - 1)
        if self.rank < m:
            self.gap = float(self.ev_keep[-1]
                             / max(abs(ev[m - self.rank - 1]), 1e-300))
        else:
            self.gap = float('inf')
        self.neg = neg
        self.cond_hint = float(ev[keep].max() / max(ev[keep].min(), 1e-300))

    def apply(self, U):
        neg = self.neg
        W = self.grid.apply_ts(U * self.grid.pos[:, None]) * neg[:, None]
        # pseudo-inverse application on the kept spectral subspace
        coef = (self.Q.conj().T @ W[neg, :]) / self.ev_keep[:, None]
        V = np.zeros_like(W)
        V[neg, :] = self.Q @ coef
        # I - C^*(CC^*)^dagger C is the EXACT orthogonal projector onto
        # ker(C); the trailing P_r (commuting with it) cuts H_neg -> M.
        return self.grid.pos[:, None] \
            * (U - self.grid.pos[:, None]
               * self.grid.apply_ts(V, adjoint=True))


def bulk_eig(cn, rank):
    """Top-rank eigenpairs of the PSD sandwich operator W."""
    N = cn.grid.N

    def mv(v):
        return cn.Wmv(v.reshape(N, -1)).ravel()
    op = LinearOperator((N, N), mv, dtype=complex)
    vals, vecs = eigsh(op, k=rank, which="LA", tol=TRACE_TOL, maxiter=5000)
    order = np.argsort(vals.real)[::-1]
    return vals.real[order], vecs[:, order]


def run_traces(grid, pf, pv, vals, vecs):
    """term1 = tr(P_r P_f P_r W), term_pv = tr(P_V W) on the spectral
    basis, both DIRECT (one P_f application; one P_V application)."""
    U = vecs * grid.pos[:, None]
    U1 = pf.apply(U)
    U1 *= grid.pos[:, None]
    term1 = float(np.sum(vals * np.einsum('ij,ij->j', U1.conj(), U).real))
    X = pv.apply(vecs)
    term_pv = float(np.sum(vals * np.einsum('ij,ij->j', X.conj(), X).real))
    return term1, term_pv, 0, True, [term_pv]


def rung(n, N, sample, f0_cont, pad=None):
    Rn = R0 + n + 1
    grid = Grid(Rn + (PAD if pad is None else pad), N)
    gt = sample(grid.t)
    f0d = float((np.abs(gt) ** 2).sum())
    win = np.abs(grid.t) <= Rn
    cn = Cn(grid, gt, win)
    Nw = int(win.sum())
    bulk = Nw * f0d                      # exact discrete tr(W), closed form
    vals, vecs = bulk_eig(cn, RANK)
    captured = float(vals.sum())
    tail_gap = (bulk - captured) / bulk
    pf = PfEngine(grid)
    pv = PvEngine(grid)
    term1, term_pv, _, _, _ = run_traces(grid, pf, pv, vals, vecs)
    Tn = term1 - term_pv
    return dict(n=n, N=N, Rn=Rn, dt=grid.dt, bulk=bulk,
                bulk_cont=2 * Rn * f0_cont, f0_disc=f0d,
                captured=captured, tail_gap=tail_gap,
                term1=term1, term_pv=term_pv, Tn=Tn, sn=Tn - bulk,
                sn_dt=(Tn - bulk) * grid.dt,
                pf_cond_hint=pf.cond_hint, pv_cond_hint=pv.cond_hint,
                pv_rank=pv.rank, pv_neg_dim=len(pv.neg), pv_gap=pv.gap)


def dense_validation(sample, f0_cont):
    """S0.5: dense W = C_n^* C_n at DENSE_N vs the spectral path."""
    n = 8
    Rn = R0 + n + 1
    grid = Grid(Rn + PAD, DENSE_N)
    gt = sample(grid.t)
    f0d = float((np.abs(gt) ** 2).sum())
    win = np.abs(grid.t) <= Rn
    cn = Cn(grid, gt, win)
    Nw = int(win.sum())
    bulk = Nw * f0d
    eye = np.eye(grid.N, dtype=complex)
    Wd = np.empty_like(eye)
    for j in range(grid.N):
        Wd[:, j] = cn.Wmv(eye[:, j:j + 1])[:, 0]
    tr_dense = float(np.einsum('ii->', Wd).real)
    herm = float(np.abs(Wd - Wd.conj().T).max()
                 / max(float(np.abs(Wd).max()), 1e-300))
    pf = PfEngine(grid)
    pv = PvEngine(grid)
    vals, vecs = bulk_eig(cn, RANK)
    term1, term_pv, _, _, _ = run_traces(grid, pf, pv, vals, vecs)
    Tn_spec = term1 - term_pv
    # dense DIRECT P_V trace and dense term1
    tr_pv_dense = float(np.einsum('ii->', pv.apply(Wd)).real)
    X = pf.apply(Wd * grid.pos[:, None])
    term1_dense = float((grid.pos * np.diag(X)).sum().real)
    Tn_dense = term1_dense - tr_pv_dense
    # alternating-projection cross-check (one-sided: tr(U_k) decreases
    # to tr(P_V W) at the measured Friedrichs rate ~0.998/iter)
    U = Wd * grid.pos[:, None]
    tr_hist = [float(np.einsum('ii->', U).real)]
    for _ in range(VN_CHECK):
        U = pf.apply(U)
        U *= grid.pos[:, None]
        tr_hist.append(float(np.einsum('ii->', U).real))
    mono = all(tr_hist[k + 1] <= tr_hist[k] + 1e-9 * abs(tr_hist[k])
               for k in range(len(tr_hist) - 1))
    return dict(N=DENSE_N, tr_dense=tr_dense, bulk=bulk,
                tr_rel=abs(tr_dense - bulk) / bulk, herm_err=herm,
                Tn_spec=Tn_spec, Tn_dense=Tn_dense,
                term1_rel=abs(term1_dense - term1) / max(abs(term1), 1e-300),
                pv_rel=abs(tr_pv_dense - term_pv) / max(abs(term_pv), 1e-300),
                rel=abs(Tn_dense - Tn_spec) / max(abs(Tn_dense), 1e-300),
                vn_check_iters=VN_CHECK, vn_monotone=mono,
                vn_last=tr_hist[-1],
                bulk_cont=2 * Rn * f0_cont)


def sample_fn(g):
    """Sample the detector on an operator grid; ZERO outside the qw grid
    [-QL, QL] (np.interp would clamp to the endpoint value, dragging the
    FFT noise floor out as a constant tail and destroying the exact
    trace closed form)."""
    def sample(tq):
        out = np.zeros(len(tq), dtype=complex)
        m = np.abs(tq) <= QL
        tqm = tq[m]
        out[m] = np.interp(tqm, QS, np.real(g)) \
            + 1j * np.interp(tqm, QS, np.imag(g))
        return out
    return sample


def main():
    smoke = os.environ.get("PROBE_SMOKE") == "1"
    if smoke:
        globals()["RANK"] = 96
        globals()["DENSE_N"] = 512
    ns = [4] if smoke else NS
    pairs = [(1024, 2048)] if smoke else [(N_COARSE, N_FINE)]
    t0 = time.time()
    mode = "SMOKE" if smoke else "OFFICIAL"
    print(f"== 1212 projection-trace renormalization probe ({mode}) ==")
    g, meta = build_g_delta0()
    print(f"S0.1 correction residual {meta['residual']:.2e} "
          f"|a|max {meta['max_abs_a']:.2e}")
    qwv = qw_terms(g)
    print(f"S0.1 f0={qwv['f0']:.6e} arch={qwv['arch']:+.6e} "
          f"prime={qwv['prime']:+.6e} pole={qwv['pole']:+.6e} "
          f"qw={qwv['qw']:+.6e}")
    row0 = None
    try:
        with open(os.path.join(HERE, "1116_d1_model.json")) as fh:
            rows = [r for r in json.load(fh).get("results", [])
                    if abs(float(r.get("delta", 1.0))) < 1e-12]
        if rows:
            row0 = rows[0]
    except (OSError, ValueError, KeyError, TypeError):
        row0 = None
    if row0 is None:
        print("S0.3 SKIP: committed 1116 delta=0 row unavailable")
    else:
        d_f0 = abs(qwv["f0"] - row0["f0"]) / abs(row0["f0"])
        d_ar = abs(qwv["arch"] - row0["arch"]) \
            / max(abs(row0["arch"]), 1e-30)
        d_pr = abs(qwv["prime"] - row0["prime"]) \
            / max(abs(row0["prime"]), 1e-30)
        print(f"S0.3 vs committed 1116 delta=0 row: f0 {d_f0:.2e} "
              f"arch {d_ar:.2e} prime {d_pr:.2e}")
        assert d_f0 < 1e-6 and d_ar < 1e-6 and d_pr < 1e-6, \
            "qw machinery does not reproduce the committed 1116 row"
    # S0.2 operator conventions on a small grid
    grid = Grid(R0 + PAD, 2048)
    u = np.exp(-grid.t ** 2 / 4).astype(complex)[:, None]
    nrm = float(np.linalg.norm(u))
    ht1 = grid.ht(u)
    inv_err = float(np.linalg.norm(grid.ht(ht1) - u) / nrm)
    read = grid.ift(grid.phase[:, None]
                    * np.roll(grid.ft(u)[::-1], 1, axis=0))
    read_err = float(np.abs(read - ht1).max() / nrm)
    e_err = float(np.linalg.norm(grid.apply_e(grid.apply_e(u, True)) - u)
                  / nrm)
    ea_err = float(np.linalg.norm(
        grid.apply_e(grid.apply_e(u, True, adjoint=True),
                     adjoint=True) - u) / nrm)
    ts_err = float(np.linalg.norm(grid.apply_ts(grid.apply_ts(u)) - u) / nrm)
    print(f"S0.2 HT invol {inv_err:.2e}  readback {read_err:.2e}  "
          f"E o E^-1 {e_err:.2e}  E* o (E^-1)* {ea_err:.2e}  "
          f"T_S invol {ts_err:.2e}")
    assert inv_err < 1e-8 and read_err < 1e-8 and e_err < 1e-9 \
        and ea_err < 1e-9 and ts_err < 1e-7, "S0.2 FAILED"
    # S0.4 P_f projector laws on the small grid
    pf = PfEngine(grid)
    rng = np.random.default_rng(1212)
    Vr = rng.standard_normal((grid.N, 4)) \
        + 1j * rng.standard_normal((grid.N, 4))
    PV = pf.apply(Vr)
    idem = float(np.linalg.norm(pf.apply(PV) - PV) / np.linalg.norm(PV))
    s1 = np.vdot(Vr, PV)
    s2 = np.vdot(PV, Vr)
    selfadj = float(abs(s1 - s2) / max(abs(s1), 1e-300))
    print(f"S0.4 P_f idempotent {idem:.2e}  self-adjoint {selfadj:.2e}  "
          f"(G cond hint {pf.cond_hint:.2e})")
    assert idem < 1e-6 and selfadj < 1e-6, "S0.4 P_f projector laws FAILED"
    pv = PvEngine(grid)
    QV = pv.apply(Vr)
    idem_pv = float(np.linalg.norm(pv.apply(QV) - QV) / np.linalg.norm(QV))
    t1 = np.vdot(Vr, QV)
    t2 = np.vdot(QV, Vr)
    selfadj_pv = float(abs(t1 - t2) / max(abs(t1), 1e-300))
    posleak = float(np.linalg.norm(QV * (~grid.pos)[:, None]
                                   / max(np.linalg.norm(QV), 1e-300)))
    print(f"S0.4 P_V idempotent {idem_pv:.2e}  self-adjoint "
          f"{selfadj_pv:.2e}  ran(P_V) within t>=0 {posleak:.2e}  "
          f"(G rank {pv.rank}/{len(pv.neg)}, spectral gap "
          f"{pv.gap:.1e}, cond hint {pv.cond_hint:.2e})")
    assert idem_pv < 1e-6 and selfadj_pv < 1e-6 and posleak < 1e-6, \
        "S0.4 P_V projector laws FAILED"
    sample = sample_fn(g)
    # S0.5 dense validation
    dv = dense_validation(sample, qwv["f0"])
    print(f"S0.5 N={dv['N']}: tr(W) dense vs closed form "
          f"{dv['tr_rel']:.2e}  herm {dv['herm_err']:.1e}  "
          f"Tn dense-vs-spectral {dv['rel']:.2e}  "
          f"term1 rel {dv['term1_rel']:.2e}  pv rel {dv['pv_rel']:.2e}  "
          f"(VN {dv['vn_check_iters']}-step monotone={dv['vn_monotone']}, "
          f"tr after {dv['vn_last']:.6e})")
    assert dv["tr_rel"] < 1e-10 and dv["herm_err"] < 1e-10 \
        and dv["rel"] < 1e-6, "S0.5 FAILED"
    # S0.6 wrap gate (FIXED-dt design): grow the box PAD 24 -> 40 while
    # holding dt = T/N fixed (N scaled proportionally), so bulk and the
    # quadrature are unchanged and any Tn drift is genuine box-content
    # wrapping, not the dt artifact that the first (miscalibrated)
    # absolute-sn gate conflated.  Detector content spans |t| <= QL+3.4
    # = 31.4 < box edge Rn+24 = 43.05, so nothing wraps at either pad;
    # the gate certifies that expectation numerically on Tn/bulk.
    Nw_gate = pairs[0][1]
    r24 = rung(8, Nw_gate, sample, qwv["f0"])
    dt24 = r24["dt"]
    N40 = 2 * int(round((2 * r24["Rn"] + 80.0) / dt24 / 2))
    r40 = rung(8, N40, sample, qwv["f0"], pad=40.0)
    ratio24 = r24["Tn"] / r24["bulk"]
    ratio40 = r40["Tn"] / r40["bulk"]
    wrap_rel = abs(ratio24 - ratio40) / max(abs(ratio24), 1e-300)
    print(f"S0.6 wrap gate n=8 fixed-dt: N {Nw_gate}->{N40}, "
          f"dt {dt24:.6f}->{r40['dt']:.6f}  "
          f"Tn/bulk(24)={ratio24:+.9f}  Tn/bulk(40)={ratio40:+.9f}  "
          f"rel drift {wrap_rel:.2e}")
    # tolerance 1e-3: the gate exists to catch box-content wrapping (an
    # O(wrap-mass) effect); the measured drift at smoke dt is 2.9e-4 and
    # is a smooth spectral-resolution effect (dxi = 1/T and dt both
    # change), scaling down with the ladder's finer dt.
    assert wrap_rel < 1e-3, "S0.6 wrap contamination FAILED"
    del r24, r40
    wrap_gate = dict(n=8, N24=Nw_gate, N40=N40, dt24=dt24,
                     ratio24=ratio24, ratio40=ratio40, rel_drift=wrap_rel)
    # ladder: each registered rung is a dt-refinement PAIR (coarse,
    # fine = coarse/2); both grades run at every n (the first official
    # invocation iterated only the fine grade -- loop bug, disclosed in
    # record 1213 -- and was completed by this corrected invocation).
    results = []
    for n in ns:
        for c, f in pairs:
            for N in (c, f):
                t1 = time.time()
                row = rung(n, N, sample, qwv["f0"])
                secs = round(time.time() - t1, 1)
                row.update(tag=c, secs=secs)
                results.append(row)
                print(f"n={n:3d} {c:6d} N={N:5d} bulk={row['bulk']:.6e} "
                      f"gap={row['tail_gap']:.1e} "
                      f"term1/b={row['term1']/row['bulk']:.6f} "
                      f"pv/b={row['term_pv']/row['bulk']:.6f} "
                      f"Tn/b={row['Tn']/row['bulk']:+.6f} "
                      f"sn_dt={row['sn_dt']:+.6e} "
                      f"pv_rank={row['pv_rank']}/{row['pv_neg_dim']} "
                      f"[{secs}s]")
            if smoke:
                out = "1212_probe_smoke.json"
            else:
                # 1224 sec.3a(f): the sweep writes NEW files only; the
                # committed official 1212 JSON is never overwritten.
                out = os.environ.get("PROBE_OUT", "1212_probe_results.json")
            with open(os.path.join(HERE, out), "w") as fh:
                json.dump(dict(record="1212", mode=mode, model=True,
                               lambda_=LAMBDA, S=S_PRIMES, qw=qwv,
                               dense_validation=dv, wrap_gate=wrap_gate,
                               results=results),
                          fh, indent=1)
    if not smoke:
        print(f"\nqw target {qwv['qw']:+.6e}; sn_dt column is the "
              "continuum-normalized finite part")
    print(f"total {time.time() - t0:.0f}s  (MODEL; certifies nothing; "
          "RH NOT claimed)")


if __name__ == "__main__":
    main()
