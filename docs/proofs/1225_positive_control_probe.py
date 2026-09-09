"""1225 - Positive-control probe for the projection-trace readback (MODEL).

Implements record 1225 section 4: the SAME 1212 machinery (verbatim operator
conventions, same ladder, same renormalization), run for the first time on a
test where a successful readback is POSSIBLE.  All earlier subjects (1213,
1224) carried healthy detector data, which forces qw g < 0 through the
committed iff chain (record 1225 F1) while the sandwich trace is forced
>= 0 through cutoffProjectionOperator_isPositive (F2); FP != qw was
guaranteed by sign before any digit was computed.

The control g is built by the identical 1116 moment-solve machinery with:

  * nodes = {(1/2,0), (1,0), (3/2,0)} ONLY - the +1/2-shifted model
    convention of the committed cc20TripleFiniteVanishingSet {0,1/2,1};
    the rho pair, the +/-1 detection targets and the on-line-zero nodes are
    all DROPPED (the rho node is exactly what carried the forced negativity);
  * bump support scaled by CONTROL_EPS so the realized g support stays
    strictly inside [-log 2/2, log 2/2] (gate C2, read at the 1e-8 relative
    floor after peak-1 rescale, per registered amendment A1-A3);
  * a free normalization node (2.0, raw moment rhs 1, no B^NEXP division)
    keeps the system square with O(1e6) coefficients;
  * gate C3 is a significance guard on the ROOT prime-free regime
    (|pole - prime|/|arch| < 1e-3, amended from 1e-9: the node set pins lap h,
    not the square's pole residue; the committed baseline itself carries
    pole/arch = 8.7e-5).  Comparison target is the 1213 statistic
    qw_model = pole - arch - prime;
  * a pre-ladder sign gate: the run is informative ONLY if the measured
    qw is strictly positive; qw <= 0 exits ABORTED-UNINFORMATIVE (the
    registered branch of sec.4 C5; a forced-negative control would repeat
    the 1213 structure and certify nothing).

Finite-window owner and trace conventions are unchanged from 1212:
T_n = Re tr(C_n^* K C_n), K = P_r P_f P_r - P_V, s_n = T_n - tr(W),
sn_dt = (T_n - tr W) * dt; MATCH branch reads sn_dt(fine, n=64)/qw within
0.01.  Everything here is a MODEL-twin statement (law 65); nothing is a
Lean-side fact.  Certifies nothing; RH NOT claimed.

(Header below kept verbatim from 1212 for convention reference:)

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
# 1225 sec.4: the control bump scale; realized support radius is bounded by
# (NEXP + 1) * CONTROL_EPS, gate C2 requires it strictly below log(2)/2.
CONTROL_EPS = float(os.environ.get("CONTROL_EPS", "0.03"))
LOG_P = [math.log(p) for p in S_PRIMES]
C_P = [1.0 / math.sqrt(p) for p in S_PRIMES]

R0 = 10.05
NS = [8, 16, 32, 64]
N_COARSE, N_FINE = 8192, 16384
PAD = 24.0
RANK = int(os.environ.get("PROBE_RANK", "320"))   # spectral-trace rank;
# A4/A4b (1225 sec.4): smallest rank of the registered ladder
# {320,640,1280,2560,5120} passing S0.5 at DENSE_N=2048 AND carrying
# tail_gap < 1e-10 on every official rung (measured rank-diag: use 2560).
DV_RANK = 1280   # A4b: fixed validation-grid rank (exact capture at 1024)
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


def build_g_control(eps):
    """1225 sec.4 control builder: triple vanishing ONLY, ROOT-scaled bump.

    Nodes = {(1/2,0), (1,0), (3/2,0)} (the +1/2-shifted model convention of
    the committed cc20TripleFiniteVanishingSet {0, 1/2, 1}); rho pair, +/-1
    detection targets and on-line-zero nodes are all absent.  The base bump
    is chi(x/eps); with the NEXP-fold star convolution the realized support
    radius is at most (NEXP + 1) * eps.  Moment rows are obtained by the
    exact change of variables u = x/eps:

        int x^m e^{-z x} chi(x/eps) dx = eps^{m+1} int u^m e^{-(z eps) u} chi(u) du,

    so the GL quadrature machinery of the committed solve is reused
    unmodified on the unscaled bump.
    """
    # Registered amendments A1-A3 (1225 sec.4, committed after smoke-1 and
    # before any official digit; smoke-1 evidence: |a|max 1.17e31, realized
    # support 27.998 = e^{x/2}-amplified torus noise, C2 gate correctly fired).
    #
    # A1: Three vanishing targets alone would admit the trivial solution, so
    # the system carries one normalization condition at a free node (not in
    # the vanishing set), making it square with Ms = 4 moments.  The rhs is
    # the RAW value in the moment partition function -- no division by
    # B(z)^NEXP as in the 1212 detector solve.  The enforced conditions are
    # lap-corr(1/2) = lap-corr(1) = lap-corr(3/2) = 0, lap-corr(2) = 1, so
    # lap h vanishes at the three nodes for the same reason as the baseline
    # (corr vanishes there and h = corr (*) base^{*NEXP}), while coefficients
    # stay O(1e6) instead of O(1e31).
    # A2: g is rescaled to peak 1 (FP and qw both scale quadratically, so the
    # adjudicated ratio FP/qw is untouched; g's scale was never registered).
    # A3: realized support is reported at relative floors 1e-4 / 1e-6 / 1e-8;
    # the gate reads the 1e-8 floor and the raw leak outside the ROOT window
    # is returned for audit.
    nodes = [0.5, 1.0, 1.5, 2.0]
    Ms = len(nodes)
    epsm = mpmath.mpf(eps)
    A = mpmath.zeros(Ms, Ms)
    for i, z in enumerate(nodes):
        row = moment_row_mp(complex(z) * eps, Ms)
        for m in range(Ms):
            A[i, m] = row[m] * epsm ** (m + 1)
    rhs = mpmath.matrix([mpmath.mpc(0), mpmath.mpc(0), mpmath.mpc(0),
                         mpmath.mpc(1)])
    sol = mpmath.lu_solve(A, rhs)
    res = float(mpmath.norm(A * sol - rhs) / max(mpmath.norm(rhs), 1))
    a = np.array([complex(sol[m]) for m in range(Ms)])
    base = chi(QS / eps)
    corr = np.zeros(NQ, dtype=complex)
    xp = np.ones_like(QS)
    for am in a:
        corr += am * xp * base
        xp = xp * QS
    h = corr
    for _ in range(NEXP):
        h = circular_conv_centered(h, base)
    g = h * np.exp(QS / 2)
    peak = float(np.abs(g).max())
    if peak > 0:
        g = g / peak  # A2
    abs_g = np.abs(g)
    r_root_model = math.log(2.0) / 2.0
    leak = float(abs_g[np.abs(QS) >= r_root_model].max()) \
        if np.any(np.abs(QS) >= r_root_model) else 0.0
    radii: dict[str, float] = {}
    for label, fl in (("1e-4", 1e-4), ("1e-6", 1e-6), ("1e-8", 1e-8)):
        idx = np.where(abs_g > fl)[0]
        radii[label] = float(np.max(np.abs(QS[idx]))) if idx.size else 0.0
    # flat float-valued meta (JSON-embeddable, no heterogeneous nesting)
    out: dict[str, float] = dict(
        residual=res, max_abs_a=float(np.abs(a).max()), eps=eps,
        support_radius=radii["1e-8"], radius_1e_4=radii["1e-4"],
        radius_1e_6=radii["1e-6"], radius_1e_8=radii["1e-8"],
        far_leak=leak, peak_before_rescale=peak)
    return g, out


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
    """Top-rank eigenpairs of the PSD sandwich operator W.  A4b: k is
    clamped to N-16 and maxiter scales with the requested rank."""
    N = cn.grid.N
    k = min(rank, N // 2)   # A4b: ARPACK space 2k+1 <= N stays feasible

    def mv(v):
        return cn.Wmv(v.reshape(N, -1)).ravel()
    op = LinearOperator((N, N), mv, dtype=complex)
    vals, vecs = eigsh(op, k=k, which="LA", tol=TRACE_TOL,
                       maxiter=max(5000, 4 * k))
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


RANK_REPLAY = 320   # A7: committed 1212 protocol rank for the C4 fidelity
# replay only; the control ladder keeps PROBE_RANK per A4b.


def rung(n, N, sample, f0_cont, pad=None, rank=None):
    Rn = R0 + n + 1
    grid = Grid(Rn + (PAD if pad is None else pad), N)
    gt = sample(grid.t)
    f0d = float((np.abs(gt) ** 2).sum())
    win = np.abs(grid.t) <= Rn
    cn = Cn(grid, gt, win)
    Nw = int(win.sum())
    bulk = Nw * f0d                      # exact discrete tr(W), closed form
    vals, vecs = bulk_eig(cn, RANK if rank is None else rank)
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
    vals, vecs = bulk_eig(cn, DV_RANK)   # A4b: validation grid has its own rank
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
    # A4 (registered): smoke mode no longer downscales RANK or DENSE_N --
    # the narrow-band control needs the official spectral rank to pass the
    # S0.5 fidelity check; smoke still shortens the ladder and dt-pair.
    ns = [4] if smoke else NS
    pairs = [(1024, 2048)] if smoke else [(N_COARSE, N_FINE)]
    t0 = time.time()
    mode = "SMOKE" if smoke else "OFFICIAL"
    print(f"== 1225 positive-control probe ({mode}, MODEL, law 65) =="
          f" eps={CONTROL_EPS}")
    g, meta = build_g_control(CONTROL_EPS)
    print(f"S0.1 correction residual {meta['residual']:.2e} "
          f"|a|max {meta['max_abs_a']:.2e}")
    # C2 gate (amended A3): realized support strictly inside the ROOT window,
    # read at the 1e-8 relative floor after the A2 peak-1 rescale; the three
    # floors and the raw far-window leak are printed for audit.
    # C2 gate (amended A3, 1225 sec.4): realized support strictly inside the
    # ROOT window, read at the 1e-8 relative floor after the A2 peak-1
    # rescale; all three floors and the raw far-window leak are printed.
    r_root = math.log(2.0) / 2.0
    support_radius = float(meta["support_radius"])
    print("C2 support radii " + " ".join(
        f"[{lbl}]={float(meta[k]):.6f}"
        for lbl, k in (("1e-4", "radius_1e_4"), ("1e-6", "radius_1e_6"),
                       ("1e-8", "radius_1e_8"))))
    print(f"C2 far leak max|g| outside [{-r_root:.4f},{r_root:.4f}] = "
          f"{float(meta['far_leak']):.2e} (pre-rescale peak "
          f"{float(meta['peak_before_rescale']):.2e})")
    print(f"C2 realized support radius {support_radius:.6f} "
          f"(bound {r_root:.6f}, margin {r_root - support_radius:+.4f})")
    assert 0.0 < support_radius < r_root, \
        "C2 FAILED: control support is not strictly ROOT-window"
    qwv = qw_terms(g)
    print(f"S0.1 f0={qwv['f0']:.6e} arch={qwv['arch']:+.6e} "
          f"prime={qwv['prime']:+.6e} pole={qwv['pole']:+.6e} "
          f"qw={qwv['qw']:+.6e}")
    # C3 gate (amended, 1225 sec.4): significance guard, not a 1e-9 identity.
    # The closed form qw = -arch additionally needs the SQUARE's pole residue
    # to vanish, which the lap-corr node set does not pin (the committed
    # baseline carries pole/arch = 8.7e-5); dev3 must only show the ROOT
    # prime-free regime is realized at all.  Comparison target is unchanged:
    # the 1213 statistic qw_model = pole - arch - prime.
    dev3 = abs(qwv["pole"] - qwv["prime"]) / max(abs(qwv["arch"]), 1e-300)
    print(f"C3 deviation |pole - prime|/|arch| = {dev3:.2e} (gate 1e-3)")
    assert dev3 < 1e-3, "C3 FAILED: ROOT prime-free regime not realized"
    # C5 pre-gate: the run is informative only for qw strictly positive.
    if qwv["qw"] <= 0.0:
        print("C5 pre-gate: control qw <= 0 -> NOT-INFORMATIVE; "
              "ABORTED-UNINFORMATIVE (registered branch, sec.4 C5)")
        raise SystemExit(3)
    print(f"C5 pre-gate PASS: control qw > 0 ({qwv['qw']:.6e}); "
          "a MATCH outcome is sign-possible")
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
    # A5 (1225 sec.4): wrap contamination is an O(bulk) mass event, so the
    # drift is measured against BULK, not against the control's tiny Tn.
    wrap_rel = abs(ratio24 - ratio40) / max(abs(ratio24), 1e-300)
    abs_drift_bulk = abs(r24["Tn"] - r40["Tn"]) / r24["bulk"]
    # A5 cross-check on Tn ONLY: sn_dt mixes the bulk dt^2 discretization
    # drift (~1e-2), which is not a wrap statistic (disclosed at smoke-5).
    drift_sn_dt = abs(r24["Tn"] - r40["Tn"]) * dt24
    print(f"S0.6 wrap gate n=8 fixed-dt: N {Nw_gate}->{N40}, "
          f"dt {dt24:.6f}->{r40['dt']:.6f}  "
          f"Tn/bulk(24)={ratio24:+.9f}  Tn/bulk(40)={ratio40:+.9f}  "
          f"rel(Tn) drift {wrap_rel:.2e}  abs drift/bulk {abs_drift_bulk:.2e}")
    # A5 tolerance 1e-3 of bulk: a genuine seam wrap moves O(content mass)
    # ~ O(bulk) of Tn; the observed smooth P_V period-dependence is 3.7e-6
    # of bulk.  Cross-check: drift in sn_dt units vs the FP scale (1% band).
    assert abs_drift_bulk < 1e-3, "S0.6 wrap contamination FAILED (A5)"
    # A5(b)/A6 disclosure: drift in PHYSICAL cont units (Tn*dt^2, the
    # adjudicated statistic); printed for audit, band check anchored at the
    # ladder grade as A5b below.
    drift_cont = abs(r24["Tn"] - r40["Tn"]) * dt24 ** 2
    print(f"S0.6 disclosure: drift in cont units (Tn*dt^2) = {drift_cont:.3e} "
          f"(band re-anchored at ladder grade, A5b)")
    del r24, r40
    wrap_gate = dict(n=8, N24=Nw_gate, N40=N40, dt24=dt24,
                     ratio24=ratio24, ratio40=ratio40, rel_drift=wrap_rel,
                     abs_drift_bulk=abs_drift_bulk, drift_sn_dt=drift_sn_dt)
    # C4 replay gate (registered sec.4): the committed baseline detector
    # twin must reproduce FP_inf = +1.3791e33 (1213) within 2e-4 at the
    # SAME rank in the same invocation, so any rank escalation under A4 is
    # shown to leave the committed convention untouched.  Official mode
    # only (the committed number is the n=64/fine grade).
    replay = None
    if not smoke:
        g_det, _ = build_g_delta0()
        sdet = sample_fn(g_det)
        qwv_det = qw_terms(g_det)
        # A7: the replay is a protocol-FIDELITY check, so it runs at the
        # COMMITTED rank 320, not the control's A4b rank.  Invocation 1
        # measured the alternative: 2.68e-3 at rank 2560 (Ritz-residual
        # accumulation is linear in k at ||W|| ~ 1e37; the 8x prediction
        # from the committed rank-320 residual 3.3e-4 matches).
        r_det = rung(64, N_FINE, sdet, qwv_det["f0"], rank=RANK_REPLAY)
        # A6/A7b: physical readout FP = Tn * dt^2; the replay constant is
        # the RAW committed n=64/fine rung value 1.382789e33 from
        # 1212_probe_results.json (preflight: fork reproduces it to 8
        # significant digits), NOT the 1213 Q2 slope-removed ladder figure
        # 1.379171e33 (that quantity removes the fitted window slope and
        # does not appear as any raw field).
        fp_det = r_det["Tn"] * r_det["dt"] ** 2
        rel_replay = abs(fp_det / 1.382789e33 - 1.0)
        print(f"C4 replay (detector twin, RANK={RANK_REPLAY}): "
              f"FP {fp_det:.8e} vs committed raw 1.382789e33  "
              f"rel {rel_replay:.2e}  (tail_gap {r_det['tail_gap']:.2e})")
        assert rel_replay <= 1e-6, \
            "C4 FAILED: rig does not reproduce the committed raw FP"
        replay = dict(fp=fp_det, rel=rel_replay, rank=RANK_REPLAY,
                      tail_gap=r_det["tail_gap"], qw=qwv_det["qw"])
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
                # A4b(iv): every OFFICIAL rung must certify spectral capture
                # (smoke rungs print only - below the knee by construction);
                # failure is ABORTED-UNINFORMATIVE (rig finding).
                if not smoke:
                    assert row["tail_gap"] < 1e-10, \
                        f"A4b FAILED: tail_gap {row['tail_gap']:.2e} " \
                        f"at n={n}, N={N}"
                results.append(row)
                print(f"n={n:3d} {c:6d} N={N:5d} bulk={row['bulk']:.6e} "
                      f"gap={row['tail_gap']:.1e} "
                      f"term1/b={row['term1']/row['bulk']:.6f} "
                      f"pv/b={row['term_pv']/row['bulk']:.6f} "
                      f"Tn/b={row['Tn']/row['bulk']:+.6f} "
                      f"cont={row['Tn']*row['dt']**2:+.6e} "
                      f"sn_dt={row['sn_dt']:+.6e} "
                      f"pv_rank={row['pv_rank']}/{row['pv_neg_dim']} "
                      f"[{secs}s]")
            if smoke:
                out = "1225_control_smoke.json"
            else:
                # 1225 sec.4: NEW files only; the committed 1212 JSON is
                # never written by this script.
                out = os.environ.get("PROBE_OUT", "1225_control_results.json")
            with open(os.path.join(HERE, out), "w") as fh:
                json.dump(dict(record="1225", mode=mode, model=True,
                               control_eps=CONTROL_EPS, control=meta,
                               lambda_=LAMBDA, S=S_PRIMES, qw=qwv,
                               c3_deviation=dev3, rank=RANK, replay=replay,
                               dense_validation=dv, wrap_gate=wrap_gate,
                               results=results),
                          fh, indent=1)
    if not smoke:
        # A5b/A6: materiality of the dt machinery at the adjudication
        # grade, in PHYSICAL cont units (FP = Tn * dt^2).
        sc = [r for r in results if r["n"] == 64 and r["N"] == N_COARSE][0]
        fp64r = [r for r in results if r["n"] == 64 and r["N"] == N_FINE][0]
        sc = sc["Tn"] * sc["dt"] ** 2
        fp64 = fp64r["Tn"] * fp64r["dt"] ** 2
        dt_pair_spread = abs(sc - fp64)
        print(f"A5b dt-pair spread at n=64: coarse {sc:+.6e} fine {fp64:+.6e} "
              f"spread {dt_pair_spread:.3e} (gate 1% of |qw| = "
              f"{0.01 * abs(qwv['qw']):.3e})")
        assert dt_pair_spread < 0.01 * abs(qwv["qw"]), \
            "A5b FAILED: dt-pair spread not resolvable against the band"
        ratio = fp64 / qwv["qw"]
        print(f"\nqw target {qwv['qw']:+.6e}; FP(sn_dt, n=64, fine) "
              f"{fp64:+.6e}; FP/qw = {ratio:+.6f}")
        print("VERDICT-MARKER: " + ("MATCH" if abs(ratio - 1.0) <= 0.01
                                    else "MISMATCH") +
              "  (registered sec.4 C5, band |ratio-1| <= 0.01; adjudication "
              "and noise band in the record, this line is an aid only)")
    print(f"total {time.time() - t0:.0f}s  (MODEL; certifies nothing; "
          "RH NOT claimed)")


if __name__ == "__main__":  # importable guard added for the 1225 rank diagnostic
    main()
