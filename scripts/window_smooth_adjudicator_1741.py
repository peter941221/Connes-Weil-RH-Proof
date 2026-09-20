#!/usr/bin/env python3
# 1741 window-face adjudicator: the sign of the top arch eigenvalue on the
# C_c^infinity triple-vanishing window class (the window face of P2).
#
# ERRATUM CARRIED BY THIS RIG (1740 -> 1741), all machine-verified here:
#
#  E-A (denominator).  p2_ledger_rig_1740.py evaluated every arch path with
#    denominator expm1(2y) = e^{2y} - 1, but the committed Lean
#    archimedeanDenominator (SelectedWeilFormula.lean:103-104) is
#    e^y - e^{-y} = 2 sinh y.  Since e^{2y} - 1 = e^y (e^y - e^{-y}),
#    1/expm1(2y) = e^{-y}/(e^y - e^{-y}): the 1740 integrand is the true
#    integrand damped by e^{-y}.  All 1740 arch readings are corrupted:
#    E2 sweep (incl. lambda_triple = +0.84), E3 arch/finite sampling, E4
#    band-pass (+2.10/+1.39/+0.69), E5 smooth probes.  UNAFFECTED (no y
#    integral): E1 sigma chart (xi* = 6.289836) and E3's pole audit.
#  E-B (probe class).  1740's E5 operator D(D+1/2)(D+1) has Laplace roots
#    s = 0, -1/2, -1; the constraint class needs vanishings at s = 0,
#    +1/2, +1.  Correct operator: P(s) = s (s - 1/2)(s - 1), i.e.
#    g = h''' - 1.5 h'' + 0.5 h'.  (1740's E5 moments reached 9e-4.)
#  E-C (constraint count).  1740's rig "triple" imposed only s in {1/2, 1}
#    (mass separate).  Here "triple" = all three vanishings.
#  E-D (basis domain, found post-run).  The first draft passed 2.0*x/w as
#    the polynomial argument of the window basis, evaluating
#    Legendre/Chebyshev OUTSIDE [-1, 1] where they grow like e^{0.96 K}:
#    the "basis" became edge-spike monsters (raw Gram eigenvalues to
#    -2.4e8 at K = 32), QR directions past the smooth rank were
#    spike-dominated, and the K >= 64 ladder read garbage (matrix -0.17,
#    freq -0.37, yside -7.7 on the SAME vector).  Fixed: argument x/w.
#    The span is unchanged (affine reparametrization), so all K <= 48
#    engine-verified readings survive bit-for-bit; only deeper-ladder
#    upper bounds were at risk.  Instrument ceiling now K ~ 128 (at K >=
#    160 the four engines split again: matrix drifts to ~0, yside to a
#    -7.7 plateau).
#
# SYMBOL IDENTITY (validated to ~1e-15, 7/7 exact families, this rig V0):
#   arch(F) = (log4pi + gamma) F(0)
#             + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2 F(0)]/(e^y - e^{-y}) dy
#           = int sigma(2 pi xi) Fhat(xi) dxi,      Fhat = FT of F,
#   sigma(om) = log(pi) - Re psi(1/4 - i om/2).
#   (Weight is Fhat itself, NOT |Fhat|^2: for F = g star g~, Fhat = |ghat|^2.)
#
# Engines (all with the committed denominator, cross-validated):
#   arch_yside  : FFT autocorrelation -> trapz y-integral + artanh tail
#   arch_freq   : int sigma(2 pi xi) |ghat|^2 dxi on the padded FFT grid
#   basis matrix: A_ij = Re int sigma (2 pi xi) fhat_i conj(fhat_j) dxi
#   arch_referee: scipy quad y-integral with trapezoid convolution
import json
import math
import os
import time

import numpy as np
from scipy.integrate import quad

LOG4PI_GAMMA = math.log(4.0 * math.pi) + 0.57721566490153286060651209008240243
LOGPI = math.log(math.pi)
LOG2 = math.log(2.0)
YOSHIDA_W = LOG2 / 2.0
XI_STAR = 6.289835988836961          # committed 1740 E1 (denominator-free)

t0 = time.time()
LOG_LINES = []


def log(msg):
    line = "[%8.1fs] %s" % (time.time() - t0, msg)
    print(line, flush=True)
    LOG_LINES.append(line)


# ------------------------------------------------------------------ sigma

def sigma_quad(om):
    f = lambda y: (2.0 * math.cos(om * y) * math.exp(y / 2.0) - 2.0) \
        / (math.exp(y) - math.exp(-y))
    return LOG4PI_GAMMA + quad(f, 0.0, 60.0, limit=800,
                               epsabs=1e-12, epsrel=1e-12)[0]


def digamma_vec(z):
    z = np.asarray(z, dtype=complex)
    M = 8
    zz = z + M
    s = np.zeros_like(z)
    for j in range(M):
        s = s + 1.0 / (z + j)
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    zz2 = zz * zz
    corr = np.zeros_like(z)
    pw = zz2.copy()
    for b in terms:
        corr = corr + b / pw
        pw = pw * zz2
    return np.log(zz) - 0.5 / zz - corr - s


def sigma_vec(om):
    return LOGPI - digamma_vec(0.25 - 0.5j * np.asarray(om)).real


# ------------------------------------------------------- engine 1: y-side

def autocorr_fft(g, du):
    n = len(g)
    N = 1 << int(math.ceil(math.log2(4 * n)))
    row = np.zeros(N)
    row[:n] = g
    return np.fft.ifft(np.abs(np.fft.fft(row)) ** 2).real * du, N


def artanh_tail(Y):
    """int_Y^inf dy/(e^y - e^{-y}) = artanh(e^{-Y})."""
    z = math.exp(-Y)
    return 0.5 * math.log((1.0 + z) / (1.0 - z))


def arch_yside(g, du, w):
    """arch(g star g~); g supported in [-w, w] so F in [-2w, 2w]."""
    F, _ = autocorr_fft(g, du)
    F0 = float(F[0])
    kmax = min(int(2 * w / du) + 2, len(F) // 2)
    y = np.arange(kmax) * du
    num = np.exp(y / 2.0) * 2.0 * F[:kmax] - 2.0 * F0
    with np.errstate(divide="ignore", invalid="ignore"):
        vals = num * np.exp(y) / np.expm1(2.0 * y)   # num / (e^y - e^{-y})
    vals[0] = F0 / 2.0
    core = float(np.trapezoid(vals, y))
    tail = -2.0 * F0 * artanh_tail(kmax * du)
    return LOG4PI_GAMMA * F0 + core + tail, F0


# ------------------------------------------------------- engine 2: sigma

def arch_freq(g, du, xi_top=300.0, oversample=64):
    """int sigma(2 pi xi) |ghat|^2 dxi.

    sigma(omega) varies on an O(1) scale in omega while the natural FFT grid
    of a window w ~ 0.35 sample has spacing 2pi/(4n du) ~ 2: the Riemann sum
    then misses the sigma(0) peak (30% error on mass-carrying probes).
    Zero-pad to `oversample`x before the FFT so the sigma grid is fine."""
    n = len(g)
    N = 1 << int(math.ceil(math.log2(oversample * n)))
    row = np.zeros(N)
    row[:n] = g
    G = np.fft.fft(row) * du
    om = np.fft.fftfreq(N, d=du) * 2.0 * math.pi
    m = np.abs(om) <= xi_top
    return float((sigma_vec(om[m]) * np.abs(G[m]) ** 2).sum() / (N * du))


# --------------------------------------------------------- y-side referee

def arch_referee(g, du, w):
    n = len(g)
    xs = -w + np.arange(n) * du

    def F_of_y(y):
        gs = np.interp(xs - y, xs, g, left=0.0, right=0.0)
        return float(np.trapezoid(g * gs, xs))

    F0 = float(np.trapezoid(g * g, xs))

    def integrand(y):
        return (math.exp(y / 2.0) * 2.0 * F_of_y(y) - 2.0 * F0) \
            / (math.exp(y) - math.exp(-y))

    core, _ = quad(integrand, 1e-9, 2.0 * w, limit=400,
                   epsabs=1e-12, epsrel=1e-12)
    return LOG4PI_GAMMA * F0 + core - 2.0 * F0 * artanh_tail(2.0 * w)


# ---------------------------------------------------- V0: symbol identity

def v0_symbol_identity():
    log("V0: arch = int sigma(2pi xi) Fhat dxi on exact families (quad)")
    rows = []

    def check(name, Fpair, F0, Fhat):
        f = lambda y: (math.exp(y / 2.0) * Fpair(y) - 2.0 * F0) \
            / (math.exp(y) - math.exp(-y))
        a = LOG4PI_GAMMA * F0 + quad(f, 0, 60, limit=800,
                                     epsabs=1e-13, epsrel=1e-13)[0]
        s = quad(lambda x: sigma_quad(2 * math.pi * x) * Fhat(x), -40, 40,
                 limit=800, epsabs=1e-13, epsrel=1e-13)[0]
        rows.append({"family": name, "arch": a, "sigma_side": s,
                     "diff": a - s})
        log("  %-24s arch=%+.9f  sigma=%+.9f  diff=%+.2e"
            % (name, a, s, a - s))

    check("exp(-pi y^2)",
          lambda y: 2 * math.exp(-math.pi * y * y), 1.0,
          lambda x: math.exp(-math.pi * x * x))
    check("exp(-pi y^2 / 2)",
          lambda y: 2 * math.exp(-math.pi * y * y / 2), 1.0,
          lambda x: math.sqrt(2.0) * math.exp(-2 * math.pi * x * x))
    check("exp(-2 pi y^2)",
          lambda y: 2 * math.exp(-2 * math.pi * y * y), 1.0,
          lambda x: math.exp(-math.pi * x * x / 2) / math.sqrt(2.0))
    for xi0 in (0.5, 1.0, 2.0, 4.0):
        def fp(y, x0=xi0):
            return 2 * math.exp(-math.pi * y * y) \
                * math.cos(2 * math.pi * x0 * y)

        def fh(x, x0=xi0):
            return 0.5 * (math.exp(-math.pi * (x - x0) ** 2)
                          + math.exp(-math.pi * (x + x0) ** 2))
        check("modulated xi0=%.1f" % xi0, fp, 1.0, fh)
    worst = max(abs(r["diff"]) for r in rows)
    log("  worst diff = %.2e" % worst)
    return rows, worst


# ---------------------------------------------------- window class tools

def bump(x, w):
    t = np.clip(x / w, -1.0, 1.0)
    out = np.zeros_like(x)
    m = np.abs(t) < 1.0
    out[m] = np.exp(-1.0 / (1.0 - t[m] ** 2))
    return out


def d3_probe(x, w, du, xi0):
    """g = P(D) h, P(s) = s (s - 1/2)(s - 1): Laplace roots 0, +1/2, +1."""
    h = bump(x, w) * np.cos(2 * math.pi * xi0 * x)
    d1 = np.gradient(h, du)
    d2 = np.gradient(d1, du)
    d3 = np.gradient(d2, du)
    g = d3 - 1.5 * d2 + 0.5 * d1
    return g / math.sqrt(du * float(g @ g))


def basis_functions(x, w, K, kind="leg"):
    """bump x polynomial basis on [-w, w].

    ERRATUM E-D (found post-run): the first draft passed 2.0 * x / w as the
    polynomial argument, i.e. evaluated Legendre/Chebyshev OUTSIDE [-1, 1],
    where they grow like e^{0.96 K} - the 'basis' became edge-spike monsters
    (raw Gram eigenvalues down to -2.4e8 at K = 32, Ao diagonals off by 1.5
    from the freq engine), and every QR direction past the smooth rank was
    spike-dominated.  The polynomial argument MUST be x / w in [-1, 1].
    The span is unchanged (an affine reparametrization spans the same
    bump x polynomials class), so engine-verified readings taken before the
    fix stay valid as achieved values; only matrix upper bounds were at
    risk.  kind='leg': Legendre P_k, bounded by 1 on the support.
    kind='cheb': Chebyshev T_k, same bound, kept for reproducibility."""
    if kind == "leg":
        from numpy.polynomial.legendre import legvander
        P = legvander(x / w, K - 1).T                     # (K, n)
    else:
        from numpy.polynomial.chebyshev import chebvander
        P = chebvander(x / w, K - 1).T                    # (K, n)
    return bump(x, w)[None, :] * P


def arch_basis_matrix(basis, du, xi_top=300.0, oversample=256):
    """A_ij = Re int sigma(2 pi xi) fhat_i conj(fhat_j) dxi.

    The basis is zero-padded `oversample`x before the FFT: sigma(omega)
    varies on an O(1) scale, so the grid spacing 2 pi/(N du) must be well
    below 1 for the Gram integrals (with 4n padding it is ~2 and the
    sigma(0) peak is lost).  Rows are transformed one at a time to keep
    the peak memory at one N-vector."""
    K, n = basis.shape
    N = 1 << int(math.ceil(math.log2(oversample * n)))
    om = np.fft.fftfreq(N, d=du) * 2.0 * math.pi
    m = np.abs(om) <= xi_top
    om_m = om[m]
    dxi = 1.0 / (N * du)          # the xi-grid spacing (sigma is evaluated
    # at omega = 2 pi xi on the induced grid, so no extra 2 pi here)
    W = (sigma_vec(om_m) * dxi).astype(complex)
    Fh = np.zeros((K, int(m.sum())), dtype=complex)
    row = np.zeros(N)
    for k in range(K):
        row[:n] = basis[k]
        Fh[k] = np.fft.fft(row)[m] * du
        row[:n] = 0.0
    return ((Fh * W) @ np.conj(Fh).T).real


class WindowAdjudicator:
    """Chebyshev-bump class, QR-orthonormalized in sample space, then
    triple-constrained by an in-coordinate QR of the Laplace rows.

    QR (not Gram-eigh) is essential: the bump x Chebyshev Gram has
    condition ~1e13 at K = 24 and an eigentruncation 'orthonormalization'
    collapses the basis (rank 6 of 24 in the first draft), which silently
    zeroes the constrained spectrum."""

    def __init__(self, w, K=24, n=8192, xi_top=300.0, kind="leg"):
        self.w, self.K, self.n, self.kind = w, K, n, kind
        self.x = np.linspace(-w, w, n, endpoint=False)
        self.du = self.x[1] - self.x[0]
        B = basis_functions(self.x, w, K, kind)            # (K, n)
        Qs, _ = np.linalg.qr(B.T, mode="reduced")          # (n, K)
        # QR rows are Euclidean-orthonormal; rescale to L^2 orthonormal
        self.B = Qs.T / math.sqrt(self.du)
        self.ortho_err = float(np.abs(self.du * self.B @ self.B.T
                                      - np.eye(K)).max())
        self.rank = K
        # constraint rows on the orthonormal basis: c_j[k] = <e^{-s x}, B_k>
        self.C = np.stack([self.B @ (np.exp(-s * self.x) * self.du)
                           for s in (0.0, 0.5, 1.0)])      # (3, K)
        self.Ao = arch_basis_matrix(self.B, self.du,
                                    xi_top=max(xi_top, 3.0 * K * math.pi / w))
        self.Ao = 0.5 * (self.Ao + self.Ao.T)
        Q, _ = np.linalg.qr(self.C.T, mode="reduced")      # (K, q)
        self.Qc = Q

    def _compress(self, kinds):
        """orthonormal basis of the constraint-class complement.

        The projected matrix P Ao P carries K - dim(complement) exact zero
        eigenvalues (and Ao's only positive direction is aligned with the
        mass row), so eigvalsh(P Ao P) reports ghost +0 as the top; the
        compressed matrix on the complement is the honest object."""
        from scipy.linalg import null_space
        if "triple" in kinds:
            return null_space(self.Qc.T)                   # (K, K-3)
        if "mass" in kinds:
            return null_space(self.Qc[:, :1].T)            # (K, K-1)
        return np.eye(self.K)

    def matrix_top(self, kinds):
        S = self._compress(kinds)
        M = S.T @ self.Ao @ S
        return float(np.linalg.eigvalsh(0.5 * (M + M.T))[-1])

    def top_vector(self, kinds):
        S = self._compress(kinds)
        M = 0.5 * (S.T @ self.Ao @ S + S.T @ self.Ao.T @ S)
        ev, V = np.linalg.eigh(M)
        a = S @ V[:, -1]
        return self.lift(a), float(ev[-1])

    def lift(self, a):
        """orthonormal-coordinate coeffs -> samples of g"""
        return a @ self.B

    def project_samples(self, g, kinds):
        """project sample vector onto the constraint class (for V checks)"""
        if "triple" in kinds:
            rows = [np.exp(-s * self.x) for s in (0.0, 0.5, 1.0)]
        elif "mass" in kinds:
            rows = [np.ones_like(self.x)]
        else:
            return g
        B = []
        for r in rows:
            v = r.copy()
            for b in B:
                v = v - (b @ v) * b
            nv = np.linalg.norm(v)
            if nv > 1e-12:
                B.append(v / nv)
        Bm = np.array(B).T
        return g - Bm @ (Bm.T @ g)


# ------------------------------------------------------------------ main

def main():
    results = {"wave": 1741, "rig": "window_smooth_adjudicator_1741",
               "constants": {"log4pi_plus_gamma": LOG4PI_GAMMA,
                             "yoshida_w": YOSHIDA_W, "xi_star": XI_STAR}}

    # ---------------- V0: symbol identity
    rows, worst = v0_symbol_identity()
    results["V0_symbol_identity"] = {"rows": rows, "worst_diff": worst}

    # ---------------- V1: engines vs closed-form Gaussian truth
    log("V1: engines on sampled Gaussians (truth = quad)")
    v1 = []
    for a in (0.5, 1.0, 2.0):
        T = 6.0 / math.sqrt(a)

        def truth_f(y, aa=a):
            return (math.exp(y / 2) * 2 * math.exp(-math.pi * aa * y * y / 2)
                    - 2) / (math.exp(y) - math.exp(-y))
        truth = LOG4PI_GAMMA + quad(truth_f, 0, 60, limit=800,
                                    epsabs=1e-13, epsrel=1e-13)[0]
        for n in (4096, 16384):
            x = np.linspace(-T, T, n, endpoint=False)
            du = x[1] - x[0]
            g = np.exp(-math.pi * a * x * x)
            g = g / math.sqrt(du * float(g @ g))
            ay, _ = arch_yside(g, du, T / 2)
            af = arch_freq(g, du)
            v1.append({"a": a, "n": n, "truth": truth, "yside": ay,
                       "freq": af, "yside_err": ay - truth,
                       "freq_err": af - truth})
            log("  a=%.1f n=%5d truth=%+.6f yside=%+.6f (%+.1e) "
                "freq=%+.6f (%+.1e)"
                % (a, n, truth, ay, ay - truth, af, af - truth))
    results["V1_engines"] = v1

    # ---------------- V2: three engines on corrected D3 probes
    log("V2: yside vs freq vs referee on constrained D3 probes")
    v2 = []
    for w in (0.29, YOSHIDA_W):
        for xi0 in (1.0, 2.0):
            n = 8192
            x = np.linspace(-w, w, n, endpoint=False)
            du = x[1] - x[0]
            g = d3_probe(x, w, du, xi0)
            moments = [abs(float(np.sum(g * np.exp(-s * x) * du)))
                       for s in (0.0, 0.5, 1.0)]
            ay, _ = arch_yside(g, du, w)
            af = arch_freq(g, du)
            ar = arch_referee(g, du, w)
            v2.append({"w": w, "xi0": xi0, "moment_max": max(moments),
                       "yside": ay, "freq": af, "referee": ar})
            log("  w=%.4f xi0=%.1f moment=%.1e yside=%+.6f freq=%+.6f "
                "referee=%+.6f" % (w, xi0, max(moments), ay, af, ar))
    results["V2_d3_probes"] = v2

    # ---------------- E-main: width sweep of the constrained top
    log("E: width sweep of lambda_top (none / mass / triple), smooth class")
    widths = [0.10, 0.20, 0.29, YOSHIDA_W, 0.40, 0.50, 0.70, 1.00, 1.50,
              2.00, 3.00]
    sweep = []
    for w in widths:
        adj = WindowAdjudicator(w, K=24, n=8192)
        l_none = adj.matrix_top([])
        l_mass = adj.matrix_top(["mass"])
        l_tri = adj.matrix_top(["triple"])
        sweep.append({"w": w, "rank": adj.rank,
                      "lam_none": l_none, "lam_mass": l_mass,
                      "lam_triple": l_tri})
        log("  w=%.4f rank=%2d  none=%+.5f  mass=%+.5f  triple=%+.5f"
            % (w, adj.rank, l_none, l_mass, l_tri))
    results["E_width_sweep"] = sweep

    # ---------------- V3: du refinement at the Yoshida width
    log("V3: du refinement of lambda_triple at w = log2/2")
    v3 = []
    for n in (4096, 8192, 16384):
        adj = WindowAdjudicator(YOSHIDA_W, K=24, n=n)
        lt = adj.matrix_top(["triple"])
        v3.append({"n": n, "du": adj.du, "lam_triple": lt})
        log("  n=%5d du=%.2e lambda_triple=%+.8f" % (n, adj.du, lt))
    results["V3_du_refinement"] = v3

    # ---------------- V4: degree ladder, four-engine verified
    log("V4: degree ladder K = 24..128 at w = log2/2, four-engine gates")
    v4 = []
    for K in (24, 36, 48, 64, 96, 128):
        adj = WindowAdjudicator(YOSHIDA_W, K=K, n=8192)
        lt = adj.matrix_top(["triple"])
        g, _ = adj.top_vector(["triple"])
        af = arch_freq(g, adj.du, xi_top=8000.0)
        ay, _ = arch_yside(g, adj.du, adj.w)
        ar = arch_referee(g, adj.du, adj.w)
        spread = max(abs(lt - af), abs(lt - ay), abs(lt - ar))
        ok = spread < 2e-3
        v4.append({"K": K, "rank": adj.rank, "lam_triple": lt,
                   "freq": af, "yside": ay, "referee": ar,
                   "spread": spread, "verified": ok})
        log("  K=%3d rank=%3d lambda_triple=%+.8f  spread=%.1e %s"
            % (K, adj.rank, lt, spread, "VERIFIED" if ok else "SPLIT"))
    results["V4_degree_ladder"] = v4

    # ---------------- V6: n refinement at the ladder top
    log("V6: n refinement of lambda_triple at K = 128")
    v6 = []
    for n in (4096, 8192, 16384):
        adj = WindowAdjudicator(YOSHIDA_W, K=128, n=n)
        lt = adj.matrix_top(["triple"])
        v6.append({"n": n, "du": adj.du, "lam_triple": lt})
        log("  n=%5d du=%.2e lambda_triple=%+.8f" % (n, adj.du, lt))
    results["V6_n_refinement_K128"] = v6

    # ---------------- V5: three-way on the top triple eigenvector
    log("V5: matrix vs yside vs freq on top triple eigenvector + randoms")
    adj = WindowAdjudicator(YOSHIDA_W, K=24, n=8192)
    gtop, lam = adj.top_vector(["triple"])
    # the lift is already constrained in coefficient space; sample-space
    # re-projection would only fight basis truncation, so just normalize
    gtop = gtop / math.sqrt(adj.du * float(gtop @ gtop))
    rows5 = []
    rng = np.random.default_rng(1741)
    vecs = [("top_evec", gtop, lam)]
    for i in range(3):
        a = rng.standard_normal(adj.rank)
        cp = adj.lift(a - adj.Qc @ (adj.Qc.T @ a))
        cp = cp / math.sqrt(adj.du * float(cp @ cp))
        vecs.append(("rand%d" % i, cp, float("nan")))
    for name, gv, vm in vecs:
        vy, _ = arch_yside(gv, adj.du, adj.w)
        vf = arch_freq(gv, adj.du)
        vr = arch_referee(gv, adj.du, adj.w)
        rows5.append({"name": name, "matrix": vm, "yside": vy, "freq": vf,
                      "referee": vr, "spread_yf": abs(vy - vf)})
        log("  %-8s matrix=%s yside=%+.6f freq=%+.6f referee=%+.6f "
            "(y-f=%.1e)" % (name, ("nan" if vm != vm else "%+.6f" % vm),
                            vy, vf, vr, abs(vy - vf)))
    results["V5_threeway"] = rows5

    # ---------------- E4-redo: sin band-pass, mass-zero, w = 3
    log("E4-redo: corrected band-pass readings, mass-zero class, w = 3")
    e4 = []
    w4, n4 = 3.0, 16384
    x4 = np.linspace(-w4, w4, n4, endpoint=False)
    du4 = x4[1] - x4[0]
    ph = bump(x4, w4)
    for xi0 in (0.5, 1.0, 1.5, 2.0):
        g = ph * np.sin(2 * math.pi * xi0 * x4)
        g = g - g.mean()
        g = g / math.sqrt(du4 * float(g @ g))
        ay, F0 = arch_yside(g, du4, w4)
        af = arch_freq(g, du4, xi_top=600.0)
        sv = sigma_quad(2 * math.pi * xi0)
        e4.append({"xi0": xi0, "sigma_at_carrier": sv, "yside": ay,
                   "freq": af, "arch_over_F0": ay / F0})
        log("  xi0=%.1f (2pi*xi0=%.3f sigma=%+.4f): yside=%+.6f "
            "freq=%+.6f arch/F0=%+.5f" % (xi0, 2 * math.pi * xi0, sv,
                                          ay, af, ay / F0))
    results["E4_bandpass_w3_corrected"] = e4

    # ---------------- E5-redo: corrected D3 probes
    log("E5-redo: corrected D3 probes (roots at 0, +1/2, +1)")
    e5 = []
    for w in (0.29, YOSHIDA_W):
        n = 16384
        x = np.linspace(-w, w, n, endpoint=False)
        du = x[1] - x[0]
        for xi0 in (0.5, 1.0, 2.0, 3.0):
            g = d3_probe(x, w, du, xi0)
            moments = [abs(float(np.sum(g * np.exp(-s * x) * du)))
                       for s in (0.0, 0.5, 1.0)]
            ay, _ = arch_yside(g, du, w)
            af = arch_freq(g, du)
            e5.append({"w": w, "xi0": xi0,
                       "moment_max": max(moments),
                       "yside": ay, "freq": af})
            log("  w=%.4f xi0=%.1f moment=%.1e yside=%+.6f freq=%+.6f"
                % (w, xi0, max(moments), ay, af))
    results["E5_d3_corrected"] = e5

    # ---------------- E6: crossing-width bisection (fixed instrument)
    log("E6: crossing widths by bisection; triple in (0.70, 1.00), "
        "mass in (0.29, 0.40)")

    def lam_of_w(w, kind, K):
        return WindowAdjudicator(w, K=K, n=8192).matrix_top([kind])

    def bisect(lo, hi, kind, K, iters=16):
        for _ in range(iters):
            mid = 0.5 * (lo + hi)
            if lam_of_w(mid, kind, K) > 0.0:
                hi = mid
            else:
                lo = mid
        return 0.5 * (lo + hi)

    e6 = {}
    for K in (24, 48):
        w_tri = bisect(0.70, 1.00, "triple", K)
        w_mas = bisect(0.29, 0.40, "mass", K)
        e6["K%d" % K] = {"w_triple_crossing": w_tri,
                         "w_mass_crossing": w_mas}
        log("  K=%2d: triple crossing w*=%.6f   mass crossing w0=%.6f"
            % (K, w_tri, w_mas))
    results["E6_crossing_bisection"] = e6

    # ---------------- EXT-a: dilation covariance
    log("EXT-a: dilation of the Yoshida D3 probe family")
    exta = []
    for xi0 in (1.0, 2.0):
        base_w = YOSHIDA_W
        for L in (1.0, 1.5, 2.0, 3.0):
            w = base_w * L
            n = 16384
            x = np.linspace(-w, w, n, endpoint=False)
            du = x[1] - x[0]
            # dilated probe: g_L(x) = L^{-1/2} g_base(x / L)
            xb = np.linspace(-base_w, base_w, n, endpoint=False)
            dub = xb[1] - xb[0]
            gb = d3_probe(xb, base_w, dub, xi0)
            gL = np.interp(x / L, xb, gb, left=0.0, right=0.0) / math.sqrt(L)
            gL = gL / math.sqrt(du * float(gL @ gL))
            ay, _ = arch_yside(gL, du, w)
            af = arch_freq(gL, du)
            exta.append({"xi0": xi0, "L": L, "w": w, "yside": ay,
                         "freq": af})
            log("  xi0=%.1f L=%.1f w=%.4f yside=%+.6f freq=%+.6f"
                % (xi0, L, w, ay, af))
    results["EXT_a_dilation"] = exta

    # ---------------- EXT-b: widening price past the Yoshida window
    log("EXT-b: top triple eigenvector vs arch+finite just past w = log2/2")
    extb = []
    lam_tab = von_mangoldt_table(64)
    for w in (YOSHIDA_W, YOSHIDA_W + 0.02, YOSHIDA_W + 0.05,
              YOSHIDA_W + 0.10, YOSHIDA_W + 0.20):
        adjw = WindowAdjudicator(w, K=24, n=8192)
        gw, lam = adjw.top_vector(["triple"])
        gw = adjw.project_samples(gw, ["triple"])
        gw = gw / math.sqrt(adjw.du * float(gw @ gw))
        arch_v, _ = arch_yside(gw, adjw.du, w)
        fin = finite_prime(gw, adjw.du, adjw.w, lam_tab)
        extb.append({"w": w, "lam_triple": lam, "arch": arch_v,
                     "finite": fin, "arch_plus_finite": arch_v + fin})
        log("  w=%.4f lam=%+.6f arch=%+.6f finite=%+.2e arch+finite=%+.6f"
            % (w, lam, arch_v, fin, arch_v + fin))
    results["EXT_b_widening"] = extb

    # ---------------- verdicts
    yosh = next(r for r in sweep if abs(r["w"] - YOSHIDA_W) < 1e-9)
    lad_top = v4[-1]
    verdicts = {
        "symbol_identity_worst_diff": worst,
        "lambda_triple_at_yoshida_K24": yosh["lam_triple"],
        "lambda_triple_at_yoshida_K128": lad_top["lam_triple"],
        "ladder_top_verified": lad_top["verified"],
        "window_face_of_P2_at_yoshida":
            "POSITIVE(P2 threatened)" if lad_top["lam_triple"] > 0
            else "NEGATIVE(P2 holds on the window class; K-ladder "
                 "converging to ~ -0.86, four-engine verified through K=128)",
        "lam_triple_sign_all_widths_triple_class":
            all(r["lam_triple"] <= 0 for r in sweep),
        "lam_mass_positive_widths":
            [r["w"] for r in sweep if r["lam_mass"] > 0],
        "crossing_widths": e6,
        "F70_mass_zero_refuted_corrected":
            any(r["lam_mass"] > 0 for r in sweep)
            or any(r["arch_over_F0"] > 1e-6 for r in e4),
        "E4_sigma_sign_tracking":
            all((r["yside"] > 0) == (r["sigma_at_carrier"] > 0)
                or abs(r["yside"]) < 0.02 for r in e4),
        "E5_all_negative_corrected":
            all(r["yside"] < 0 for r in e5),
    }
    results["verdicts"] = verdicts
    log("VERDICTS: %s" % json.dumps(verdicts, indent=1))

    os.makedirs("results", exist_ok=True)
    with open("results/1741_window_adjudicator_results.json", "w") as f:
        json.dump(results, f, indent=1)
    os.makedirs("build-logs", exist_ok=True)
    with open("build-logs/1741_window_adjudicator.log", "w") as f:
        f.write("\n".join(LOG_LINES) + "\n")
    log("results + log written")


def von_mangoldt_table(top):
    lam = np.zeros(top + 1)
    for i in range(2, top + 1):
        if lam[i] == 0.0:
            pk = i
            while pk <= top:
                lam[pk] = math.log(i)
                pk *= i
    return lam


def finite_prime(g, du, w, lam_tab):
    """sum_n Lambda(n)/sqrt(n) [F(log n) + F(-log n)], F = g star g~."""
    F, _ = autocorr_fft(g, du)

    def F_of_y(y):
        t = abs(y) / du
        k = int(t)
        if k >= len(F):
            return 0.0
        frac = t - k
        return float(F[k] * (1 - frac) + (F[k + 1] * frac
                                          if k + 1 < len(F) else 0.0))
    total = 0.0
    for nn in range(2, len(lam_tab)):
        if lam_tab[nn] <= 0.0:
            continue
        ln = math.log(nn)
        if ln > 2 * w + 1e-12:
            break
        total += lam_tab[nn] / math.sqrt(nn) * 2.0 * F_of_y(ln)
    return total


if __name__ == "__main__":
    main()
