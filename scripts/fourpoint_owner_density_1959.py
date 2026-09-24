#!/usr/bin/env python3
# fourpoint_owner_density_1959.py — record 1959 (map 106, probe P0)
#
# Cut-2 gate probe on the ACTUAL selected owner instead of a bump surrogate.
# Records 1918/1919/1920 read the gate entries through W = |ĝ|² for a real,
# even, compact bump g.  The committed producer never uses a bare bump: the
# owner test is the half-density shift of a convolution power of an
# interpolating base with a finite-node correction.  This rig builds that
# object and reads the same gate entries off it.
#
# Committed definitions coded verbatim (F27/F28: source read before rig):
#
#   [1] selectedOwner base correction n
#         = ofCompactLogTest (halfDensityShift
#             ((convolutionIterate base n).convolution correction))
#       [Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean:93]
#   [2] laplaceAt (selectedOwner ...).sourceTest (z - 1/2)
#         = laplaceAt ((convolutionIterate base n).convolution correction) z
#       [ibid:117]; halfDensityShift multiplies by e^{x/2}, so
#       laplaceAt (halfDensityShift f) s = laplaceAt f (s + 1/2)   [ibid:54]
#   [3] convolutionIterate f n = n+1 copies of f
#       [Source/CC20YoshidaConvolution.lean, docstring at convolutionIterate]
#   [4] healthyUnscaledTargetNodes rho
#         = sourceFunctionalEquationOrbit rho ∪ {rho+1/2, 1/2, 1, 3/2}
#       [Dev/C1HealthyYoshidaUnscaledOrbit.lean:31] with
#       sourceFunctionalEquationOrbit rho = {rho, 1 - star rho, star rho,
#       1 - rho}                              [Source/CC20YoshidaFullProduct.lean:52]
#   [5] healthyUnscaledTargetValue rho: 1 at rho, -1 at 1 - star rho, else 0
#       on the orbit (orbit priority); -1 at rho + 1/2; 0 at 1/2, 1, 3/2
#       [Dev/C1HealthyYoshidaUnscaledOrbit.lean:39]
#   [6] base hypotheses of the all-index theorem: support in
#       Ioo baseLower baseUpper, laplaceAt base w = 1 on every target node,
#       and the strip contraction
#         forall sigma in [0,1], forall t, T <= |t| ->
#             ||laplaceAt base (sigma + i t)|| <= 1/2
#       [Dev/...:678-683] — the contraction forces T > gamma, because the
#       orbit pins sit at |Im| = gamma with value 1
#   [7] explicit finite-node correction (record 1958):
#         laplaceAt (correction nodes seed y) s
#           = sum_{z in nodes} (y z / (nodeProduct z z * laplaceAt seed 0))
#               * nodeProduct z s * laplaceAt seed (s - z)
#       [Dev/C1ExplicitFiniteNodeCorrection.lean:122]
#   [8] convolutionSquare g = g.involution.convolution g
#       [Source/CCM25Concrete/CompactLogConvolution.lean:114] with
#       F(-x) = conj (F x)                                         [ibid:123];
#       hence Fhat(xi) = |ĝ(xi)|² >= 0 is real, and for a COMPLEX g it need
#       not be even (a Hermitian F has Fhat = even real + odd real)
#   [9] gate entries in kernel form (record 1919, cross-validated there
#       against the record-1918 engines):
#         ICgate(g*g) = ∫ K·W,  ICgate(u*g) = ∫ K·P·W,
#         ICgate(u*u) = ∫ K·P²·W,
#       W(xi) = |ĝ(xi)|², K(xi) = sigma(2 pi xi)
#         + 2 sum_visible (Lambda(n)/sqrt n) cos(2 pi xi log n),
#       sigma(u) = log pi - Re psi(1/4 - i u/2), and P(xi) = prod_j
#       (s_j + 2 pi i xi) over the four CENTERED orbit nodes
#       s_j = ±delta ± i gamma (real on the axis).  The pair B01 = B10 holds
#       for any W, because P is real on the axis.
#
# STRUCTURE READ OFF THE DEFINITIONS (this probe's target):
#
#   ĝ(xi) = L_base(1/2 - 2 pi i xi)^(n+1) * L_corr(1/2 - 2 pi i xi),
#   W(xi) = |L_base(1/2 - 2 pi i xi)|^{2(n+1)} |L_corr(1/2 - 2 pi i xi)|².
#
#   (S1) the raw node 1/2 pins L_base(1/2) = 1 and L_corr(1/2) = y(1/2) = 0,
#        so W(0) = 0 exactly (a double zero), for every admissible base and
#        correction.  The bump surrogate of 1918-1920 puts its mass AT
#        xi = 0, where sigma(0) = 5.372 > 0; the owner cannot put mass there.
#   (S2) the orbit pins at Re = 1/2 ± delta, |Im| = gamma sit at distance
#        delta from the line Re = 1/2 that carries W, and the contraction
#        [6] forces the base transform to be small above height T > gamma.
#        An admissible base therefore has its transform concentrated in the
#        vertical band |Im s| <= T, giving W a two-lobe profile near
#        xi = ±gamma/(2 pi) — where sigma(2 pi xi) < 0 for |xi| > 1.0011
#        (record 1920, probe A) and P(xi) ~ 4 delta² gamma² << gamma⁴ = P(0).
#
# BASE FAMILIES (both legitimate instances of hypothesis [6]; the probe
# reports which ones are admissible and never mixes them):
#
#   mode "design" (primary): the base and the correction are finite sums
#         f(x) = sum_j A_j phi(x) e^{i theta_j x},
#         L_f(s) = sum_j A_j L_phi(s + i theta_j),
#     with phi(x) = exp(-k/(1 - (x/a)²)) on |x| < a (C-infinity, compact,
#     Gevrey order k, so its vertical decay is exp(-c sqrt(k |t|))).  The
#     amplitudes solve the 8x8 interpolation systems for the base (target
#     value 1) and the correction (target values [5]).  This is the same
#     architecture as the committed correction family: a fixed window with
#     exponential weights.
#
#   mode "cardinal" (documented limitation): base = correction(targets,
#     explicitSeed, 1) and correction = correction(targets, explicitSeed, y)
#     in the committed 1958 formulas, with the exact committed seed
#     seed_r(x) = r^{-1} smoothTransition(2 - |x|/r)  (Mathlib bump base
#     toFun R x = smoothTransition((R - |x|)/(R - 1))
#     [Mathlib/.../BumpFunction/InnerProduct.lean:33]).  This base is exact
#     at the pins (3.3e-16) but its transform has a Gevrey tail that is still
#     O(10) at height 2 pi |xi| ~ 190: the density peaks at |xi| ~ 10 and
#     keeps 99.9% of its mass beyond |xi| > 4 (81.8% beyond |xi| > 8), so the
#     gate integrals become truncation-sensitive, and the strip contraction
#     fails on the scanned range (max |L_base| = 1.4e2 on t <= 150, no
#     T_need).  Reported as a scoped limitation, not as a verdict.
#
# Instruments (F77 discipline): the prime channel is computed twice —
#   E-A  dual-grid route: prime term = 2 sum (Lambda(n)/sqrt n) Re F_f(log n)
#        with F_f(x) = ∫ f(xi) e^{2 pi i xi x} dxi by FFT of f = W, P W, P²W;
#   E-B  direct route: K(xi) on the grid and the direct sum of the integral.
# Both are reported whenever E-B is affordable, plus the tail diagnostics
# ∫_{|xi|>Xi} W / ∫ W and the replay window checks.
#
# Levers established by this rig (all numeric, none a proof):
#   F1  the grid MEASURE, not the integrand, is what the 1919 identity wants:
#       det = A^2 Var_nu(P) is homogeneous of degree 2 in the grid weights, so
#       passing K*W without dxi inflates det by exactly 1/dxi^2 (which reads as
#       a 1e4..1e6 "relative error" that is really a units error).  With dxi in
#       place both the two-sided variance form and the quartic moment form
#       reproduce the channel-split det to ~1e-7 relative at every dxi tested.
#   F2  an FFT-dual route must carry the phase of the array origin WITH THE
#       RIGHT SIGN: Re(fft(f) dxi exp(-2 pi i xi_0 x_k)) = int f e^{2 pi i xi x}
#       (calibrated at <= 6e-12 relative on f = exp(-xi^2), whose transform is
#       exact; the opposite sign reads 4.8e-07..6.3e-06 and the naive raw real
#       part up to 2.0).  Phase at the actual dual-grid frequency x_k, never at
#       the requested test point; and use an asymmetric grid, since on a grid
#       symmetric about 0 the two sign conventions nearly coincide.
#   F3  route A is interpolation-limited at fixed xi_max and is not certified;
#       the certified pair is (Ap, B), which agree to ~1e-8 and are stable in
#       dxi to 8 digits at the 1e-3 residual scale.
#   F4  the owner's W(0) = 0 exactly (raw node 1/2 pins L_base(1/2) = 1 and
#       L_corr(1/2) = 0), so the density is an odd-ish two-lobe object; the
#       archimedean and prime channels nearly cancel and the gate entries are
#       a 1e-3-level residual of 1e3..1e9-sized channel terms.
#
# No gate sign is proved here.

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402  (sigma_vec, primes)

T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------------------------ node data

def orbit_nodes(rho):
    return [rho, 1 - np.conj(rho), np.conj(rho), 1 - rho]


def target_nodes(rho):
    return orbit_nodes(rho) + [rho + 0.5, 0.5, 1.0, 1.5]


def target_value(rho, z):
    orb = orbit_nodes(rho)
    if z == rho:
        return 1.0 + 0j
    if z == 1 - np.conj(rho):
        return -1.0 + 0j
    if z in orb:
        return 0j
    if z == rho + 0.5:
        return -1.0 + 0j
    return 0j


def counterpart_nodes(rho):
    """Centered orbit nodes of the four-point annihilator (record 1918)."""
    return [rho - 0.5, (1 - np.conj(rho)) - 0.5,
            np.conj(rho) - 0.5, (1 - rho) - 0.5]


# ------------------------------------------------------------- profiles (phi)

def phi_fun(x, a, k):
    """phi(x) = exp(-k/(1 - (x/a)^2)) on |x| < a, else 0  (C-infinity)."""
    u = np.abs(np.asarray(x, dtype=float)) / a
    out = np.zeros_like(u)
    m = u < 1.0
    out[m] = np.exp(-k / (1.0 - u[m] ** 2))
    return out


def phi_weights(a, panels=6, m=400):
    """Composite Gauss-Legendre nodes/weights for phi on [-a, a]."""
    xs, ws = np.polynomial.legendre.leggauss(m)
    edges = np.linspace(-a, a, panels + 1)
    X, W = [], []
    for j in range(panels):
        lo, hi = edges[j], edges[j + 1]
        X.append(0.5 * (hi - lo) * xs + 0.5 * (lo + hi))
        W.append(0.5 * (hi - lo) * ws)
    return np.concatenate(X), np.concatenate(W)


def phi_laplace(a, k, s, XW=None):
    """L_phi(s) = ∫ phi(x) e^{s x} dx for an array of complex s."""
    if XW is None:
        XW = phi_weights(a)
    X, W = XW
    f = phi_fun(X, a, k) * W
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    out = np.empty_like(s)
    step = max(1, int(4e6 // max(X.shape[0], 1)))
    for lo in range(0, s.shape[0], step):
        hi = min(lo + step, s.shape[0])
        out[lo:hi] = np.exp(np.outer(s[lo:hi], X)) @ f
    return out


def design_family(rho, scale=1.0):
    """One profile per target node: (scale a_j, weight theta_j = -Im node).

    Distinct scales inside each height group are what keeps the 8x8
    interpolation matrix usable: with a single fixed profile the rows at
    Re = 1/2 +- delta are indistinguishable (a function of exponential type
    a resolves Re only on the scale 1/a, and 2*delta < 1/a for small delta),
    the matrix is numerically singular, and the interpolant is then a
    difference of 1e22-sized terms whose value is pure roundoff.  The
    overall `scale` is the probe's free knob: it changes W's shape, hence
    the gate residual, without touching the pins or the contraction.
    """
    gam = float(rho.imag)
    groups = {gam: [2.0, 3.0, 4.0], -gam: [2.5, 3.5], 0.0: [2.0, 3.0, 4.0]}
    fam = []
    for z in target_nodes(rho):
        fam.append((scale * groups[float(z.imag)].pop(0), -float(z.imag)))
    return fam


def family_quad(fam, k):
    return [phi_weights(a, panels=6, m=400) for (a, _th) in fam]


def family_values(fam, k, s, XW):
    """V[j] = L_{phi_j}(s) for phi_j(x) = phi(x/a_j) e^{i theta_j x}
    (a_j * L_phi(a_j (s + i theta_j))); s may be an array."""
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    V = np.empty((len(fam), s.shape[0]), dtype=complex)
    for j, (a, th) in enumerate(fam):
        V[j, :] = a * phi_laplace(a, k, a * (s + 1j * th), XW=XW[j])
    return V


def family_interpolate(fam, k, XW, rho, ys):
    """Solve sum_j A_j phi_j(w_i) = ys_i and report the solve quality."""
    nodes = target_nodes(rho)
    M = family_values(fam, k, np.array(nodes, dtype=complex), XW).T
    cond = float(np.linalg.cond(M))
    A = np.linalg.solve(M, np.asarray(ys, dtype=complex))
    resid = float(np.max(np.abs(M @ A - np.asarray(ys, dtype=complex))))
    return A, {"cond": cond, "resid": resid, "max_A": float(np.max(np.abs(A)))}


def design_amplitudes(rho, fam, k, XW):
    """The two interpolation systems of hypothesis [6] / record [7]."""
    nodes = target_nodes(rho)
    ys_base = np.ones(len(nodes), dtype=complex)
    ys_corr = np.array([target_value(rho, z) for z in nodes])
    A_base, info_b = family_interpolate(fam, k, XW, rho, ys_base)
    A_corr, info_c = family_interpolate(fam, k, XW, rho, ys_corr)
    return A_base, A_corr, {"base": info_b, "corr": info_c}


# ------------------------------------------------------------- owner density

def owner_density_design(rho, fam, k, n, xi, XW, A=None):
    """W(xi) = |L_base(s)|^{2(n+1)} |L_corr(s)|² at s = 1/2 - 2 pi i xi.

    Also returns the cancellation ratio max_j |A_j phi_j| / |L|, which is
    the instrument's own error meter: the evaluation error is
    machine eps times that ratio, so a ratio near 1 certifies the reading.
    """
    if A is None:
        A = design_amplitudes(rho, fam, k, XW)[:2]
    A_base, A_corr = A
    s = 0.5 - 2j * np.pi * np.asarray(xi)
    V = family_values(fam, k, s, XW)          # (8, N)
    Lb = A_base @ V
    Lc = A_corr @ V
    W = np.abs(Lb) ** (2 * (n + 1)) * np.abs(Lc) ** 2
    term = np.abs(A_base[:, None] * V)
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(np.abs(Lb) > 0, term.max(axis=0)
                         / np.abs(Lb), np.inf)
    return W, Lb, Lc, ratio


# --- committed cardinal base (documented limitation mode) -------------------

def exp_neg_inv_glue(t):
    t = np.asarray(t, dtype=float)
    out = np.zeros_like(t)
    m = t > 0
    out[m] = np.exp(-1.0 / t[m])
    return out


def smooth_transition(t):
    t = np.asarray(t, dtype=float)
    a = exp_neg_inv_glue(t)
    b = exp_neg_inv_glue(1.0 - t)
    d = a + b
    out = np.zeros_like(t)
    nz = d > 0
    out[nz] = a[nz] / d[nz]
    return out


def seed_fun(x, r):
    """explicitSeed r:  r^{-1} smoothTransition(2 - |x|/r), support |x| < 2r."""
    return smooth_transition(2.0 - np.abs(np.asarray(x, dtype=float)) / r) / r


def node_product(nodes, z, s, vec=False):
    p = np.ones_like(s) if vec else (1.0 + 0.0j)
    skipped = False
    for t in nodes:
        if (not skipped) and t == z:
            skipped = True
            continue
        p = p * (t - s)
    return p


def cardinal_formula(nodes, ys, r, s, mass0, XW=None):
    """Record-1958 interpolation: sum_z y_z/(np z z * L_seed 0) np z s L_seed(s-z)."""
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    total = np.zeros_like(s)
    XW = phi_weights(2.0 * r, panels=4, m=600) if XW is None else XW
    seed_w = seed_fun(XW[0], r) * XW[1]
    for z, y in zip(nodes, ys):
        ls = np.exp(np.outer(s - z, XW[0])) @ seed_w
        total += (y / (node_product(nodes, z, z) * mass0)) \
            * node_product(nodes, z, s, vec=True) * ls
    return total


def owner_density_cardinal(rho, r, n, xi):
    nodes = target_nodes(rho)
    ys = np.array([target_value(rho, z) for z in nodes])
    XW = phi_weights(2.0 * r, panels=4, m=600)
    mass0 = float(np.sum(seed_fun(XW[0], r) * XW[1]))
    s = 0.5 - 2j * np.pi * np.asarray(xi)
    Lb = cardinal_formula(nodes, np.ones(len(nodes), dtype=complex), r, s,
                          mass0, XW=XW)
    Lc = cardinal_formula(nodes, ys, r, s, mass0, XW=XW)
    W = np.abs(Lb) ** (2 * (n + 1)) * np.abs(Lc) ** 2
    return W, Lb, Lc, {"mass0": mass0}, None


# ------------------------------------------------------------- gate entries

def P_from_nodes(xi, nodes):
    s = -2j * np.pi * np.asarray(xi)
    p = np.ones_like(s, dtype=complex)
    for a in nodes:
        p = p * (a - s)
    return p


def P_quartic(xi, delta, gamma):
    om = 2.0 * np.pi * np.asarray(xi)
    return (delta ** 2 + gamma ** 2 - om ** 2) ** 2 \
        + 4.0 * delta ** 2 * om ** 2


def interpolate_dual(Ff, xs_dual, logn):
    from scipy.interpolate import CubicSpline
    order = np.argsort(xs_dual)
    xo = xs_dual[order]
    Fo = Ff[order]
    sr = CubicSpline(xo, Fo.real)
    si = CubicSpline(xo, Fo.imag)
    return sr(logn) + 1j * si(logn)


def gate_entries(xi, W, P, support_radius, prime_cap=3000000):
    """Gate entries: archimedean channel plus the prime channel by 3 routes.

    Routes, and why each needs care (F2/F3: an FFT-dual route must carry the
    phase of the array origin, and the SIGN of that phase is fixed by the
    analytic model; see `calibration`):
      A   phased FFT of the xi-grid, spline-interpolated to x = log n;
      Ap  exact transform of the same samples (spline-refined xi-grid);
      B   direct kernel K on the xi-grid (sigma excluded, so route B total
          is arch + prime_B and not a double count).
    The spread across routes is the prime channel's error bar.
    """
    dxi = float(xi[1] - xi[0])
    sig = rig.sigma_vec(2.0 * np.pi * xi)
    fs = (W, P * W, P * P * W)
    arch = [float(np.trapezoid(sig * f, xi)) for f in fs]

    pset = rig.prime_powers_up_to(math.exp(support_radius))
    out = {"arch": arch, "dxi": dxi, "n_primes": int(len(pset)),
           "prime": {}}
    logn = np.array([math.log(nn) for nn, _ in pset])
    lam = np.array([l for _, l in pset], dtype=float)
    sq = np.array([nn for nn, _ in pset], dtype=float)
    if pset:
        n = xi.shape[0]
        xs_dual = np.fft.fftfreq(n, d=dxi)
        good = logn <= float(np.max(xs_dual))
        out["n_covered"] = int(np.sum(good))
        lg, lw, lq = logn[good], lam[good], sq[good]
        A, Ap, B = [], [], []
        if len(pset) <= prime_cap:
            for f in fs:
                F = np.fft.fft(f) * dxi * np.exp(-2j * np.pi * float(xi[0])
                                                 * xs_dual)
                r = interpolate_dual(F, xs_dual, lg)
                A.append(float(np.sum(lw / np.sqrt(lq) * 2.0 * r.real)))
            out["prime"]["A"] = A
        if len(pset) <= 4000:
            fine = np.linspace(float(xi[0]), float(xi[-1]), 8 * n)
            from scipy.interpolate import CubicSpline
            for f in fs:
                ff = CubicSpline(xi, f)(fine)
                tot = 0.0
                for i in range(lg.shape[0]):
                    tot += 2.0 * lw[i] / math.sqrt(lq[i]) * float(
                        np.trapezoid(ff * np.cos(2.0 * np.pi * fine * lg[i]),
                                     fine))
                Ap.append(float(tot))
            out["prime"]["Ap"] = Ap
        if len(pset) <= 60000:
            Kp = np.zeros_like(sig)
            for nn, l in pset:
                Kp = Kp + 2.0 * l * math.sqrt(1.0 / nn) \
                    * np.cos(2.0 * np.pi * xi * math.log(nn))
            for f in fs:
                B.append(float(np.trapezoid(Kp * f, xi)))
            out["prime"]["B"] = B
            # mu is the signed GRID MEASURE, weights dxi included: the 1919
            # identity is homogeneous of degree 2 in those weights, so handing
            # over the integrand K*W alone multiplies det by 1/dxi^2 (observed
            # as a bogus 1e4..1e6 "relative error" that is a units error).
            out["mu"] = (sig + Kp) * W * dxi
    key = next((kk for kk in CERTIFIED_ROUTES if kk in out["prime"]),
               next(iter(out["prime"]), "A"))
    pr = out["prime"].get(key, [float("nan")] * 3)
    out["route_key"] = key
    out["C"] = arch[0] + pr[0]
    out["B01"] = arch[1] + pr[1]
    out["D"] = arch[2] + pr[2]
    return out


def measure_stats(mu, x):
    """Mass/mean/variance of the positive and negative parts of a signed
    grid-measure mu with test x (record 1919 engine, verbatim)."""
    mp = mu[mu > 0].sum()
    mm = -mu[mu < 0].sum()
    xp = (mu * x)[mu > 0].sum() / mp
    xm = -(mu * x)[mu < 0].sum() / mm
    vp = (mu * x * x)[mu > 0].sum() / mp - xp * xp
    vm = -(mu * x * x)[mu < 0].sum() / mm - xm * xm
    return mp, mm, xp, xm, vp, vm


def variance_check(mu, P, xi, delta, gamma):
    """Record 1919's exact identity det = A^2 * Var_nu(P) as a SECOND
    algebraic route to the determinant: it never splits the kernel into
    channels and never transforms anything, so it is independent of the
    route-A/B question.  mu = K*W*dxi on the grid, nu = mu/A,
    Var_nu(P) = (1+f)Var_+ - f*Var_- - f(1+f)*Delta^2 with f = mu_-/A.

    The identity is exact for any finite signed measure (it is just
    det = A^2 (E_nu[P^2] - (E_nu P)^2) in the entries' own terms), so what it
    tests is that C, B01, D really are the moments of ONE grid measure.  Its
    two printed values are the two-sided variance form and the quartic moment
    expansion Var_nu(v^2 + aa*v), v = (2 pi xi)^2, aa = -2(gamma^2 - delta^2),
    which are the SAME quantity computed by different arithmetic; agreement
    between them and with the channel-split det is the content of the check.
    """
    A = float(np.sum(mu))
    if A == 0:
        return None
    mp, mm, xp, xm, vp, vm = measure_stats(mu, P)
    f = mm / A
    dm = xp - xm
    var = (1.0 + f) * vp - f * vm - f * (1.0 + f) * dm * dm
    om = 2.0 * np.pi * xi
    u2 = om * om
    nu = mu / A
    m1 = float(np.sum(nu * u2))
    m2 = float(np.sum(nu * u2 * u2))
    m3 = float(np.sum(nu * u2 ** 3))
    m4 = float(np.sum(nu * u2 ** 4))
    aa = -2.0 * (gamma * gamma - delta * delta)
    mform = (m4 - m2 * m2) + 2.0 * aa * (m3 - m1 * m2) \
        + aa * aa * (m2 - m1 * m1)
    return {"A": A, "f": float(f), "var_plus": float(vp),
            "var_minus": float(vm), "delta_mean": float(dm),
            "det_var": float(A * A * var),
            "det_moment": float(A * A * mform)}


CERTIFIED_ROUTES = ("Ap", "B")


def route_spread(ge):
    """Relative spread of each gate entry across the certified routes.

    Route A (dual-FFT plus spline interpolation in the dual variable) is
    recorded but excluded: interpolating the oscillatory dual transform
    costs 1e-2..1e-1 relative on a 1e-3-level residual, while Ap and B are
    the two no-interpolation routes and agree to 1e-5.
    """
    pr = ge["prime"]
    vals_avail = [kk for kk in CERTIFIED_ROUTES if kk in pr]
    if not vals_avail:
        vals_avail = list(pr)
    if not vals_avail:
        return [float("nan")] * 3
    spread = []
    for i in range(3):
        vals = [ge["arch"][i] + pr[kk][i] for kk in vals_avail]
        mx, mn = max(vals), min(vals)
        spread.append(float((mx - mn) / max(abs(mx), abs(mn), 1e-300)))
    return spread


# ------------------------------------------------------------- verification

def check_pins(rho, mode, fam=None, k=30.0, r=1.0, XW=None):
    """Re-evaluate every interpolation pin; the rig is only as good as this."""
    nodes = target_nodes(rho)
    ys = np.array([target_value(rho, z) for z in nodes])
    out = []
    if mode == "design":
        A_base, A_corr, _ = design_amplitudes(rho, fam, k, XW)
        for z, y in zip(nodes, ys):
            V = family_values(fam, k, np.array([z]), XW)[:, 0]
            Lb = complex(np.sum(A_base * V))
            Lc = complex(np.sum(A_corr * V))
            out.append({"node": [z.real, z.imag], "L_base": Lb,
                        "L_corr": Lc, "err_base": abs(Lb - 1.0),
                        "err_corr": abs(Lc - y)})
    else:
        XW2 = XW if XW is not None else phi_weights(2.0 * r)
        mass0 = float(np.sum(seed_fun(XW2[0], r) * XW2[1]))
        for z, y in zip(nodes, ys):
            Lb = cardinal_formula(nodes, np.ones(len(nodes), dtype=complex),
                                  r, [z], mass0, XW=XW2)[0]
            Lc = cardinal_formula(nodes, ys, r, [z], mass0, XW=XW2)[0]
            out.append({"node": [z.real, z.imag], "L_base": complex(Lb),
                        "L_corr": complex(Lc),
                        "err_base": abs(complex(Lb) - 1.0),
                        "err_corr": abs(complex(Lc) - y)})
    return out


def contraction_scan(rho, fam, k, tmax, nt=300, sigmas=(0.0, 0.25, 0.5,
                                                          0.75, 1.0), XW=None):
    """max |L_base(sigma + i t)| over the strip; smallest grid T with tail <= 1/2."""
    A_base, _, _ = design_amplitudes(rho, fam, k, XW)[:3]
    ts = np.linspace(0.0, tmax, nt)
    prof = np.zeros(nt)
    for s0 in sigmas:
        grid = np.asarray(s0 + 1j * ts, dtype=complex)
        V = family_values(fam, k, grid, XW)
        prof = np.maximum(prof, np.abs(A_base @ V))
    T_need = None
    for i in range(nt):
        if prof[i:].max() <= 0.5:
            T_need = float(ts[i])
            break
    return {"t_grid": ts.tolist(), "profile": prof.tolist(),
            "T_need": T_need, "global_max": float(prof.max()),
            "gamma": float(rho.imag)}


# --------------------------------------------------------------------- main

def tail_fraction(xi, W, cut):
    """(mass beyond |xi| > cut) / (total mass), plus the total mass."""
    dxi = float(xi[1] - xi[0])
    tot = float(np.sum(W) * dxi)
    if tot <= 0:
        return float("nan"), tot
    m = np.abs(xi) > cut
    return float(np.sum(W[m]) * dxi / tot), tot


def run_design(cases, xi_max=40.0, dxi=0.004, nt_cont=400, n_cont=40.0):
    out = []
    for (delta, gamma, n, k, scale) in cases:
        rho = (0.5 + delta) + 1j * gamma
        tag = "design sc=%.2f k=%.1f d=%.2f g=%.2f n=%d" % (scale, k, delta,
                                                            gamma, n)
        log("case %s" % tag)
        fam = design_family(rho, scale)
        XW = family_quad(fam, k)
        pins = check_pins(rho, "design", fam=fam, k=k, XW=XW)
        log("  pins: max |L_base-1| = %.2e ; max |L_corr-y| = %.2e"
            % (max(p["err_base"] for p in pins),
               max(p["err_corr"] for p in pins)))
        nxi = int(round(2.0 * xi_max / dxi)) + 1
        xi = np.linspace(-xi_max, xi_max, nxi)
        A_base, A_corr, info = design_amplitudes(rho, fam, k, XW)
        W, Lb, _Lc, ratio = owner_density_design(rho, fam, k, n, xi, XW,
                                                 A=(A_base, A_corr))
        cen = counterpart_nodes(rho)
        P = P_from_nodes(xi, cen)
        Pquar = P_quartic(xi, delta, gamma)
        prel = float(np.max(np.abs(np.imag(P))) / np.max(np.abs(P)))
        pdev = float(np.max(np.abs(np.real(P) - Pquar)) / np.max(Pquar))
        support_radius = max(a for a, _ in fam) * (n + 2)
        ge = gate_entries(xi, W, np.real(P), support_radius)
        dxi_eff = float(xi[1] - xi[0])
        tot = float(np.sum(W) * dxi_eff)
        xp = float(xi[np.argmax(W)])
        frac_cut = tail_fraction(xi, W, 0.7 * xi_max)[0]
        W0 = float(W[np.argmin(np.abs(xi))])
        D, C, B01 = ge["D"], ge["C"], ge["B01"]
        det = D * C - B01 * B01
        spread = route_spread(ge)
        branch = ("D<0" if D < 0 else
                  "D>0,det<0" if (D > 0 and det < 0) else "NO-WITNESS")
        if C > 0 and B01 > 0 and det < 0:
            branch = "VERTEX(B'=2B01>0)"
        elif C < 0 and B01 > 0 and D > 0:
            branch = "RAY(C<0,D>0)"
        elif C > 0 and D < 0:
            branch = "DOOR-A(D<0)"
        elif C < 0:
            branch = "RAY-OR-NONE(C<0)"
        cont = contraction_scan(rho, fam, k, n_cont, nt=nt_cont, XW=XW)
        rec = {
            "tag": tag, "rho": [rho.real, rho.imag], "n": n, "k": k,
            "scale": scale,
            "family": [[float(a), float(th)] for a, th in fam],
            "pin_err_base": max(p["err_base"] for p in pins),
            "pin_err_corr": max(p["err_corr"] for p in pins),
            "solve": info,
            "cancel_ratio_max": float(np.max(ratio[np.abs(Lb) > 0])),
            "xi_peak": xp, "gamma_over_2pi": gamma / (2.0 * math.pi),
            "W0": W0, "mass": tot, "tail_frac_0.7xi_max": frac_cut,
            "evenness_defect": evenness(W, xi),
            "P_imag_rel": prel, "P_quartic_rel": pdev,
            "support_radius": support_radius, "n_primes": ge["n_primes"],
            "arch_C": ge["arch"][0], "arch_B01": ge["arch"][1],
            "arch_D": ge["arch"][2],
            "prime_C": ge["prime"][ge["route_key"]][0],
            "prime_B01": ge["prime"][ge["route_key"]][1],
            "prime_D": ge["prime"][ge["route_key"]][2],
            "arch_share_D": ge["arch"][2] / D if D != 0 else None,
            "C": C, "B01": B01, "D": D, "det": det, "branch": branch,
            "prime_routes": {kk: [float(x) for x in vv]
                             for kk, vv in ge["prime"].items()},
            "spread_C": spread[0], "spread_B01": spread[1],
            "spread_D": spread[2],
            "variance_check": (variance_check(ge["mu"], np.real(P), xi,
                                              delta, gamma)
                               if "mu" in ge else None),
            "margin_rel": det / (4.0 * C * D) if (C * D) != 0 else None,
            "lam_vertex": B01 / C if C != 0 else None,
            "contraction_T_need": cont["T_need"],
            "contraction_max": cont["global_max"],
        }
        log("  W(0) = %.2e ; peak xi = %+.4f (gamma/2pi = %.4f) ; "
            "evenness defect %.2e ; tail(|xi|>%.1f)/mass = %.2e"
            % (W0, xp, gamma / (2.0 * math.pi), rec["evenness_defect"],
               0.7 * xi_max, frac_cut))
        log("  arch   C=%+.6e B01=%+.6e D=%+.6e  (arch share of D %.4f)"
            % (rec["arch_C"], rec["arch_B01"], rec["arch_D"],
               rec["arch_share_D"]))
        log("  prime  C=%+.6e B01=%+.6e D=%+.6e  (n_primes=%d)"
            % (rec["prime_C"], rec["prime_B01"], rec["prime_D"],
               rec["n_primes"]))
        log("  full   C=%+.6e B01=%+.6e D=%+.6e det=%+.6e margin=%s branch=%s"
            % (C, B01, D, det,
               ("%.3e" % rec["margin_rel"]) if rec["margin_rel"] else "n/a",
               branch))
        vc = rec["variance_check"]
        if vc:
            d1 = abs(vc["det_var"] - det) / max(abs(det), 1e-300)
            d2 = abs(vc["det_moment"] - det) / max(abs(det), 1e-300)
            log("  1919 variance identity: A=%+.6e f=%.4f det_var=%+.6e "
                "(rel %.1e) det_moment=%+.6e (rel %.1e)"
                % (vc["A"], vc["f"], vc["det_var"], d1, vc["det_moment"], d2))
        log("  route spread (rel): C %.1e B01 %.1e D %.1e  [routes %s]"
            % (rec["spread_C"], rec["spread_B01"], rec["spread_D"],
               ",".join(sorted(ge["prime"].keys()))))
        for kk in sorted(ge["prime"]):
            vv = ge["prime"][kk]
            log("    route %-2s total: C %+.6e  B01 %+.6e  D %+.6e"
                % (kk, ge["arch"][0] + vv[0], ge["arch"][1] + vv[1],
                   ge["arch"][2] + vv[2]))
        log("  contraction: max|L_base| on strip grid %.3e ; T_need = %s "
            "(gamma = %.3f)" % (rec["contraction_max"],
                                str(rec["contraction_T_need"]), gamma))
        out.append(rec)
    return out


def evenness(W, xi):
    sel = np.abs(xi) <= min(20.0, 0.5 * np.max(np.abs(xi)))
    xs = xi[sel]
    Ws = W[sel]
    Wm = np.interp(-xs, xi, W)
    denom = max(float(np.max(Ws)), 1e-300)
    return float(np.max(np.abs(Ws - Wm)) / denom)


def refinement(cases, dxis=(0.008, 0.004, 0.002, 0.001, 0.0005), xi_max=8.0):
    """Grid-refinement study: is the residual (C, B01, D) discretization-stable?

    This is the decisive instrument test on the residual scale. Route A is
    listed too but is known to be interpolation-limited (it flips D's sign
    at the residual scale); the certified content is the drift of the
    no-interpolation engines under dxi -> dxi/2.
    """
    out = []
    for (delta, gamma, n, k, scale) in cases:
        rho = (0.5 + delta) + 1j * gamma
        log("refine sc=%.2f k=%.1f d=%.2f g=%.2f n=%d" % (scale, k, delta,
                                                         gamma, n))
        fam = design_family(rho, scale)
        XW = family_quad(fam, k)
        A = design_amplitudes(rho, fam, k, XW)[:2]
        cen = counterpart_nodes(rho)
        support_radius = max(a for a, _ in fam) * (n + 2)
        rows = []
        for dxi in dxis:
            nxi = int(round(2.0 * xi_max / dxi)) + 1
            xi = np.linspace(-xi_max, xi_max, nxi)
            W, _Lb, _Lc, _r = owner_density_design(rho, fam, k, n, xi, XW,
                                                   A=A)
            P = np.real(P_from_nodes(xi, cen))
            ge = gate_entries(xi, W, P, support_radius)
            row = {"dxi": dxi, "nxi": nxi,
                   "arch_C": ge["arch"][0], "arch_B01": ge["arch"][1],
                   "arch_D": ge["arch"][2],
                   "variance_check": (variance_check(ge["mu"], P, xi, delta,
                                                     gamma)
                                      if "mu" in ge else None),
                   "routes": {kk: [float(x) for x in vv]
                              for kk, vv in ge["prime"].items()}}
            rows.append(row)
            log("  dxi = %8.5f : arch C %+.6e B01 %+.6e D %+.6e"
                % (dxi, ge["arch"][0], ge["arch"][1], ge["arch"][2]))
            for kk in sorted(ge["prime"]):
                vv = ge["prime"][kk]
                tot = [ge["arch"][i] + vv[i] for i in range(3)]
                det_k = tot[2] * tot[0] - tot[1] ** 2
                extra = ""
                if row["variance_check"] and kk == "B":
                    vc = row["variance_check"]
                    extra = ("  [1919 id: det_var %+.8e mom %+.8e "
                             "rel_var %.1e rel_mom %.1e]"
                             % (vc["det_var"], vc["det_moment"],
                                abs(vc["det_var"] - det_k)
                                / max(abs(det_k), 1e-300),
                                abs(vc["det_moment"] - det_k)
                                / max(abs(det_k), 1e-300)))
                log("      %-2s total: C %+.8e B01 %+.8e D %+.8e det %+.6e%s"
                    % (kk, tot[0], tot[1], tot[2], det_k, extra))
        out.append({"rho": [rho.real, rho.imag], "n": n, "k": k,
                    "scale": scale, "rows": rows})
    return out


def calibration():
    """Machine-level test of the dual-FFT phase convention (lever F2).

    On the analytic model f(xi) = exp(-xi^2) the transform is exact,
    F(x) = int f e^{2 pi i xi x} dxi = sqrt(pi) exp(-(pi x)^2), so the phase
    of the array origin is the ONLY thing under test.  Two traps, both hit in
    this rig's first version: (i) the phase must be evaluated at the ACTUAL
    dual-grid frequency xs[i], not at the requested test point; (ii) on a
    grid symmetric about 0 (n odd, x0 = -x1) Im(fft) is small, so the two
    sign conventions barely separate -- the decisive grid is asymmetric.
    Measured with the wrong sign `exp(+2 pi i x0 x)`: rel 4.8e-07 at
    x = 0.31 rising to 6.3e-06 at x = 1.12 (grows with x); with the correct
    sign `exp(-2 pi i x0 x)`: rel <= 6e-12 at every sampled point."""
    mod = lambda z: np.exp(-z * z)                              # noqa: E731
    xs_test = (0.13, 0.3, 0.55, 1.1)
    for (x0, x1, n) in ((-8.0, 8.0, 32000), (-8.0, 8.0, 32001)):
        xi = np.linspace(x0, x1, n)
        dxi = float(xi[1] - xi[0])
        xs = np.fft.fftfreq(n, d=dxi)
        F = np.fft.fft(mod(xi)) * dxi
        e_ok = e_bad = e_na = 0.0
        for xt in xs_test:
            i = int(np.argmin(np.abs(xs - xt)))
            xk = float(xs[i])
            th = 2.0 * math.pi * x0 * xk
            exact = math.sqrt(math.pi) * math.exp(-(math.pi * xk) ** 2)
            a, b = F[i].real, F[i].imag
            ok = a * math.cos(th) + b * math.sin(th)     # Re(z e^{-i th})
            bad = a * math.cos(th) - b * math.sin(th)    # Re(z e^{+i th})
            e_ok = max(e_ok, abs(ok - exact) / exact)
            e_bad = max(e_bad, abs(bad - exact) / exact)
            e_na = max(e_na, abs(a - exact) / exact)
        log("  calib grid [%g,%g] n=%d : max rel err  correct sign %.2e | "
            "wrong sign %.2e | naive %.2e" % (x0, x1, n, e_ok, e_bad, e_na))
    log("  (naive = the raw real part; its error is |exp(2 pi i x0 x) - 1| "
        "on the sampled points, i.e. up to 2.0)")


def main():
    log("record 1959 — committed-owner density probe (map 106, P0)")
    quick = "--quick" in sys.argv
    cardinal_mode = "--cardinal" in sys.argv

    if "--calib" in sys.argv:
        log("mode CALIB: analytic model test of the dual-FFT phase convention")
        calibration()

    if cardinal_mode:
        log("mode CARDINAL: committed 1958 interpolation base with explicitSeed")
        r = 1.0
        delta, gamma = 0.05, 14.134725141734693
        rho = (0.5 + delta) + 1j * gamma
        nodes = target_nodes(rho)
        ys = np.array([target_value(rho, z) for z in nodes])
        XW = phi_weights(2.0 * r, panels=4, m=600)
        mass0 = float(np.sum(seed_fun(XW[0], r) * XW[1]))
        pins = check_pins(rho, "cardinal", r=r, XW=XW)
        log("  pins: max |L_base-1| = %.2e ; max |L_corr-y| = %.2e"
            % (max(p["err_base"] for p in pins),
               max(p["err_corr"] for p in pins)))
        xi = np.linspace(-60.0, 60.0, 30001)
        W, Lb, _Lc, _info, _ = owner_density_cardinal(rho, r, 0, xi)
        ts = np.linspace(0.0, 150.0, 151)
        prof = np.zeros(ts.shape[0])
        for s0 in (0.0, 0.25, 0.5, 0.75, 1.0):
            Lp = cardinal_formula(nodes, np.ones(len(nodes), dtype=complex),
                                  r, s0 + 1j * ts, mass0, XW=XW)
            prof = np.maximum(prof, np.abs(Lp))
        T_need = None
        for i in range(ts.shape[0]):
            if prof[i:].max() <= 0.5:
                T_need = float(ts[i])
                break
        frac, tot = tail_fraction(xi, W, 45.0)
        cuts = [(c, tail_fraction(xi, W, c)[0]) for c in (4.0, 8.0, 16.0)]
        log("  W(0) = %.2e ; peak xi = %+.4f ; |L_base| at xi=30: %.3e"
            % (W[np.argmin(np.abs(xi))], xi[np.argmax(W)],
               np.abs(Lb[np.argmin(np.abs(xi - 30.0))])))
        log("  mass beyond |xi| > 4 / 8 / 16 : %s"
            % " / ".join("%.4f" % f for _, f in cuts))
        log("  mass fraction beyond |xi| > 45: %.4f ; contraction scan on "
            "t <= 150: max|L_base| = %.3e ; T_need = %s (gamma = %.3f)"
            % (frac, prof.max(), str(T_need), gamma))
        log("  => cardinal base is NOT usable for a gate reading: its Gevrey "
            "tail keeps |L_base| = O(10) at height 2*pi*30, %.1f%% of the "
            "density mass sits beyond |xi| > 4 (peak |xi| = %.2f, designed "
            "base: |xi| <~ 4), and the strip contraction fails on the "
            "scanned range" % (100.0 * cuts[0][1], abs(xi[np.argmax(W)])))
        os.makedirs("results", exist_ok=True)
        # pins carry complex Laplace values; serialize the magnitudes of the
        # pin errors only (the complex values are not needed downstream)
        pins_out = [{kk: (abs(vv) if isinstance(vv, complex) else vv)
                     for kk, vv in p.items()} for p in pins]
        with open("results/1959_cardinal_base_limitation.json", "w") as fh:
            json.dump({"r": r, "rho": [rho.real, rho.imag],
                       "pins": pins_out, "mass0": mass0,
                       "W0": float(W[np.argmin(np.abs(xi))]),
                       "xi_peak": float(xi[np.argmax(W)]),
                       "mass_beyond_45": frac, "mass_total": tot,
                       "mass_beyond": {str(c): f for c, f in cuts},
                       "t_grid": ts.tolist(), "contraction_profile":
                       prof.tolist(), "T_need": T_need,
                       "njobs_note": "cardinal interpolation base"},
                      fh, indent=1, default=float)
        log("wrote results/1959_cardinal_base_limitation.json")
        return

    G1, G2 = 14.134725141734693, 21.022039638771555
    cases = [(0.05, G1, 0, 30.0, 1.0)]
    if not quick:
        # main grid: n <= 1 keeps the support (hence the prime book) inside
        # the direct route's budget; n = 2 shrinks the windows instead
        cases = [(d, g, n, 30.0, 1.0)
                 for g in (G1, G2) for d in (0.05, 0.10, 0.30) for n in (0, 1)]
        cases += [(d, g, 2, 30.0, 0.5)
                  for g in (G1, G2) for d in (0.05, 0.10, 0.30)]
        # free-knob scan at the same rho: the gate residual is a 1e-3-level
        # arch/prime cancellation, so its sign must be mapped, not assumed
        cases += [(0.05, G1, 0, 30.0, sc) for sc in (0.7, 0.8, 0.9, 1.1, 1.2)]
        cases += [(0.05, G1, 0, kk, 1.0) for kk in (20.0, 40.0, 60.0)]
    res = run_design(cases)
    os.makedirs("results", exist_ok=True)
    with open("results/1959_fourpoint_owner_density.json", "w") as fh:
        json.dump({"mode": "design", "cases": res}, fh, indent=1,
                  default=float)
    log("wrote results/1959_fourpoint_owner_density.json")

    if "--refine" in sys.argv:
        ref_cases = [(0.05, G1, 0, 30.0, sc) for sc in (1.0, 0.9, 0.8)]
        ref_cases += [(0.05, G1, 0, 40.0, 1.0), (0.10, G1, 0, 30.0, 1.0)]
        refs = refinement(ref_cases)
        with open("results/1959_refinement.json", "w") as fh:
            json.dump({"mode": "refinement", "cases": refs}, fh, indent=1,
                      default=float)
        log("wrote results/1959_refinement.json")

    if "--scan" in sys.argv:
        # width of the pivot-positive window along the free knob
        scan = [(0.05, G1, 0, 30.0, sc)
                for sc in (0.82, 0.84, 0.86, 0.88, 0.90, 0.92, 0.94, 0.96,
                           0.98)]
        res2 = run_design(scan)
        with open("results/1959_scale_scan.json", "w") as fh:
            json.dump({"mode": "scale_scan", "cases": res2}, fh, indent=1,
                      default=float)
        log("wrote results/1959_scale_scan.json")


if __name__ == "__main__":
    main()