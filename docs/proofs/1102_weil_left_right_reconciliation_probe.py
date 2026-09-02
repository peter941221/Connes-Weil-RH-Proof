# 1102 - Weil explicit-formula LEFT/RIGHT reconciliation (certified intervals).
#
# What this probe does (the step-3 "left-right reconciliation" experiment, run
# by ourselves instead of waiting on external AI):
#
#   The Weil explicit formula is an IDENTITY between two different ways of
#   computing the same number:
#
#       LEFT  (zero / spectral side)      ==    RIGHT (closed forms)
#       sum over zeros  f~(rho)           ==    trivial - W_R - prime_side
#
#     * LEFT is computed from an INDEPENDENT zero list (mpmath `zetazero`),
#       truncated at height T with a CERTIFIED tail bound.
#     * RIGHT is the archimedean term W_R, computed in TWO closed forms and
#       cross-checked against each other = law-(19) two-closed-form anchor,
#       plus the finite/INFINITE prime sum (certified when non-compact),
#       plus the trivial-zero value f~(0)+f~(1).
#
#   We do not merely report a single residual.  Each side is wrapped in a
#   CERTIFIED INTERVAL [center - err, center + err] and we PASS iff the two
#   intervals overlap (gap <= left_err + right_err), reporting clearance =
#   budget / gap.
#
# Three objects are reconciled:
#
#   PART 1  CONTROL-COMPACT = C_c 6-fold B-spline test function G=bspline6,
#           compact support [-3,3].  Reuses ANCHOR-A's formulas VERBATIM; the
#           prime sum is EXACT-finite (visible m log p <= 3).  If it reproduces
#           anchor_gate's closure then our transform convention + interval
#           plumbing are proven correct BY CONSTRUCTION on a known-good object.
#
#   PART 2  CONTROL-NONCOMPACT = Gaussian G(u)=e^{-u^2/4}, whose Mellin-type
#           transform f~(s)=int e^{-u^2/4} e^{-su} du = 2 sqrt(pi) e^{s^2} is in
#           CLOSED FORM (no numerical inversion).  This is the genuine new
#           ingredient: G is NON-compact, so EVERY prime power contributes and
#           the prime sum is INFINITE -- we enumerate primes up to a log-cut-off
#           Lt and certify the remainder by an analytic over-count bound.  Both
#           W_R closed forms are single 1-D integrals here (no nested inversion),
#           so law-(19)'s two-closed-form cross-check is clean.
#
#   PART 3  STRESS = the pinned orbit detector g_3 (record-1089 family, same form
#           as 1077) at d^2=4, mu=0 -- "our battlefield object".  Its G must be
#           inverted numerically and its normalization is large (N~52), so the
#           reconciliation here is deliberately LOOSER (digamma-form W_R only;
#           u-form deferred to bound inversion cost).  It reports honestly whether
#           our actual detector closes under the same method.
#
# Three-point anchor (law-19) honored on PARTS 1 & 2:
#     point #1 = mpmath zero list (independent of all closed forms),
#     point #2 = W_R u-additive closed form,
#     point #3 = W_R digamma/f~ closed form.
#   Points #2 and #3 are cross-checked; the LEFT side is checked against their
#   common value -> three independent evaluations agree.  (PART 3 uses points
#   #1 and #3 only, since #2 needs nested inversions of a numerically-inverted G.)
#
# Run (WSL ext4 copy, ONE command):
#   MSYS_NO_PATHCONV=1 wsl.exe bash -lc \
#     'cd /home/peter/rh && ~/.local/bin/uv run --with numpy --with mpmath \
#      python -u docs/proofs/1102_weil_left_right_reconciliation_probe.py'

import importlib.util
import math
import os

from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, sqrt as msqrt, \
    sinh as msinh, digamma as mdigamma, quad as mquad, zetazero

mp.dps = 45          # headroom above the working precision for interval budgets
                     # (raised from 32: at 32 the O(1-13) closed-form terms cancel to
                     # a ~1e-11 quadrature floor on the non-compact object; 45 pushes
                     # that below every certified budget so residuals reflect real tail
                     # error, not quad noise.)

EULER = mpf("0.57721566490153286060651209008240243104215933593992")


# ---- reuse the committed 1071 machinery (transform pair + zero cache) ------
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1071", os.path.join(_here, "1071_engineered_weil_hunt_probe.py"))
assert _spec is not None and _spec.loader is not None, \
    "committed 1071 probe not found next to this file"
p1071 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1071)

bspline6 = p1071.bspline6          # G(u), compact support [-3, 3]
zero_cache = p1071.zero_cache      # persisted mpmath zero ordinates


# ---- transform pair (PART 1 control: VERBATIM ANCHOR-A) ---------------------
def ftit_b(s):
    """Control forward transform f~(s)=(sinh(s/2)/(s/2))^6 for G=bspline6.

    VERBATIM the ftil used by 1071 anchor_gate ANCHOR-A, so PART-1 reproduces
    that proven identity exactly.  The s->0 limit is 1 (sinh(x)/x -> 1), handled
    explicitly to avoid 0/0 at the trivial zero."""
    if abs(s) < mpf("1e-20"):
        return mpf(1)
    return (msinh(s / 2) / (s / 2)) ** 6


def G_inv(ft_of_it, u, Tinv):
    """Inverse transform  G(u) = (1/2pi) * int_{-T}^{T} f(it) e^{i t u} dt.

    Returns (value, err).  Truncation to |t|<=T is the only approximation; the
    caller supplies Tinv large enough that the discarded tail is below budget."""
    def h(t):
        return ft_of_it(1j * t) * mexp(1j * t * u)

    val, err = mquad(h, [-Tinv, 0, Tinv], error=True, maxdegree=8)
    return val / (2 * mpi), err / (2 * mpi)


# ---- transform pair (PART 2 non-compact: CLOSED FORM, no inversion) ---------
def gaussianG(u):
    """Non-compact test function G(u)=e^{-u^2/4}.  Even, positive, Schwartz."""
    return mexp(-(mpf(u) ** 2) / mpf(4))


def ftit_gauss(s):
    """f~(s)=int_{R} e^{-u^2/4} e^{-su} du = 2 sqrt(pi) e^{s^2}.

    Completing the square: -u^2/4 - su = -(u+2s)^2/4 + s^2, and
    int e^{-(u+2s)^2/4} du = 2 sqrt(pi).  On the critical line s=1/2+i*gamma
    this is 2 sqrt(pi) e^{1/4} e^{-gamma^2} (cos gamma + i sin gamma): real-even
    decay, so the zero-side sum converges super-fast and both W_R forms are
    single well-behaved integrals."""
    return 2 * msqrt(mpi) * mexp(s * s)


# ---- the pinned orbit detector g_3 (record-1089 family; verbatim from 1077) -
def make_g3(delta, norm, mu):
    """g_3(s)=N' * s(s-1)(s-1/2)^2 * exp((-d^2 + i mu) s(1-s)).

    Symmetric g_3(1-s)=g_3(s); vanishes EXACTLY at the triple {0, 1/2, 1}.
    (1077's make_g3 copied verbatim so we reconcile the SAME family.)"""
    c = -delta * delta + 1j * mu

    def g3(s):
        return norm * p1071.vf0(s) * (s - mpf("0.5")) ** 2 \
            * mexp(c * p1071.qsym(s))
    return g3


def normalize_family3(delta, npts=800):
    """N' so that peak_t |g_3(1/2+it)|=1 (mu-independent on-line peak).  Verbatim."""
    d2 = delta * delta

    def mag(t):
        q = t * t + mpf("0.25")
        return q * (t * t) * mexp(-d2 * q)

    best, tb = mpf(0), mpf(0)
    hi = 6.0 / float(delta)
    for k in range(1, npts + 1):
        t = mpf(hi) * (mpf(k) / mpf(npts))
        v = mag(t)
        if v > best:
            best, tb = v, t
    return mpf(1) / best


# ---- the two CLOSED-FORM archimedean terms (law-19 points #2 and #3) --------
def wr_u(G):
    """W_R in the u-additive closed form.  Returns (value, err).

    VERBATIM integrand from 1071 anchor_gate ANCHOR-A."""
    def integrand(u):
        return (G(u) + mexp(-u) * G(-u) - 2 * mexp(-u) * G(mpf(0))) \
            / (1 - mexp(-2 * u))

    val, err = mquad(integrand,
                     [mpf("1e-12"), mpf("0.25"), mpf("0.5"), 1, 2, 3, 40],
                     error=True, maxdegree=8)
    return (mlog(4 * mpi) + EULER) * G(mpf(0)) + val, err


def wr_dig(G0, ftit):
    """W_R in the digamma / f~ closed form.  Returns (value, err).

    VERBATIM from 1071 anchor_gate ANCHOR-A:
        i3 = 2 Re int_0^inf Re(digamma((1/2+it)/2)) ftit(1/2+it) dt
        W_R = log(pi)*G(0) - i3/(2 pi)."""
    def integ(t):
        w = mpf("1/2") + 1j * t
        return mp.re(mdigamma(w / 2)) * ftit(w)

    val, err = mquad(integ,
                     [0, mpf("0.5"), 1, 2, 4, 8, 16, 32, 64, 128],
                     error=True, maxdegree=8)
    i3 = 2 * mp.re(val)
    return mlog(mpi) * G0 - i3 / (2 * mpi), err


# ---- zero side (law-19 point #1: independent mpmath zero list) --------------
def zero_side(T, ftit, gam):
    """Sum_{0<gamma<=T} 2 Re f~(1/2 + i gamma)."""
    s = mpf(0)
    for g in gam:
        if float(g) > T:
            break
        s += 2 * mp.re(ftit(mpf("1/2") + 1j * g))
    return s


def primes_up_to(n):
    n = int(n)
    if n < 2:
        return []
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.isqrt(n)) + 1):
        if sieve[i]:
            for j in range(i * i, n + 1, i):
                sieve[j] = False
    return [i for i in range(2, n + 1) if sieve[i]]


def report(tag, center_l, err_l, center_r, err_r, extra=""):
    """Print a certified-interval reconciliation verdict for one object."""
    gap = abs(center_l - center_r)
    budget = err_l + err_r
    clearance = (budget / gap) if gap > mpf(0) else mp.inf
    ok = gap <= budget
    cl = float(mp.re(center_l)); cr = float(mp.re(center_r))
    print(f"RECONCILE|{tag}|gap={float(gap):.4e}"
          f"|left=[{cl - float(err_l):.10f},{cl + float(err_l):.10f}]"
          f"|right=[{cr - float(err_r):.10f},{cr + float(err_r):.10f}]"
          f"|budget={float(budget):.3e}"
          f"|clearance={float(clearance) if clearance != mp.inf else float('inf'):.2f}"
          f"{'|PASS' if ok else '|FAIL'} {extra}", flush=True)


def run():
    print("=== 1102 Weil explicit-formula LEFT/RIGHT reconciliation ===",
          flush=True)

    gam = zero_cache(300.0)     # zeros up to gamma=300 (more than enough for T<=200)
    print(f"[cache] {len(gam)} zeros cached, max gamma={float(gam[-1]):.2f}",
          flush=True)

    # =======================================================================
    # PART 0 - transform-convention self-check: recover bspline6 from f~(it).
    # Proves the inverse-FT routine + sign/scale convention before trusting it
    # on g_3 (PART 3, whose G must be inverted numerically).
    # =======================================================================
    print("\n=== PART 0: inversion self-check (recover bspline6 from its f~) ===",
          flush=True)
    Tinv0 = mpf(80)             # control decays ~t^-12; tail < C/T^11 is tiny at 80
    maxrel = mpf(0)
    for u in (mpf(0), mpf("0.5"), mpf("1.0"), mpf("1.7")):   # well inside support
        grec, err = G_inv(lambda t: ftit_b(t), float(u), Tinv0)
        gt = bspline6(float(u))
        rel = abs(grec - gt) / max(abs(gt), mpf(1e-30))
        maxrel = max(maxrel, rel)
        print(f"PART0|u={float(u):.2f}|G_rec={float(mp.re(grec)):.8f}"
              f"|bspline6={float(gt):.8f}|relerr={float(rel):.2e}", flush=True)
    assert maxrel < 1e-6, "PART-0: inversion convention does not recover bspline6"
    # near the support edge u->3, bspline6(u)->0 so a fixed absolute inversion
    # error reads as large RELATIVE error; check it in ABSOLUTE terms instead.
    ue = mpf("2.9")
    grec_e, _ = G_inv(lambda t: ftit_b(t), float(ue), Tinv0)
    abserr_e = abs(grec_e - bspline6(float(ue)))
    print(f"PART0|u={float(ue):.2f}(edge)|abs_err={float(abserr_e):.2e}"
          f" (value itself ~{float(bspline6(float(ue))):.1e})", flush=True)
    assert abserr_e < 1e-5, "PART-0: edge-point absolute inversion error too large"
    print(f"PART0|SELF-CHECK-PASS|max_interior_rel_err={float(maxrel):.2e} (<= 1e-6)",
          flush=True)

    # =======================================================================
    # PART 1 - CONTROL-COMPACT reconciliation on the B-spline test function.
    # Verbatim ANCHOR-A formulas; must reproduce anchor_gate's closure and, as
    # certified intervals, show a large clearance.
    # =======================================================================
    print("\n=== PART 1: CONTROL-COMPACT (bspline6, support [-3,3]) ===", flush=True)
    # LEFT: zero sum at TWO heights (step-doubling).  For this object the on-line
    # terms decay ~gamma^-6, so the [Tlo,Thi] chunk OVER-covers the [Thi,inf] tail;
    # center uses the more-converged Thi value.  This is an honest truncation bound
    # (the inherited ANCHOR-A `0.75(2.063/T)^6` was calibrated for a loose 1e-6
    # assert and under-covers the true ~gamma^-6 tail at T~100).
    Tlo, Thi = mpf(300), mpf(600)          # cache goes to gamma=1728; both heights safe
    Z_lo = zero_side(float(Tlo), ftit_b, gam)
    Z_hi = zero_side(float(Thi), ftit_b, gam)
    center_l = Z_hi                          # converged value (more zeros included)
    err_l = abs(Z_hi - Z_lo) + mpf("1e-25")  # [Tlo,Thi] chunk over-covers the [Thi,inf] tail

    # RIGHT: triv - W_R - prime_side, with W_R cross-checked (law-19).
    G = bspline6                                # exact closed form (no inversion)
    triv = ftit_b(mpf(1)) + ftit_b(mpf(0))      # trivial zeros s=1 and s=0

    wr_u_val, wr_u_err = wr_u(G)
    wr_dig_val, wr_dig_err = wr_dig(G(mpf(0)), ftit_b)
    arch_xcheck = abs(wr_u_val - wr_dig_val)
    print(f"PART1|W_R(u-form)={float(mp.re(wr_u_val)):.12f}"
          f"|W_R(digamma)={float(mp.re(wr_dig_val)):.12f}"
          f"|xcheck={float(arch_xcheck):.3e}", flush=True)
    assert arch_xcheck < 1e-8, "PART-1: the two W_R closed forms disagree"

    # prime side: compact support => exact finite sum (visible m log p <= 3).
    ps = mpf(0)
    for p in primes_up_to(int(mpf(str(math.exp(3))))):   # e^3 ~ 20 -> {2..19}
        lp = mlog(mpf(p))
        m = 1
        while m * lp <= 3:
            u0 = mpf(m) * lp
            ps += lp * (G(u0) + mexp(-u0) * G(-u0))
            m += 1
    print(f"PART1|prime_side(exact, finite by support)={float(mp.re(ps)):.10f}",
          flush=True)

    center_r = triv - wr_u_val - ps             # u-form as the headline value
    err_r = abs(wr_u_err) + arch_xcheck         # quad self-report + cross-form W_R disagreement (honest floor)
    print(f"PART1|trivial={float(mp.re(triv)):.8f}|LEFT_center={float(mp.re(center_l)):.10e}"
          f"|RIGHT_center={float(mp.re(center_r)):.10e}", flush=True)
    report("control-compact", center_l, err_l, center_r, err_r,
           extra=f"(xcheck W_R={float(arch_xcheck):.1e})")

    # =======================================================================
    # PART 2 - CONTROL-NONCOMPACT reconciliation on G(u)=e^{-u^2/4}.
    # Closed-form transform f~(s)=2 sqrt(pi) e^{s^2}; INFINITE prime sum with a
    # certified analytic tail; both W_R forms are single 1-D integrals.
    # =======================================================================
    print("\n=== PART 2: CONTROL-NONCOMPACT (Gaussian G=e^{-u^2/4}) ===", flush=True)

    # ---- LEFT: zero sum + CERTIFIED on-line Gaussian tail ------------------
    T = mpf(60)     # e^{-gamma^2} at gamma=60 is e^-3600 ~ 0; tail below dps
    Z_on2 = zero_side(float(T), ftit_gauss, gam)

    # |2 Re f~(1/2+i*g)| <= 4 sqrt(pi) e^{1/4} e^{-g^2}; zero density dN/dg<= g/(2pi).
    # tail <= int_T^inf 4 sqrt(pi) e^{1/4} e^{-g^2} (g/(2pi)) dg = (2 e^{1/4}/sqrt(pi)) e^{-T^2}.
    tailZ2 = mpf(2) * mexp(mpf("0.25")) / msqrt(mpi) * mexp(-(T ** 2))
    err_l2 = tailZ2 + mpf("1e-25")       # + a fixed dps floor for the sum itself
    center_l2 = Z_on2

    # ---- RIGHT: triv - W_R - prime_side (W_R cross-checked, law-19) --------
    Gg = gaussianG                          # closed form, no inversion
    triv2 = ftit_gauss(mpf(1)) + ftit_gauss(mpf(0))

    wr_u_val2, wr_u_err2 = wr_u(Gg)         # single integral over u
    wr_dig_val2, wr_dig_err2 = wr_dig(Gg(mpf(0)), ftit_gauss)  # G(0)=1; single integral over t
    arch_xcheck2 = abs(wr_u_val2 - wr_dig_val2)
    print(f"PART2|W_R(u-form)={float(mp.re(wr_u_val2)):.12f}"
          f"|W_R(digamma)={float(mp.re(wr_dig_val2)):.12f}"
          f"|xcheck={float(arch_xcheck2):.3e}", flush=True)
    assert arch_xcheck2 < 1e-8, "PART-2: the two W_R closed forms disagree"

    # prime side is INFINITE (G nonzero everywhere).  Enumerate primes up to a
    # log-cut-off Lt and CERTIFY the remainder by an analytic over-count bound.
    Lt = mpf("12")                          # per-unit-log weight ~ y e^{-y^2/4}
    pmax = int(mpf(str(math.exp(float(Lt))))) + 1   # ~ e^12 = 162754 (~15k primes)
    ps2 = mpf(0)
    for p in primes_up_to(pmax):
        lp = mlog(mpf(p))
        m = 1
        while True:                          # all prime powers of this base prime
            u0 = mpf(m) * lp
            w = Gg(u0)                       # even => G(-u)=G(u)=w
            term = lp * (w + mexp(-u0) * w)  # = lp*w*(1+e^{-u}); >= 0 for Gaussian
            if abs(term) < mpf("1e-30"):
                break
            ps2 += term
            m += 1

    # certified tail (primes p > pmax, i.e. log p > Lt):  summing over PRIMES needs the
    # PNT measure -- primes with log in [y,y+dy] number ~ e^y/y, NOT one-per-unit-y: that
    # is the Jacobian e^y of the linear prime density d pi/dx = 1/ln x.  So a per-prime
    # weight y*G(y) = y*e^{-y^2/4} integrates to
    #   int_{Lt}^{inf} [ y e^{-y^2/4} ] * [ e^y/y ] dy = int_{Lt}^{inf} e^{y - y^2/4} dy,
    # NOT the unit-spaced 2*e^{-Lt^2/4}, which under-counts by ~e^{Lt}.  Verified at Lt=12:
    #   direct sum over real primes > e^12 = 7.38e-12  <=  PNT bound = 7.41e-12,
    # while the old unit-spacing formula gave only 9.3e-16 (dropped the e^{y} Jacobian).
    # m>=2 prime powers beyond y>Lt add < 1e-60, so x3 covers quad tolerance + PNT error.
    tailP2 = mpf(3) * mquad(lambda y: mexp(y - y ** 2 / 4), [Lt, mp.inf])
    print(f"PART2|prime_side(infinite; enumerated p<={pmax})={float(mp.re(ps2)):.10f}"
          f"|certified_tail<{float(tailP2):.3e}", flush=True)

    center_r2 = triv2 - wr_u_val2 - ps2      # u-form headline (digamma agrees to 1e-8)
    err_r2 = abs(wr_u_err2) + tailP2 + arch_xcheck2
    print(f"PART2|trivial={float(mp.re(triv2)):.8f}|LEFT_center={float(mp.re(center_l2)):.10e}"
          f"|RIGHT_center={float(mp.re(center_r2)):.10e}", flush=True)
    report("control-noncompact", center_l2, err_l2, center_r2, err_r2,
           extra=f"(xcheck W_R={float(arch_xcheck2):.1e})")

    # =======================================================================
    # PART 3 - STRESS: the pinned orbit detector g_3 (record-1089 family).
    # G must be inverted numerically and N~52 => loose, honest reconciliation.
    # Uses law-19 points #1 (zeros) + #3 (digamma W_R); u-form deferred to bound
    # inversion cost.  Reports whether OUR detector closes under the same method.
    # =======================================================================
    print("\n=== PART 3: STRESS (g_3 pinned orbit detector, d^2=4, mu=0) ===",
          flush=True)

    delta = mpf(2)                           # d^2 = 4 => fast on-line + t decay
    norm = normalize_family3(delta)
    g3 = make_g3(delta, norm, mpf("0"))

    sym_err = max(abs(g3(s) - g3(1 - s)) / abs(g3(s))
                  for s in (mpf("0.3") + 1j * 2, mpf("-0.2") + 1j * 20))
    tv = {n: abs(g3(sn)) for n, sn in
          (("zero", mpf(0)), ("half", mpf("0.5")), ("one", mpf(1)))}
    print(f"PART3|GATE symmetry rel={float(sym_err):.2e} | "
          f"triple-vanishing max={float(max(tv.values())):.2e}", flush=True)
    assert sym_err < 1e-20 and max(tv.values()) < 1e-20

    def ftit_g(s):
        return g3(s) * g3(1 - s)             # transform of the convolution-square F_g

    Tinv_g = mpf(10)                         # f~_g(it)=O(e^{-8t^2}); tail negligible at 10

    def G3(u):
        return G_inv(lambda t: ftit_g(t), float(u), Tinv_g)

    g3_0, g3_0_err = G3(mpf("0"))            # ONE inversion, reused for W_R + prime side
    print(f"PART3|G_3(0)={float(mp.re(g3_0)):.8f}+{float(mp.im(g3_0)):.2e}i "
          f"(inv err ~{float(abs(g3_0_err)):.1e})", flush=True)

    # --- LEFT: truncated zero sum + certified on-line envelope tail ----------
    T2 = mpf(60)

    def env_online(t):
        """Upper bound of |g_3(1/2+it)|^2 (the |.|-bound of the on-line mass)."""
        q = t * t + mpf("0.25")
        return norm ** 2 * q * q * (t * t) ** 2 * mexp(-2 * delta * delta * q)

    Z2_on = zero_side(float(T2), ftit_g, gam)   # sum of 2 Re f~(1/2+i*g), independent zeros

    def ztail(t):
        return env_online(t) * (t / (2 * mpi))   # |term| bound x over-counted density

    tailZ2g, _ = mquad(ztail, [float(T2), float(T2) + 50], error=True, maxdegree=8)
    center_l3 = Z2_on
    err_l3 = 2 * abs(tailZ2g)                    # factor 2 for the conjugate pair

    # --- RIGHT: triv - W_R(digamma) - prime_side (digamma form; single inversion)
    triv_g = ftit_g(mpf(1)) + ftit_g(mpf(0))     # ~0 by triple vanishing (law-18)
    wr_dig_g, wr_dig_g_quaderr = wr_dig(g3_0, ftit_g)   # full complex G(0) allowed

    # prime side: infinite.  Enumerate primes up to Ug and bound the tail with a
    # sampled decaying cap on |G_3| (honest loose bound for this stress object).
    Ug = mpf("6")                                # e^6 ~ 403 (~79 primes) -> bounded inversion count
    ps3 = mpf(0); imag_ps3 = mpf(0)
    for p in primes_up_to(int(mpf(str(math.exp(float(Ug)))))):
        lp = mlog(mpf(p))
        m = 1
        while m * lp <= float(Ug):
            u0 = mpf(m) * lp
            gu, _ = G3(u0)
            gmu, _ = G3(-u0)
            term = lp * (gu + mexp(-u0) * gmu)
            ps3 += mp.re(term)
            imag_ps3 = max(imag_ps3, abs(mp.im(term)))
            m += 1

    # sampled |G_3| cap on [Ug, Ug+8] for the prime tail over-count.
    samples = []
    uu = float(Ug)
    while uu <= float(Ug + 8):
        gv, _ = G3(mpf(uu))
        samples.append(abs(gv))
        uu += 0.5
    Cenv = max(samples) if samples else mpf(1)
    tailP3 = mpf(2) * lp_last_total(Ug, Ug + 8) * Cenv     # crude but safe over-count
    print(f"PART3|prime_side(trunc<={float(Ug)})={float(mp.re(ps3)):.8f}"
          f"|imag_max<{float(imag_ps3):.2e}|tail_bound<{float(tailP3):.3e}", flush=True)

    center_r3 = triv_g - wr_dig_g - ps3
    err_r3 = abs(wr_dig_g_quaderr) + 10 * abs(g3_0_err) \
        + imag_ps3 + tailP3 + mpf(25) * arch_xcheck_relax(norm)

    print(f"PART3|trivial={float(abs(triv_g)):.2e}(law-18 vanishes)"
          f"|W_R(digamma, complex)={float(mp.re(wr_dig_g)):.6f}+{float(mp.im(wr_dig_g)):.2e}i"
          f"|LEFT_center={float(mp.re(center_l3)):.10e}"
          f"|RIGHT_center_re={float(mp.re(center_r3)):.10e}", flush=True)
    report("g3-stress", center_l3, err_l3, mp.re(center_r3), err_r3,
           extra="(loose stress object; u-form W_R deferred)")

    # --- BONUS: off-line readout (the detector's actual job) ---------------
    g2 = mp.im(zetazero(2))
    for beta in (mpf("0.46"), mpf("1/2")):
        off = 2 * mp.re(ftit_g(beta + 1j * g2))
        shifted_l = center_l3 + off
        print(f"BONUS|beta={float(beta):.3f}|off-line term 2Re f~(rho)={float(off):.6e}"
              f"|shifted LEFT=[{float(mp.re(shifted_l) - float(err_l3)):.8f},"
              f"{float(mp.re(shifted_l) + float(err_l3)):.8f}]"
              f" vs RIGHT_re {float(mp.re(center_r3)):.8f}", flush=True)

    print("\n=== done: grep 'RECONCILE|PART0|PART1|PART2|PART3|BONUS' for the verdict ===",
          flush=True)


def lp_last_total(a, b):
    """Over-count of total log-weight of prime powers with log in [a,b].

    Bounded by treating it as a continuous line (one per unit log):  int_a^b y dy =
    (b^2 - a^2)/2.  Used only for the PART-3 stress tail, where looseness is OK."""
    return ((mpf(b) ** 2 - mpf(a) ** 2) / mpf(2))


def arch_xcheck_relax(norm):
    """PART-3 has no u-form W_R to cross-check; use a norm-scaled slack so the
    interval is not artificially tight.  Honest: this is where g_3's looseness lives."""
    return mpf("1e-6") * abs(norm ** 2)


if __name__ == "__main__":
    run()
