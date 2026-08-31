# 1070 ANCHOR DEBUG - which side of the explicit-formula identity is broken?
#
# Identity under test (CC20 tex:2039 bombieriexplicit, = Bombieri [EB] eq. p.186):
#   sum_rho f~(rho) = f~(1) + f~(0) - W_R(f) - sum_p W_p(f)
# Test: G = 6-fold cardinal B-spline (C_c, support [-3,3] in u), f(x) = G(log x),
#       f~(s) = (sinh(s/2)/(s/2))^6.
#
# Three independent evaluations of sum_v W_v = W_R + W_p:
#   (i)  u-quadrature of tex:2047 bombieriexplicit2   [wr_u + prime_ff]
#   (ii) f~-form tex:2049 bombieriexplicit3           [wr3 + prime_ff]
#   (iii) contour route from Bombieri (2.2)+(2.3):
#            I  = -1/2 log(pi) f(1) + (1/4 pi i) int_(2) psi(w/2) f~ dw - sum L(n) f(n)
#            Lc = (1/2 pi i) int_(-1) Z'/Z f~ dw
#            sum_v W_v = Lc - I
# Target: sum_v W_v = f~(1) + f~(0) - sum_rho f~(rho) ~ 2.562788.

import numpy as np  # noqa: F401  (kept for parity with the main probe)
from mpmath import mp, mpf, exp as mexp, pi as mpi, log as mlog, sinh as msinh, \
    zetazero, quad as mquad, digamma, zeta as mzeta

mp.dps = 30

EULER = mpf("0.57721566490153286060651209008240243104215933593992")


def bspline6(u):
    u = mpf(repr(u)) if isinstance(u, float) else u
    x = u + 3
    if x < 0 or x > 6:
        return mpf(0)
    s = mpf(0)
    for k in range(0, int(mp.floor(x)) + 1):
        s += (-1) ** k * mp.binomial(6, k) * (x - k) ** 5
    return s / mp.factorial(5)


def ftil(s):
    if abs(s) < mpf("1e-20"):
        return mpf(1)
    return (msinh(s / 2) / (s / 2)) ** 6


def Gof(x):
    return bspline6(mlog(x))


def run():
    G0 = bspline6(mpf(0))

    print("=== 0. ftil closed form vs direct Mellin quadrature ===", flush=True)
    for re0, im0 in ((1.0, 0.0), (0.5, 14.1347251), (2.0, 3.0), (-1.0, 5.0)):
        s = mpf(re0) + 1j * mpf(im0)
        val = mquad(lambda x: Gof(x) * x ** (s - 1),
                    [mexp(-3), mpf("0.3"), 1, 3, mexp(3)])
        print(f"ftil|s={re0}{im0:+.4f}j|closed={float(mp.re(ftil(s))):.12f}"
              f"|mellin={float(mp.re(val)):.12f}|diff={float(abs(val - ftil(s))):.2e}",
              flush=True)

    print("\n=== 1. zero side (zetazero sum, gamma <= 100) ===", flush=True)
    zero = mpf(0)
    j = 0
    while True:
        j += 1
        g = mp.im(zetazero(j))
        if g > 100:
            break
        zero += 2 * mp.re(ftil(mpf(1) / 2 + 1j * g))
    print(f"zero={float(zero):.12e}  (j ran to {j - 1})", flush=True)

    print("\n=== 2. prime sides ===", flush=True)
    prime_ff = mpf(0)          # sum_p log p sum_m (f + f*)   [CC20 W_p]
    for p0 in (2, 3, 5, 7, 11, 13, 17, 19):
        lp = mlog(mpf(p0))
        m0, pterm = 1, mpf(0)
        while m0 * lp < 3:
            u0 = m0 * lp
            pterm += lp * (bspline6(u0) + mexp(-u0) * bspline6(-u0))
            m0 += 1
        print(f"W_p|p={p0}|term={float(pterm):.12f}", flush=True)
        prime_ff += pterm
    lam_f = mpf(0)             # sum_n Lambda(n) f(n)          [Bombieri (2.2)]
    for p0 in (2, 3, 5, 7, 11, 13, 17, 19):
        p0m = 1
        while p0m <= 20:
            lam_f += mlog(mpf(p0)) * Gof(mpf(p0m))
            p0m *= p0
    print(f"prime_ff={float(prime_ff):.12f}|lam_f={float(lam_f):.12f}", flush=True)

    print("\n=== 3. W_R: u-quadrature vs f~-form ===", flush=True)

    def integ_u(u):
        return (bspline6(u) + mexp(-u) * bspline6(-u) - 2 * mexp(-u) * G0) \
            / (1 - mexp(-2 * u))

    wr_u = (mlog(4 * mpi) + EULER) * G0 + \
        mquad(integ_u, [mpf("1e-12"), mpf("0.25"), mpf("0.5"), 1, 2, 3, 40])

    def integ3(t):
        w = mpf(1) / 2 + 1j * t
        return mp.re(digamma(w / 2)) * ftil(w)

    i3 = 2 * mp.re(mquad(integ3, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32, 64, 128]))
    wr3 = mlog(mpi) * G0 - i3 / (2 * mpi)
    print(f"wr_u(u-quad)={float(wr_u):.12f}", flush=True)
    print(f"wr3(f-form) ={float(wr3):.12f}   [log(pi) f(1) = "
          f"{float(mlog(mpi) * G0):.6f}]", flush=True)

    print("\n=== 4. contour route: Lc, A, I, sum_v W_v (3 candidates) ===",
          flush=True)

    def zlr(w):
        return -mlog(mpi) / 2 + digamma(w / 2) / 2 + mzeta(w, 1) / mzeta(w)

    def integL(t):
        w = -1 + 1j * t
        return zlr(w) * ftil(w)

    Lc = 2 * mp.re(mquad(integL, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32])) / (2 * mpi)

    def integA(t):
        w = 2 + 1j * t
        return digamma(w / 2) * ftil(w)

    A = 2 * mp.re(mquad(integA, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32])) / (4 * mpi)
    I_rhs = -mlog(mpi) / 2 * G0 + A - lam_f
    print(f"Lc={float(Lc):.12f}|A={float(A):.12f}|I_rhs={float(I_rhs):.12f}",
          flush=True)

    # attribution of the contour-side mismatch: direct I(c=2) quadrature vs
    # the (2.2) assembly, and Lc line-independence (c' in (-2, 0))
    def integI2(t):
        w = 2 + 1j * t
        return zlr(w) * ftil(w)

    I2 = 2 * mp.re(mquad(integI2, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32])) \
        / (2 * mpi)

    def integL05(t):
        w = mpf("-0.5") + 1j * t
        return zlr(w) * ftil(w)

    Lc05 = 2 * mp.re(mquad(integL05, [0, mpf("0.5"), 1, 2, 4, 8, 16, 32])) \
        / (2 * mpi)
    print(f"I2(direct c=2)={float(I2):.12f}  [vs I_rhs {float(I_rhs):.6f},"
          f" I_lhs(c' route) {float(-ftil(mpf(0)) - ftil(mpf(1)) + zero + Lc):.6f}]",
          flush=True)
    print(f"Lc(c'=-0.5)={float(Lc05):.12f}  [vs Lc(c'=-1) {float(Lc):.12f}]",
          flush=True)

    sumv_target = ftil(mpf(1)) + ftil(mpf(0)) - zero
    sumv_uform = wr_u + prime_ff
    sumv_fform = wr3 + prime_ff
    sumv_contour = Lc - I_rhs
    print(f"sum_v W_v target  = {float(sumv_target):.12f}", flush=True)
    print(f"sum_v W_v u-form  = {float(sumv_uform):.12f}", flush=True)
    print(f"sum_v W_v f-form  = {float(sumv_fform):.12f}", flush=True)
    print(f"sum_v W_v contour = {float(sumv_contour):.12f}", flush=True)
    zero_contour = I_rhs + ftil(mpf(0)) + ftil(mpf(1)) - Lc
    print(f"zero_via_contour  = {float(zero_contour):.12e}  "
          f"(vs zetazero {float(zero):.6e})", flush=True)
    print("\nDEBUG DONE", flush=True)


if __name__ == "__main__":
    run()
