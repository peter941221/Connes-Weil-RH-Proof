#!/usr/bin/env python3
"""W0 appendix (map 011, track W): SELF-CHECK for record 1578 only.

STATUS 2026-09-17: SUPERSEDED AS AN AUTHORITY, RETAINED AS AN APPENDIX.
Record 1578 pins C' = log(pi) by a five-step hand derivation from committed
definitions, which needs no quadrature; and its section 2 shows that TEST C
below is INVALID for (OB): the committed window class
(C1MinimalWeilCriterion.lean:263-271) carries a second hypothesis,
laplaceAt g (1/2) = 0, i.e. g-hat(i/4pi) = 0, which this script's trial space
(all of PW_R) does not impose.  A positive value from TEST C is therefore a
supremum over a strict SUPERSET and refutes nothing - per law F28, its absurd
consequence (not-RH via the machine-checked gate) is evidence against the
scoping, not for a counterexample.  The Psi = 1 => M = I basis sentinel was
never run, which is a second reason not to quote its eigenvalues.

Owner rule on this wave (law F27): attack committed source directly; a rig runs
only where the definitions cannot decide, and never as authority for a claim a
hand proof already fixes.  This file's legitimate content is the two algebra
self-checks it caught (see 1578 section 6): the non-local counter-term tail
log coth(Y/2) of (D1), and the small-theta instability of the moment recursion.

PAPER / MODEL evidence only, under law 65: no Lean is built and no number below
is certified by Lean.  The script tries to REFUTE the symbolic claim

    C' = log(pi),   i.e.   Psi(xi) = log(pi) - Re psi(1/4 + i*pi*xi)

against the committed archimedean definitions, then (invalidly, see above)
prices the window supremum that (OB) asks about.

Committed source mirrored verbatim:

  Source/CCM25Concrete/SelectedWeilFormula.lean:96-109
    archimedeanNumerator   F y = e^(y/2) * (F y + F (-y)) - 2 * F 0
    archimedeanDenominator   y = e^y - e^(-y)                (= 2 sinh y)
    archimedeanIntegrand   F y = numerator / denominator
  Dev/C1SameOwnerWeil.lean:61-64
    archimedeanTerm F = ((log(4*pi) + gamma) * F 0 + int_{y>0} integrand).re
  Source/CCM25Concrete/CompactLogConvolution.lean:114-124
    convolutionSquare g = g.involution.convolution g ;  F(-x) = conj(F x)

Hence for F = g * g~ Hermitian with F(0) real,

  (D1)  A(g) = (log 4pi + gamma) F(0)
               + int_0^inf [ e^{y/2} Re F(y) - F(0) ] / sinh y dy

STRUCTURAL NOTE found while writing this script: even when supp g is compact, so
that Re F(y) vanishes for y > 2R, the COUNTER-TERM -F(0)/sinh y does NOT vanish;
its tail is the explicit constant

  int_Y^inf dy / sinh y = log coth(Y/2),

so the renormalisation is NON-LOCAL and truncating (D1) at y = 2R is wrong by
F(0) * log coth(R).  A first draft of this script made exactly that truncation
error; it was caught because the residual matched that closed form to every
printed digit (0.610649 vs R * log coth(R/2) = 0.610649).

Everything is pure mpmath: no sympy, no scipy, nothing installed.  For a
polynomial window g(x) = sum_k a_k (x/R)^k on [-R, R] both sides of the identity
are EXACT: the autocorrelation is a polynomial in y obtained from antiderivatives
(F_of_y), and the Fourier transform follows from the moment recursion
(ghat_of_xi), so the only numerical step left is a non-oscillatory quadrature of
a function decaying like xi^-6.

Fourier convention is Mathlib's exp(-2*pi*i*x*xi): F-hat = |g-hat|^2, Plancherel
unweighted, Re F(y) = int |g-hat(xi)|^2 cos(2*pi*y*xi) dxi.
"""

import mpmath as mp

mp.mp.dps = 50

LOG2 = mp.log(2)
R = LOG2 / 2                        # window half-width = log 2 / 2
GAMMA = mp.euler
HEAD = mp.log(4 * mp.pi) + GAMMA    # the "3.1083..." head coefficient
PI = mp.pi
C_CLAIM = mp.log(mp.pi)             # the claim under test:  C' = log pi


def re_psi_quarter(rt):
    """Re psi(1/4 + i rt/2), the r-variable core (r = 2 pi xi)."""
    return mp.re(mp.digamma(mp.mpf('0.25') + 1j * rt / 2))


def re_psi_xi(xi):
    """Re psi(1/4 + i pi xi), the same core in the Mathlib xi convention."""
    return mp.re(mp.digamma(mp.mpf('0.25') + 1j * PI * xi))


def Phi(r):
    """Pinned symbol, r variable: Phi(r) = C' - Re psi(1/4 + i r/2)."""
    return C_CLAIM - re_psi_quarter(r)


def Psi(xi):
    """Pinned symbol, xi variable."""
    return C_CLAIM - re_psi_xi(xi)


# ---------------------------------------------------------------------------
# exact building blocks for polynomial windows  g(x) = sum a_k (x/R)^k on [-R,R]
# ---------------------------------------------------------------------------
def F_of_y(aco, y):
    """Autocorrelation F(y) = int_{-R}^{R-y} g(t) g(t+y) dt, EXACT, 0 <= y <= 2R."""
    N = len(aco)
    tot = mp.mpf('0')
    for i in range(N):
        if aco[i] == 0:
            continue
        for j in range(N):
            if aco[j] == 0:
                continue
            c = aco[i] * aco[j] * R ** (-(i + j))
            inner = mp.mpf('0')
            for m in range(j + 1):
                p = i + m
                anti = lambda z: z ** (p + 1) / (p + 1)
                inner += mp.binomial(j, m) * y ** (j - m) \
                    * (anti(R - y) - anti(-R))
            tot += c * inner
    return tot


def N_moment(k, theta):
    """N_k(theta) = int_{-1}^{1} z^k e^{-i theta z} dz, exact to mp.dps.

    Small theta uses the Taylor series (the integration-by-parts recursion
    divides by theta k times and loses ~k*log10(theta) digits: a first draft
    used the recursion alone and produced |g-hat|^2 of order 1e217).
    Large theta uses the stable recursion from N_0, N_1.
    """
    ath = abs(theta)
    if ath < 30:
        tot = mp.mpc(0)
        pw = mp.mpc(1)
        fact = mp.mpf('1')
        tiny = mp.mpf('1e-%d' % (mp.mp.dps - 4))
        for m in range(0, 600):
            if m:
                pw *= -1j * theta
                fact *= m
            if (k + m) % 2:
                continue
            tot += pw / fact * 2 / (k + m + 1)
            if m > ath and abs(pw / fact) < tiny:
                break
        return tot
    N0 = 2 * mp.sin(theta) / theta
    if k == 0:
        return N0
    N1 = -2j * (mp.sin(theta) - theta * mp.cos(theta)) / theta ** 2
    if k == 1:
        return N1
    prev1 = N1
    for j in range(2, k + 1):
        cur = (mp.e ** (-1j * theta) - (-1) ** j * mp.e ** (1j * theta)) \
            / (-1j * theta) + (j / (1j * theta)) * prev1
        prev1 = cur
    return prev1


def ghat_of_xi(aco, xi):
    """int_{-R}^{R} g(x) e^{-2 pi i xi x} dx = R sum_k a_k N_k(2 pi xi R)."""
    theta = 2 * PI * xi * R
    return R * sum(mp.mpc(a) * N_moment(k, theta)
                   for k, a in enumerate(aco) if a != 0)


def norm_spatial(aco):
    """||g||^2 = F(0), exact."""
    return F_of_y(aco, mp.mpf('0'))


def norm_planche(aco):
    """int |g-hat|^2 dxi, numeric (Plancherel cross-check)."""
    return mp.quad(lambda xi: mp.re(ghat_of_xi(aco, xi)
                                    * mp.conj(ghat_of_xi(aco, xi))),
                   [-mp.inf, -40, -10, -2, -0.5, 0, 0.5, 2, 10, 40, mp.inf])


# ---------------------------------------------------------------------------
# the two sides of the claim
# ---------------------------------------------------------------------------
def counter_tail(F0, Y):
    """-F0 * int_Y^inf dy/sinh y = -F0 * log coth(Y/2): the non-local tail."""
    return -F0 * mp.log(1 / mp.tanh(Y / 2))


def A_spatial(aco):
    """(D1), the committed archimedean form, spatial / autocorrelation side."""
    F0 = norm_spatial(aco)
    bulk = mp.quad(lambda y: (mp.e ** (y / 2) * F_of_y(aco, y) - F0)
                   / mp.sinh(y), [0, 2 * R])
    return HEAD * F0 + bulk + counter_tail(F0, 2 * R)


def A_spectral(aco, with_C=C_CLAIM):
    """int |g-hat|^2 * (with_C - Re psi(1/4 + i pi xi)) dxi."""
    def integrand(xi):
        h = ghat_of_xi(aco, xi)
        return mp.re(h * mp.conj(h)) * (with_C - re_psi_xi(xi))
    return 2 * mp.quad(integrand, [0, 0.5, 2, 10, 40, mp.inf])


def sentinel(aco, label):
    LHS = A_spatial(aco)
    RHS = A_spectral(aco)
    core = A_spectral(aco, with_C=mp.mpf('0'))
    F0 = norm_spatial(aco)
    C_emp = (LHS - core) / F0
    print('\n--- %s ---' % label)
    print('  ||g||^2  spatial   =', mp.nstr(F0, 24))
    print('  ||g||^2  Plancherel=', mp.nstr(norm_planche(aco), 24))
    print('  A_spatial   (D1)   =', mp.nstr(LHS, 24))
    print('  A_spectral  (logpi)=', mp.nstr(RHS, 24))
    print('  |difference|       =', mp.nstr(abs(LHS - RHS), 6))
    print("  empirical C'       =", mp.nstr(C_emp, 24))
    print('  log pi             =', mp.nstr(C_CLAIM, 24))
    print('  |C_emp - log pi|   =', mp.nstr(abs(C_emp - C_CLAIM), 6))
    return abs(LHS - RHS), abs(C_emp - C_CLAIM)


# ---------------------------------------------------------------------------
# TEST B -- the sign change r_0 of Phi, which law F18 deferred until C' was
# pinned.  Gauss's value psi(1/4) = -gamma - pi/2 - 3 log 2 gives Phi(0).
# ---------------------------------------------------------------------------
def test_B():
    Phi0 = Phi(0)
    Phi0_closed = mp.log(mp.pi) + GAMMA + PI / 2 + 3 * LOG2
    r0 = mp.findroot(Phi, mp.mpf('3'))
    return Phi0, Phi0_closed, r0, r0 / (2 * PI)


# ---------------------------------------------------------------------------
# TEST C -- Galerkin LOWER bound for the window supremum (sup-law: a
# finite-subspace maximum is <= the true sup, so a positive value falsifies
# (OB); a negative one proves nothing -- 1417 s3b, 1418 s5).
#
#   basis of L2(-R,R): phi_n(x) = sqrt((2n+1)/(2R)) P_n(x/R)
#   phi_n^(xi) = sqrt(2R(2n+1)) (-i)^n j_n(2 pi R xi),  j_n = sqrt(pi/2u) J_{n+1/2}
# ---------------------------------------------------------------------------
def legendre_aco(n):
    """Coefficients a_k of phi_n(x) = sqrt((2n+1)/(2R)) P_n(x/R) in (x/R)^k.

    P_n(x) = sum_j (-1)^j (2n-2j)! / (2^n j! (n-j)! (n-2j)!) x^{n-2j}.
    A first draft dropped the 2^-n and factorial normalisation, which silently
    destroyed orthonormality and inflated the TEST C eigenvalue; the two
    sentinels below (spatial inner products, and M = I for Psi = 1) are there to
    catch that class of error.
    """
    c = mp.sqrt((2 * n + 1) / (2 * R))
    aco = [mp.mpf('0')] * (n + 1)
    for j in range(n // 2 + 1):
        k = n - 2 * j
        coef = (-1) ** j * mp.factorial(2 * n - 2 * j) / \
            (2 ** n * mp.factorial(j) * mp.factorial(n - j)
             * mp.factorial(n - 2 * j))
        aco[k] = c * coef
    return aco


def inner_poly(aco, bco):
    """int_{-R}^{R} (sum a_k (x/R)^k)(sum b_l (x/R)^l) dx, exact."""
    tot = mp.mpf('0')
    for k, a in enumerate(aco):
        if a == 0:
            continue
        for l, b in enumerate(bco):
            if b == 0:
                continue
            if (k + l) % 2:
                continue
            tot += a * b * 2 * R / (k + l + 1)
    return tot


def sph_jn(n, u):
    if u == 0:
        return mp.mpf('1') if n == 0 else mp.mpf('0')
    return mp.sqrt(PI / (2 * u)) * mp.besselj(n + mp.mpf('0.5'), u)


def spectral_matrix(N, sym=None):
    """M_mn = int conj(phi_m^) phi_n^ sym dxi; zero unless m+n is even.

    Passing sym = const 1 must return the IDENTITY -- that is the unit sentinel
    that validates the basis normalisation and the Bessel amplitudes together.
    """
    s = sym if sym is not None else Psi
    M = [[mp.mpf('0')] * N for _ in range(N)]
    for m in range(N):
        for n in range(N):
            if (m + n) % 2:
                continue
            amp = mp.sqrt(2 * R * (2 * m + 1) * (2 * n + 1))
            sgn = -1 if ((m + n) // 2) % 2 else 1

            def integrand(xi, m=m, n=n):
                u = 2 * PI * R * xi
                return amp * sgn * sph_jn(m, u) * sph_jn(n, u) * s(xi)
            M[m][n] = 2 * mp.quad(integrand, [0, 1, 5, 20, 60, mp.inf])
    return M


def jacobi_max(M, sweeps=80):
    """Largest eigenvalue + vector of a small real symmetric mp matrix,
    by cyclic Jacobi rotations carried at mp precision."""
    N = len(M)
    A = [[M[i][j] for j in range(N)] for i in range(N)]
    V = [[mp.mpf('1') if i == j else mp.mpf('0') for j in range(N)]
         for i in range(N)]
    for _ in range(sweeps):
        off = max((abs(A[p][q]) for p in range(N) for q in range(p + 1, N)),
                  default=mp.mpf('0'))
        if off < mp.mpf('1e-30'):
            break
        for p in range(N):
            for q in range(p + 1, N):
                if A[p][q] == 0:
                    continue
                theta = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = 1 / (abs(theta) + mp.sqrt(1 + theta ** 2))
                if theta < 0:
                    t = -t
                c = 1 / mp.sqrt(1 + t * t)
                s = t * c
                for k in range(N):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p], A[k][q] = c * akp - s * akq, s * akp + c * akq
                for k in range(N):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k], A[q][k] = c * apk - s * aqk, s * apk + c * aqk
                for k in range(N):
                    vkp, vkq = V[k][p], V[k][q]
                    V[k][p], V[k][q] = c * vkp - s * vkq, s * vkp + c * vkq
    d = [A[i][i] for i in range(N)]
    im = max(range(N), key=lambda i: d[i])
    return d[im], [V[i][im] for i in range(N)], min(d)


def main():
    print('=' * 78)
    print("W0  window symbol / pinned constant C' / form domain / sup pricing")
    print('  R = log2/2 =', mp.nstr(R, 16),
          '   HEAD = log(4pi)+gamma =', mp.nstr(HEAD, 18))
    print('=' * 78)

    print('\n### PRIMARY sentinels: exact F, exact g-hat, xi^-6 decay ###')
    devs_id, devs_c = [], []
    cases = [
        ([1, 0, -1], 'S1  g = 1 - (x/R)^2'),
        ([1, 0, -2, 0, 1], 'S2  g = (1 - (x/R)^2)^2'),
        ([1, mp.mpf('1') / 3, -1], 'S3  g = 1 + (x/R)/3 - (x/R)^2  (asymmetric)'),
        ([mp.mpf('1') / 2, -mp.mpf('7') / 10, mp.mpf('1') / 5,
          mp.mpf('3') / 10, -mp.mpf('1') / 4],
         'S4  g = generic quartic'),
    ]
    for aco, label in cases:
        d1, d2 = sentinel([mp.mpf(x) for x in aco], label)
        devs_id.append(d1)
        devs_c.append(d2)

    print('\n  worst |A_spatial - A_spectral| over 4 windows =',
          mp.nstr(max(devs_id), 5))
    print("  worst |C_emp - log pi|     over 4 windows =",
          mp.nstr(max(devs_c), 5))

    print('\n--- TEST B  the pinned symbol, its maximum, its sign change ---')
    Phi0, Phi0c, r0, xi0 = test_B()
    print('  Phi(0) numeric                  =', mp.nstr(Phi0, 24))
    print('  Phi(0) = logpi+gam+pi/2+3log2   =', mp.nstr(Phi0c, 24))
    print('  |Phi0 - closed form|            =', mp.nstr(abs(Phi0 - Phi0c), 5))
    print('  r_0 (first zero of Phi)         =', mp.nstr(r0, 24))
    print('  r_0 / (2 pi)                    =', mp.nstr(r0 / (2 * PI), 16))
    print('  xi_0 = r_0/2pi                  =', mp.nstr(xi0, 24))
    print('  Phi(r_0) residual               =', mp.nstr(Phi(r0), 5))
    print('  1/(2R) = 1/log2 (uncertainty width) =', mp.nstr(1 / (2 * R), 16))

    print('\n--- VALIDATION of the Galerkin basis (guards the previous bug) ---')
    NB = 6
    basis = [legendre_aco(n) for n in range(NB)]
    ortho = max(abs(inner_poly(basis[m], basis[n])
                    - (mp.mpf('1') if m == n else mp.mpf('0')))
                for m in range(NB) for n in range(NB))
    print('  spatial:  max |<phi_m,phi_n> - delta_mn|      =', mp.nstr(ortho, 5))
    plan = max(abs(norm_planche(basis[n]) - 1) for n in range(4))
    print('  plancherel: max |int|phi_n^|^2 - 1|           =', mp.nstr(plan, 5))
    MINUS = spectral_matrix(4, sym=lambda xi: mp.mpf('1'))
    unit = max(abs(MINUS[m][n] - (mp.mpf('1') if m == n else mp.mpf('0')))
               for m in range(4) for n in range(4))
    print('  matrix with Psi = 1 is the identity: max dev  =', mp.nstr(unit, 5))
    basis_ok = ortho < mp.mpf('1e-20') and plan < mp.mpf('1e-12') \
        and unit < mp.mpf('1e-12')
    print('  BASIS VALIDATED                               :',
          'PASS' if basis_ok else 'FAIL -- TEST C numbers are meaningless')

    print('\n--- TEST C  window sup: Galerkin LOWER bound, N = 4..10 ---')
    print('  (positive => (OB) falsified by a concrete g; negative => no claim)')
    best = None
    for N in (4, 6, 8, 10):
        M = spectral_matrix(N)
        top, vec, bot = jacobi_max(M)
        print('  N=%2d   top = %+.12f    min = %+.6f' % (N, top, bot))
        if best is None or top > best[0]:
            best = (top, vec, N)
    top, vec, N = best
    print('  best lower bound = %+.12f at N = %d' % (top, N))
    print('  multiplier upper bound Phi(0) = %+.12f (no support constraint)' % Phi0)

    print('\n--- TEST D  cross-check the maximizing direction two ways ---')
    # path 2 is the eigenvalue itself; path 1 rebuilds g in the Legendre basis
    # and runs the SPATIAL form, so a convention error cannot pass silently.
    nrm2 = sum(c * c for c in vec)
    # path 1: rebuild g in the Legendre basis, then run the SPATIAL form
    aco_s = [mp.mpf('0')] * N
    for n in range(N):
        a = legendre_aco(n)
        for k in range(len(a)):
            aco_s[k] = aco_s[k] + vec[n] * a[k]
    print('  ||g||^2 from coefficients (should be 1) =', mp.nstr(nrm2, 16))
    sp_val = A_spatial(aco_s) / nrm2
    print('  A(g) path 1 (spatial (D1), exact F)     =', mp.nstr(sp_val, 16))
    print('  A(g) path 2 (spectral matrix eigenvalue) =', mp.nstr(top, 16))
    print('  |difference|                            =',
          mp.nstr(abs(sp_val - top), 6))

    print('\n' + '=' * 78)
    print('SENTINELS  (law 65: MODEL evidence, not Lean-certified)')
    print('=' * 78)
    ok_id = max(devs_id) < mp.mpf('1e-25')
    ok_c = max(devs_c) < mp.mpf('1e-25')
    print("  A_spatial == A_spectral on all windows :", 'PASS' if ok_id else 'FAIL')
    print("  C' == log pi on all windows            :", 'PASS' if ok_c else 'FAIL')
    print('  window sup best LOWER bound            : %+.12f -> %s'
          % (top, 'INVALID FOR (OB): trial space omits hvanishes (see 1578 s2)'))
    print('  named constants: HEAD =', mp.nstr(HEAD, 18),
          ' Phi(0) =', mp.nstr(Phi0, 18), ' r_0 =', mp.nstr(r0, 18))
    print('=' * 78)


if __name__ == '__main__':
    main()
