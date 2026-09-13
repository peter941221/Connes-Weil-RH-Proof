# 1396: verified rational enclosure of the 1394 section 4 witness cell of (J1).
#
# Goal: a machine-checked certificate in EXACT arithmetic that the locked
# witness cell satisfies the strict inequality (J1):
#
#     ceiling  <=  C_UP   <   (1/100) / (2 * D_HI)  <=  delta / (2 * C_min)
#
# where C_UP and D_HI are dyadic rationals printed by the script and the
# middle strict inequality is verified over Python Fractions -- there is no
# floating point at the comparison layer.  Validity chain:
#
#   1. every datum of the cell is an exact rational: d = 1/200,
#      delta = 1/100, Rf = Ru = 1/50, eps = eps' = 1/100,
#      rho = 99/100 + 1054*I;
#   2. transcendental functions (sinh, cosh, cos, sin, exp, pi) are applied
#      ONLY to exact rationals, evaluated with mpmath at dps = 100 and padded
#      by +-1e-80, far above mpmath's guard-digit error; a padded value is an
#      exact rational interval;
#   3. everything after that (4x4 Gram determinant, 3x3 cofactor Leibniz
#      expansion, complex products, one division by the determinant) runs
#      through real/complex interval layers over Fractions whose outward
#      rounding is exact by construction (min/max of exact endpoint products);
#   4. ceiling is increasing in K_loc_f and K_loc_u, and delta/(2 C_min) is
#      decreasing in C_min = min(C_C, C_D); so UPPER edges of K and of C_C,
#      C_D give valid ceiling_up and rhs_lo (the assertion that the K
#      imaginary enclosures are tiny is itself a G3-style instrument check).
#
# mpmath's iv layer is deliberately NOT used: it has no complex-interval
# support, iv.conj does not exist, and `x + 1j * y` on ivmpf coerces through
# float, silently destroying enclosure.
#
# Certificate, not a rig: no grid, no bands, no re-chosen cell -- parameters
# are VERBATIM the cell committed in 1394 section 4 under prereg 1393
# section 2 (law 42: prereg -> digit -> this check).  All numbers are MODEL
# (law 65): a budget-arithmetic statement on the route-alpha register, not a
# Lean term and not an RH inference.

import math
import sys
from fractions import Fraction as Fr
from itertools import permutations

import mpmath as mp

mp.mp.dps = 100
PAD = Fr(1, 10) ** 80  # +-1e-80 pad for every transcendental value

# ---------------------------------------------------------------- exact atoms


def fmpq(q):
    """exact Fraction -> mpmath mpf, no decimal round trip."""
    return mp.mpf(q.numerator) / q.denominator


def fr(z):
    """mpmath mpf -> exact Fraction from its internal (sign, man, exp, bc).

    Fraction(mpf) is a TypeError (mpf is not a numbers.Rational), and
    Fr(str(mpf)) could round INWARD and break outward enclosure; the _mpf_
    tuple IS the exact binary float: value = sign * man * 2**exp.
    """
    sign, man, e, _bc = z._mpf_
    q = Fr(man << e) if e >= 0 else Fr(man, 1 << -e)
    return -q if sign else q


def rp(q, pad=Fr(0)):
    """real point interval with symmetric pad."""
    return (q - pad, q + pad)


R01 = (Fr(0), Fr(0))  # exact real zero as a padded-free point


def ci(re, im=R01):
    """complex interval from two real intervals."""
    return (re, im)


def cip(re, im=Fr(0), pad=Fr(0)):
    return ci(rp(re, pad), rp(im, pad))


# ------------------------------------------------------- real interval layer


def r_add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def r_sub(x, y):
    return (x[0] - y[1], x[1] - y[0])


def r_mul(x, y):
    v = [x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1]]
    return (min(v), max(v))


def r_div(x, y):
    yl, yh = y
    assert yl > 0 or yh < 0, "real division through a zero-containing interval"
    inv = (Fr(1) / yh, Fr(1) / yl)
    return r_mul(x, inv)


# ---------------------------------------------------- complex interval layer


def c_add(x, y):
    return (r_add(x[0], y[0]), r_add(x[1], y[1]))


def c_neg(x):
    return r_sub(R01, x[0]), r_sub(R01, x[1])


def c_mul(x, y):
    re = r_sub(r_mul(x[0], y[0]), r_mul(x[1], y[1]))
    im = r_add(r_mul(x[0], y[1]), r_mul(x[1], y[0]))
    return (re, im)


def c_conj(x):
    return (x[0], c_neg(x)[1])


def c_scale_real(a, x):  # a: real interval
    return (r_mul(a, x[0]), r_mul(a, x[1]))


def c_div(x, y):
    # x/y = x * conj(y) / |y|^2, with 1/|y|^2 an interval (|y|^2 asserted > 0)
    nrm2 = r_add(r_mul(y[0], y[0]), r_mul(y[1], y[1]))
    assert nrm2[0] > 0, "complex division through a zero-containing norm"
    return c_mul(c_mul(x, c_conj(y)), ci(r_div((Fr(1), Fr(1)), nrm2), R01))


# ------------------------------------------------- transcendental atoms (rational input only)


def t_sinh(x):
    return rp(fr(mp.sinh(fmpq(x))), PAD)


def t_cosh(x):
    return rp(fr(mp.cosh(fmpq(x))), PAD)


def t_cos(x):
    return rp(fr(mp.cos(fmpq(x))), PAD)


def t_sin(x):
    return rp(fr(mp.sin(fmpq(x))), PAD)


def t_exp(x):
    return rp(fr(mp.exp(fmpq(x))), PAD)


T_PI = rp(fr(mp.pi), PAD)


def sinh_complex(re, im):
    """sinh(re + i im) for exact rationals re, im."""
    return ci(r_mul(t_sinh(re), t_cos(im)), r_mul(t_cosh(re), t_sin(im)))


# ------------------------------------------------------------- determinant


def det(mat):
    """Leibniz determinant; mat: list of lists of CI."""
    n = len(mat)
    total = None
    for perm in permutations(range(n)):
        inv = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        term = mat[0][perm[0]]
        for row in range(1, n):
            term = c_mul(term, mat[row][perm[row]])
        if inv % 2:
            term = c_neg(term)
        total = term if total is None else c_add(total, term)
    return total


# ------------------------------------------------------------ locked cell

DELTA = Fr(1, 100)
DD = Fr(5, 1000)
RAD = Fr(2, 100)  # Rf = Ru = 1/50
EPS = Fr(1, 100)
NODES = [(Fr(0), Fr(0)), (Fr(1, 2), Fr(0)), (Fr(1), Fr(0)), (Fr(99, 100), Fr(1054))]
V_ONES = [Fr(1)] * 4
Y_CONC = [Fr(0), Fr(0), Fr(0), Fr(-1)]


def gram(Rq):
    """G_ij = 2 sinh(A_ij R)/A_ij, A = s_i + conj s_j; A = 0 branch -> 2R."""
    n = len(NODES)
    G = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            a_re = NODES[i][0] + NODES[j][0]
            a_im = NODES[i][1] - NODES[j][1]
            if a_re == 0 and a_im == 0:
                G[i][j] = cip(2 * Rq)  # exact rational entry
            else:
                num = c_scale_real(rp(Fr(2)), sinh_complex(a_re * Rq, a_im * Rq))
                G[i][j] = c_div(num, cip(a_re, a_im))
    return G


def kloc(Rq, pattern):
    """K = z* G^-1 z by Cramer over CI. Returns (K interval, det interval)."""
    n = len(NODES)
    G = gram(Rq)
    dv = det(G)
    acc = None
    for i in range(n):
        for j in range(n):
            minor = [[G[r][c] for c in range(n) if c != j] for r in range(n) if r != i]
            cof = det(minor)
            if (i + j) % 2:
                cof = c_neg(cof)
            # pattern entries are real rationals: conj is identity
            term = c_mul(cip(pattern[i]), c_mul(cof, cip(pattern[j])))
            acc = term if acc is None else c_add(acc, term)
    return c_div(acc, dv), dv


def real_enclosure(kci, label):
    """Upper bound of a model-real quantity: re.hi + |im| enclosure."""
    (rl, rh), (il, ih) = kci
    assert ih - il < Fr(1, 10) ** 40, f"{label}: interval solve blew up"
    assert max(abs(il), abs(ih)) < Fr(1, 10) ** 40, f"{label}: imaginary part wide"
    return rh + max(abs(il), abs(ih))


def main():
    Kf, detf = kloc(RAD, Y_CONC)
    Ku, detu = kloc(RAD, V_ONES)
    Kf_hi = real_enclosure(Kf, "K_loc_f")
    Ku_hi = real_enclosure(Ku, "K_loc_u")

    ceil_hi = 2 * RAD * (1 + EPS) * Ku_hi * (1 + EPS) * Kf_hi  # all Fr, exact

    Rg = RAD + RAD
    dRg = DD * Rg
    CC1 = r_mul(r_mul(T_PI, rp(Fr(8))), r_mul(t_sinh(dRg), t_sinh(dRg)))
    CC2 = r_mul(rp(2 * DELTA ** 3 * Rg ** 3), t_exp(2 * dRg))
    C_C_hi = r_add(CC1, CC2)[1]
    em1 = r_sub(t_exp(dRg), (Fr(1), Fr(1)))
    CD1 = r_mul(rp(2 * Rg * DELTA), r_mul(em1, em1))
    CD2 = rp(Fr(4, 3) * DELTA ** 3 * Rg ** 3)
    C_D_hi = r_add(CD1, CD2)[1]
    D_HI = min(C_C_hi, C_D_hi)
    rhs_lo = (DELTA / 2) / D_HI  # Fraction arithmetic: D_HI >= C_min -> valid lo
    ok = ceil_hi < rhs_lo

    K = 60
    C_UP = Fr(math.ceil(ceil_hi * 2 ** K), 2 ** K)
    D_HIq = Fr(math.ceil(D_HI * 2 ** K), 2 ** K)
    rhs_exact = (DELTA / 2) / D_HIq
    exact_ok = C_UP < rhs_exact

    print("cell: d=1/200 delta=1/100 Rf=Ru=1/50 eps=eps'=1/100 rho=99/100+1054i")
    print("K_loc_f enclosure widths  re/im:",
          float(Kf[0][1] - Kf[0][0]), float(Kf[1][1] - Kf[1][0]))
    print("K_loc_u enclosure widths  re/im:",
          float(Ku[0][1] - Ku[0][0]), float(Ku[1][1] - Ku[1][0]))
    print("det enclosure widths      re/im:",
          float(detf[0][1] - detf[0][0]), float(detu[0][1] - detu[0][0]))
    # NOTE (7i landmine, hit for real here): the PAD=1e-80 interval fractions
    # have numerator digit counts far above CPython's 4300-digit int->str
    # guard; intermediate exact values are RENDERED as float (correctly
    # rounded from the Fraction) and only the FINAL dyadic pair, whose ints
    # are ~20 digits, is printed exactly.
    print("ceiling upper (exact Fr, rendered)   :", float(ceil_hi))
    print("C_C upper (exact Fr, rendered)       :", float(C_C_hi))
    print("C_D upper (exact Fr, rendered)       :", float(C_D_hi))
    print("D_HI = min upper (exact Fr, rendered):", float(D_HI))
    print("delta/(2 D_HI) lower  (rendered)     :", float(rhs_lo))
    print("interval-layer strict separation:", "PASS" if ok else "FAIL")
    print("C_UP  = %d / 2^%d" % (C_UP.numerator, K))
    print("D_HIq = %d / 2^%d" % (D_HIq.numerator, K))
    print("delta/(2 D_HIq) exact     :", rhs_exact.numerator, "/", rhs_exact.denominator)
    print("EXACT-RATIONAL strict check C_UP < delta/(2*D_HIq):",
          "PASS" if exact_ok else "FAIL")
    verdict = ok and exact_ok
    print("CERT DONE" if verdict else "CERT FAILED")
    return 0 if verdict else 1


if __name__ == "__main__":
    sys.exit(main())
