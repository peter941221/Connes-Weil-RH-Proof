#!/usr/bin/env python3
"""Rigorous rational-interval certificates for finite Hermitian forms.

ENGINE ONLY (2026-08-27): no entry formula of any published Yoshida matrix is
encoded here — the primary text is access-restricted; see README.md for the
checked provenance. Every value node carries a mandatory `source` string so
the encoder cannot silently invent an input.

All arithmetic is exact `fractions.Fraction` interval arithmetic. Directed
rounding is trivially correct because endpoints are rationals.

Public surface
--------------
* Interval            -- closed [lo, hi] with lo, hi Fractions.
* const_interval(q)   -- point interval.
* add / scale / mul / join -- exact interval algebra.
* psi_bracket(x)      -- rigorous bracket of the digamma at rational x > 0.
* elementary_bracket(kind, theta_iv)
                      -- rigorous sin/cos/sinh/cosh brackets on an INTERVAL
                         argument; series + Lagrange remainder only, NO
                         stored digits anywhere.
* ldlt_positive_definite(A) -- exact symmetric positive-definite check and
  factor readback (mirrors Dev/C1YoshidaLdlCertificate.lean).
* emit_interval_line / emit_ldlt_witness -- Lean-ready transcription snippets.
"""

from __future__ import annotations

from fractions import Fraction as F


# --------------------------------------------------------------------------
# Interval algebra (exact)
# --------------------------------------------------------------------------


class Interval:
    """Closed real interval [lo, hi] with exact Fraction endpoints."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo: F, hi: F):
        if not isinstance(lo, F) or not isinstance(hi, F):
            raise TypeError("Interval endpoints must be exact Fractions")
        if lo > hi:
            raise ValueError(f"empty interval [{lo}, {hi}]")
        self.lo = lo
        self.hi = hi

    def __repr__(self) -> str:
        return f"Interval[{self.lo}, {self.hi}]"

    def contains(self, other: "Interval") -> bool:
        return self.lo <= other.lo and other.hi <= self.hi

    def width(self) -> F:
        return self.hi - self.lo

    def __eq__(self, other: object) -> bool:
        # Value equality on endpoints; hashability is not needed anywhere.
        if not isinstance(other, Interval):
            return NotImplemented
        return self.lo == other.lo and self.hi == other.hi


def const_interval(q: F) -> Interval:
    return Interval(q, q)


def add(a: Interval, b: Interval) -> Interval:
    return Interval(a.lo + b.lo, a.hi + b.hi)


def scale(c: F, a: Interval) -> Interval:
    lo, hi = c * a.lo, c * a.hi
    return Interval(min(lo, hi), max(lo, hi))


def mul(a: Interval, b: Interval) -> Interval:
    products = (a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi)
    return Interval(min(products), max(products))


def join(a: Interval, b: Interval) -> Interval:
    return Interval(min(a.lo, b.lo), max(a.hi, b.hi))


# --------------------------------------------------------------------------
# Rigorous digamma brackets at positive rationals
# --------------------------------------------------------------------------

# Published digit expansion of the Euler–Mascheroni constant
# gamma = 0.57721566490153286060651209008240243104215933593992...,
# bracketed at the last stored digit (OEIS A002852 tier). Generator-grade
# evidence: re-derive or import via a proof-carrying route before any Lean
# consumer relies on these digits.
GAMMA_LO = F("0.57721566490153286060651209008240243104215933593992")
GAMMA_HI = F("0.57721566490153286060651209008240243104215933593993")


def psi_partial_sum(x: F, n_terms: int) -> F:
    """S_N(x) = sum_{k=0}^{N-1} (1/(k+1) - 1/(k+x)) as an exact Fraction."""
    total = F(0)
    for k in range(n_terms):
        total += 1 / F(k + 1) - 1 / F(k + x)
    return total


def psi_tail_bound(x: F, n_terms: int) -> F:
    """|sum_{k=N}^inf (1/(k+1) - 1/(k+x))| <= |x-1|/N for x > 0, N >= 1.

    Proof: each term equals (x-1)/((k+x)(k+1)); since x > 0 and k >= N >= 1,
    (k+x)(k+1) > k(k+1), so the absolute tail is at most
    |x-1| * sum_{k=N}^inf 1/(k(k+1)) = |x-1|/N (telescoping).
    """
    if n_terms < 1:
        raise ValueError("tail bound needs n_terms >= 1")
    return abs(x - 1) / n_terms


def psi_bracket(
    x: F, width_target: F = F(1, 10**6), n_cap: int = 8_000_000
) -> Interval:
    """Rigorous bracket of psi(x) for rational x > 0, no floating point.

    Uses psi(x) = -gamma + S_N(x) +/- |x-1|/N with gamma itself bracketed.
    N grows until the combined tail plus the pre-stored gamma slack is under
    `width_target`.

    COST MODEL (honest): the direct series converges like 1/N, so reaching a
    target width w needs N ~ |x-1|/w evaluated terms — 10^6 terms at the
    default 1e-6, and 10^50 terms for a 50-digit target. Tight certificates
    are FUTURE WORK requiring an accelerated rational algorithm (Stieltjes
    continued fraction or asymptotic expansion with a rigorous remainder);
    this engine does not fake them today.
    """
    if not isinstance(x, F):
        raise TypeError("psi argument must be an exact Fraction")
    if x <= 0:
        raise ValueError("psi needs a strictly positive rational argument")

    base_slack = GAMMA_HI - GAMMA_LO
    n_terms = max(2, int(abs(x - 1)) + 1)
    while True:
        slack = psi_tail_bound(x, n_terms)
        if slack + base_slack <= width_target:
            break
        if n_terms > n_cap:
            raise RuntimeError(
                f"width {width_target} unreachable within {n_cap} terms; "
                "widen width_target or implement an accelerated algorithm"
            )
        n_terms *= 2
    center_lo = psi_partial_sum(x, n_terms) - GAMMA_HI - slack
    center_hi = psi_partial_sum(x, n_terms) - GAMMA_LO + slack
    return Interval(center_lo, center_hi)


# --------------------------------------------------------------------------
# Exact LDL^T inspection for symmetric positive-definite matrices
# --------------------------------------------------------------------------


def _check_square_symmetric(a: list[list[F]]) -> None:
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("matrix must be square")
    for i in range(n):
        for j in range(i + 1, n):
            if a[i][j] != a[j][i]:
                raise ValueError(f"matrix is not symmetric at ({i}, {j})")


def ldlt_positive_definite(
    a: list[list[F]],
) -> tuple[bool, list[list[F]], list[F]]:
    """Exact symmetric rational matrix -> (is_pos_def, L, d).

    Returns the unit lower triangular L and diagonal d with A = L D L^T when
    every pivot d_i > 0 (positive definite); otherwise flags failure with the
    partial factors computed so far. All arithmetic is exact.
    """
    _check_square_symmetric(a)
    n = len(a)
    l_factor: list[list[F]] = [[F(0)] * n for _ in range(n)]
    d: list[F] = [F(0)] * n
    work: list[list[F]] = [row[:] for row in a]
    for i in range(n):
        pivot = work[i][i]
        if pivot <= 0:
            return False, l_factor, d
        d[i] = pivot
        l_factor[i][i] = F(1)
        for r in range(i + 1, n):
            factor = work[r][i] / pivot
            l_factor[r][i] = factor
            for c in range(i, n):
                work[r][c] -= factor * d[i] * l_factor[c][i]
    return True, l_factor, d


# --------------------------------------------------------------------------
# Lean emitters
# --------------------------------------------------------------------------


def format_fraction(q: F) -> str:
    num, den = q.numerator, q.denominator
    return str(num) if den == 1 else f"({num} / {den})"


def format_fraction_real(q: F) -> str:
    body = format_fraction(q).strip("()")
    return f"({body} : R)"


def emit_interval_line(name: str, iv: Interval, source: str) -> str:
    return (
        f"-- {name}: {iv.lo} <= value <= {iv.hi}\n"
        f"def {name}_lo : Q := {format_fraction(iv.lo)}\n"
        f"def {name}_hi : Q := {format_fraction(iv.hi)}\n"
        f"-- source: {source}"
    )


def emit_ldlt_witness(name: str, l_factor: list[list[F]], d: list[F]) -> str:
    n = len(d)
    lines = [
        f"noncomputable def {name}L : Matrix (Fin {n}) (Fin {n}) R :=",
        "  Matrix.of fun i j =>",
    ]
    branches = []
    for i in range(n):
        for j in range(n):
            if i == j:
                branches.append((f"(i, j) = ({i}, {i})", "1"))
            elif i > j and l_factor[i][j] != 0:
                branches.append(
                    (f"(i, j) = ({i}, {j})", format_fraction(l_factor[i][j]))
                )
    lines.append("    if " + branches[0][0] + f" then {branches[0][1]}")
    for predicate, value in branches[1:]:
        lines.append(f"    else if {predicate} then {value}")
    lines.append("    else 0")
    lines.append("")
    entries = ", ".join(format_fraction(v) for v in d)
    lines.append(f"def {name}D : Fin {n} → R := ![{entries}]")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Rigorous elementary brackets at interval arguments (NO stored digits)
#
# Every bracket below comes from the defining Taylor series evaluated in
# exact Fraction interval arithmetic, plus a Lagrange remainder bound that is
# itself derived in this file.  No published digit expansion is consumed here
# (the engine's only stored digits remain Euler gamma and log 2 for the psi
# tests).  Arguments are Intervals so callers can feed certified argument
# intervals - for example future zeta-zero ordinate tables - unchanged.
# --------------------------------------------------------------------------


def _sup_abs(theta: Interval) -> F:
    return max(abs(theta.lo), abs(theta.hi))


def _fact(n: int) -> F:
    f = F(1)
    for q in range(1, n + 1):
        f *= F(q)
    return f


def _exp_upper_bound(a: F, target_slack: F = F(1, 10**12)) -> F:
    """A proven rational upper bound for exp(a), a >= 0.

    With term_n = a^n/n!, once N + 1 > a every further step rescales the
    remaining tail by <= a/(N+1) < 1, hence
        total_tail <= term_N * (N+1)/(N+1-a).
    The loop threshold only trades tightness against work; soundness holds
    for every N with N + 1 > a.
    """
    if a < 0:
        raise ValueError("needs a >= 0")
    total = F(0)
    term = F(1)
    n = 0
    while True:
        total += term
        n += 1
        term *= a / F(n)
        if n > 20_000_000:
            raise RuntimeError("exp upper bound did not converge")
        # The geometric-tail ratio (n+1)/(n+1-a) is only a valid contraction
        # factor once n + 1 > a; before that it goes negative and would fake
        # convergence. Gate the acceptance on it explicitly.
        if n + 1 > a:
            tail = term * F(n + 1) / F(n + 1 - a)
            if tail < target_slack:
                return total + tail


def _kind_coefs(kind: str, n: int) -> list[tuple[int, F]]:
    """Taylor coefficients through degree bound n for the four series."""
    out: list[tuple[int, F]] = []
    for k in range(n):
        if kind == "sin":
            sign = F(1) if k % 2 == 0 else F(-1)
            deg = 2 * k + 1
            out.append((deg, sign / _fact(deg)))
        elif kind == "cos":
            sign = F(1) if k % 2 == 0 else F(-1)
            deg = 2 * k
            out.append((deg, sign / _fact(deg)))
        elif kind == "sinh":
            out.append((2 * k + 1, F(1) / _fact(2 * k + 1)))
        elif kind == "cosh":
            out.append((2 * k, F(1) / _fact(2 * k)))
        else:
            raise ValueError(kind)
    return out


_KIND_DERIV_SUP_ONE = {"sin": True, "cos": True, "sinh": False, "cosh": False}


def elementary_bracket(
    kind: str,
    theta: Interval,
    width_target: F = F(1, 10**28),
    terms_start: int = 16,
    terms_cap: int = 8192,
) -> tuple[Interval, int]:
    """Rigorous bracket of sin/cos/sinh/cosh on the whole argument interval.

    Lagrange remainder after truncating at the largest included degree E:
        |R| <= sup|theta|^(E+1) / (E+1)! * M,
        M = 1 for sin/cos, M = exp(sup|theta|) for sinh/cosh.
    The number of terms doubles until the remainder meets `width_target`
    (or `terms_cap` is hit).  Returns (bracket, terms_used).
    """
    sup = _sup_abs(theta)
    deriv_sup_one = _KIND_DERIV_SUP_ONE[kind]
    n = terms_start
    while True:
        coefs = _kind_coefs(kind, n)
        acc = const_interval(F(0))
        pw = const_interval(F(1))
        prev_deg = 0
        e_last = 0
        for deg, c in coefs:
            for _ in range(deg - prev_deg):
                pw = mul(pw, theta)
            acc = add(acc, scale(c, pw))
            prev_deg = deg
            e_last = deg
        rem = sup ** (e_last + 1) / _fact(e_last + 1)
        if not deriv_sup_one:
            rem = rem * _exp_upper_bound(sup)
        if rem <= width_target or n >= terms_cap:
            return Interval(acc.lo - rem, acc.hi + rem), n
        n *= 2


# --------------------------------------------------------------------------
# Self tests
# --------------------------------------------------------------------------


def _lean_witness_matrix() -> list[list[F]]:
    """Gram matrix of the witness already landed in C1YoshidaLdlCertificate."""
    # L unit-lower with subdiagonal entries 1/2 (row 1), 1/3, 1/4 (row 2);
    # D = diag(4, 9, 1).
    l_mat = [[F(1), F(0), F(0)], [F(1, 2), F(1), F(0)], [F(1, 3), F(1, 4), F(1)]]
    d_diag = [F(4), F(9), F(1)]
    gram = [[F(0)] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            gram[i][j] = sum(
                (l_mat[i][k] * d_diag[k] * l_mat[j][k] for k in range(3)), F(0)
            )
    expected = [
        [F(4), F(2), F(4, 3)],
        [F(2), F(10), F(35, 12)],
        [F(4, 3), F(35, 12), F(289, 144)],
    ]
    assert gram == expected, f"witness Gram mismatch: {gram}"
    return gram


LOG2_PUBLISHED_DIGITS = (
    "0.69314718055994530941723212145817656807550013436026"
)


def run_self_tests(use_mpmath: bool) -> None:
    # T1: mirror the landed Lean synthetic witness exactly.
    gram = _lean_witness_matrix()
    ok, l_factor, d = ldlt_positive_definite(gram)
    assert ok, "witness Gram must be positive definite"
    assert d == [F(4), F(9), F(1)], f"pivots mismatch: {d}"
    assert l_factor[1][0] == F(1, 2)
    assert l_factor[2][0] == F(1, 3)
    assert l_factor[2][1] == F(1, 4)
    print("T1 ldlt witness .......... OK (d = 4, 9, 1)")

    # T2: psi(1) = -gamma sits inside its bracket by construction.
    iv1 = psi_bracket(F(1))
    neg_gamma = Interval(-GAMMA_HI, -GAMMA_LO)
    assert iv1.contains(neg_gamma), f"psi(1) bracket lost -gamma: {iv1}"
    print("T2 psi(1) = -gamma ....... OK")

    # T3: psi(1/2) = -gamma - 2 log 2 against independently published digits.
    gamma_iv = Interval(GAMMA_LO, GAMMA_HI)
    log2_center = F(LOG2_PUBLISHED_DIGITS[:40])
    log2_slack = F(10) ** -38
    log2_iv = Interval(log2_center - log2_slack, log2_center + log2_slack)
    target = add(scale(F(-1), gamma_iv), scale(F(-2), log2_iv))
    iv_half = psi_bracket(F(1, 2), width_target=F(1, 10**4))
    assert iv_half.contains(target), f"psi(1/2) missed identity: {iv_half} vs {target}"
    print(f"T3 psi(1/2) identity ..... OK (width {float(iv_half.width()):.2e})")

    # T4: a non-unit rational argument brackets to smoke-test precision.
    # (Deep certificates are future work; see psi_bracket cost model.)
    iv_quarter = psi_bracket(F(1, 4), width_target=F(1, 10**4))
    assert iv_quarter.width() <= F(11, 10**4)
    print(f"T4 psi(1/4) bracket ...... OK (width {float(iv_quarter.width()):.2e})")

    # T5 (optional): cross-generate against high-precision mpmath floats.
    # The float cannot sit inside a rigorously tight bracket by itself; it is
    # checked against the bracket ENLARGED by the explicit parsing slack
    # implied by the working precision.
    if use_mpmath:
        import mpmath as mp  # noqa: PLC0415  (optional dependency)

        mp.mp.dps = 30
        parse_slack = F(10) ** -(mp.mp.dps - 2)
        for arg in (F(1), F(1, 2), F(1, 4), F(7, 3)):
            float_value = F(str(mp.psi(0, mp.mpf(arg.numerator) / arg.denominator)))
            iv = psi_bracket(arg, width_target=F(1, 10**4))
            enlarged = Interval(iv.lo - parse_slack, iv.hi + parse_slack)
            assert enlarged.contains(const_interval(float_value)), arg
        print("T5 mpmath cross-check .... OK")

    # T6: negative-definite matrix is rejected, never certified.
    bad = [[-F(1), F(0)], [F(0), -F(1)]]
    ok_bad, _, _ = ldlt_positive_definite(bad)
    assert not ok_bad
    print("T6 negative rejection .... OK")

    # T7: removable values at zero are reproduced exactly.
    for kind, lo_exact in (("sin", F(0)), ("cos", F(1)), ("sinh", F(0)), ("cosh", F(1))):
        iv_z, _ = elementary_bracket(kind, const_interval(F(0)))
        assert iv_z == Interval(lo_exact, lo_exact), (kind, iv_z)
    print("T7 elementary zeros ...... OK")

    # T8: Pythagorean identity holds as a set containment (sound direction:
    # each widened bracket contains its true value, so their pair sum
    # contains every realizable sin^2 + cos^2, in particular exactly 1).
    theta8 = Interval(F(2, 3), F(9, 10))
    s_br8, _ = elementary_bracket("sin", theta8, width_target=F(1, 10**18))
    c_br8, _ = elementary_bracket("cos", theta8, width_target=F(1, 10**18))
    total8 = add(mul(s_br8, s_br8), mul(c_br8, c_br8))
    assert total8.contains(const_interval(F(1))), f"lost sin^2+cos^2=1: {total8}"
    print(f"T8 pythagorean ........... OK (width {float(total8.width()):.2e})")

    # T9: widening the argument can only widen the hull (containment).
    p_lo, _ = elementary_bracket("sinh", const_interval(F(7, 2)))
    p_hi, _ = elementary_bracket("sinh", const_interval(F(4)))
    iv_wide, _ = elementary_bracket(
        "sinh", Interval(F(7, 2), F(4)), width_target=F(1, 10**16)
    )
    assert iv_wide.contains(join(p_lo, p_hi)), "interval hull shrank"
    print(f"T9 interval monotonicity . OK (width {float(iv_wide.width()):.2e})")

    # T10: emitters stay usable on elementary outputs.
    e10, _ = elementary_bracket("cos", const_interval(F(1)))
    line10 = emit_interval_line("cosOneSmoke", e10, "generator self-test only")
    assert "cosOneSmoke" in line10 and "-- cosOneSmoke:" in line10
    print("T10 emitter smoke ........ OK")

    # T11 (optional): float oracle cross-check for the four brackets.
    if use_mpmath:
        import mpmath as mp  # noqa: PLC0415

        mp.mp.dps = 30
        parse_slack = F(10) ** -(mp.mp.dps - 2)
        fns = {
            "sin": lambda z: mp.sin(z),
            "cos": lambda z: mp.cos(z),
            "sinh": lambda z: mp.sinh(z),
            "cosh": lambda z: mp.cosh(z),
        }
        for kind, fn in fns.items():
            for arg in (F(1), F(-4, 3), F(21, 8)):
                # Exact rational -> mpf conversion must go through the
                # integer numerator/denominator; an int/int float quotient
                # would silently round the ARGUMENT to double precision.
                zarg = mp.mpf(arg.numerator) / mp.mpf(arg.denominator)
                fv = F(str(fn(zarg)))
                br, _ = elementary_bracket(kind, const_interval(arg))
                grown = Interval(br.lo - parse_slack, br.hi + parse_slack)
                assert grown.contains(const_interval(fv)), (kind, arg)
        print("T11 elementary mpmath .... OK")


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--mpmath", action="store_true",
                        help="additionally cross-check psi brackets with mpmath")
    args = parser.parse_args()

    if args.self_test:
        run_self_tests(args.mpmath)
        return

    print(__doc__)
    print("No Yoshida entry data is encoded; see README.md.")


if __name__ == "__main__":
    main()
