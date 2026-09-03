"""1116 - D1 model detector instantiation at k=1 (MODEL, declared).

First numerical twin of the pinned D1 assembly (record 1089), built
from the Lean definitions read verbatim (preregistration section 0);
reports the LEFT side of the Stage-B domination inequality against the
certified window certificates.  Certifies nothing; RH NOT claimed.

S0 = instantiation fidelity (abort class: wrong machine).
S1 = gate data (report class: signs are findings, not failures).
"""
import json
import math
import os
import time

import mpmath
import numpy as np

mpmath.mp.dps = 80
HERE = os.path.dirname(os.path.abspath(__file__))
LOG4PI_GAMMA = float(mpmath.log(4 * mpmath.pi) + mpmath.euler)

NEXP = 9                      # n_lo = 8 -> n + 1 = 9, a_det = n + 2 = 10
A_DET = NEXP + 1
GAMMAS = [float(mpmath.im(mpmath.zetazero(j))) for j in range(1, 10)]
T = GAMMAS[0]
# fix batch 6 (post-S1 registered extension): delta = 0.0 is the TRUE
# 1089 pinned configuration - at rho on the critical line the orbit
# entries 1-rho-bar and 1-rho collide with rho and rho-bar and the
# priority order of healthyUnscaledTargetValue (first match wins, the
# semantics the add() collision policy mirrors) resolves the pair to
# rho -> 1 / rho-bar -> 0: 6 distinct targets + 7 forced line zeros
# = 13 constraints, the object whose gate Prop IS the open obligation.
# The positive-delta rows are the 1114b favorable-branch SURROGATE
# scan, registered first; its coefficients diverge as delta -> 0
# because the surrogate carries BOTH conflicting +-1 targets.
DELTAS = [0.0, 0.5, 0.25, 0.125, 0.0625, 1 / 64, 1 / 256]
PIN2, PIN3, PIN4 = 1.4433774e-6, 1.6140489e-8, 2.5999281e-10

L = 28.0
NX = 1 << 15                  # centered grid, xs[k] = (k - NX/2) * DX
DX = 2 * L / NX
XS = (np.arange(NX) - NX // 2) * DX
M_GL, M_CHK = 900, 1400
GLX, GLW = np.polynomial.legendre.leggauss(M_GL)
CHIX = None


def simpson_uniform(y, dx):
    """Composite Simpson on a uniform grid (last interval falls back to
    trapezoid when the sample count is even), keeping the stdlib + numpy
    stack declared in the preregistration."""
    n = len(y)
    if n % 2 == 0:
        tail = 0.5 * dx * (y[-1] + y[-2])
        y = y[:-1]
    else:
        tail = 0.0
    y3 = y.reshape(-1, 3)
    return float(tail + (dx / 3.0) * (y3[:, 0] + 4.0 * y3[:, 1] + y3[:, 2]).sum())


def chi(u):
    v = np.asarray(u, dtype=float)
    out = np.zeros_like(v)
    m = (v > -1.0) & (v < 1.0)
    out[m] = np.exp(-1.0 / (1.0 - v[m] ** 2))
    return out


CHIX = chi(GLX)
MOMW = GLW * CHIX


def chi1(u):
    return math.exp(-1.0 / (1.0 - u * u)) if -1.0 < u < 1.0 else 0.0


def moment_rows(zs, M):
    """(nz, M) float64 rows of B^(m)(z_i) = sum w chi x^m e^{z x}."""
    E = np.exp(np.outer(np.asarray(zs, dtype=complex), GLX))
    xf = MOMW.copy()
    out = np.empty((E.shape[0], M), dtype=complex)
    for m in range(M):
        out[:, m] = E @ xf
        xf = xf * GLX
    return out


def moment_row_mp(z, M):
    x, w = np.polynomial.legendre.leggauss(M_CHK)
    zm = mpmath.mpc(z)
    xm = [mpmath.mpf(v) for v in x]
    wm = [mpmath.mpf(w[k]) * mpmath.mpf(chi1(x[k])) for k in range(len(x))]
    Em = [mpmath.exp(zm * xm[k]) for k in range(len(x))]
    row = []
    powers = [mpmath.mpf(1)] * len(x)
    for _m in range(M):
        row.append(mpmath.fsum(wm[k] * powers[k] * Em[k]
                              for k in range(len(x))))
        powers = [powers[k] * xm[k] for k in range(len(x))]
    return row


def solve_correction(nodes, nexp):
    zs = [z for z, _ in nodes]
    Ms = len(nodes)
    Bz = moment_rows(zs, Ms)[:, 0]
    A = mpmath.zeros(Ms, Ms)
    for i, z in enumerate(zs):
        for m, v in enumerate(moment_row_mp(z, Ms)):
            A[i, m] = v
    rhs = mpmath.matrix([mpmath.mpc(v) / mpmath.power(mpmath.mpc(b), nexp)
                         for (_z, v), b in zip(nodes, Bz)])
    sol = mpmath.lu_solve(A, rhs)
    res = float(mpmath.norm(A * sol - rhs) / max(mpmath.norm(rhs), mpmath.mpf(1)))
    return sol, np.array([complex(sol[m]) for m in range(Ms)]), res


def raw_val(z, sol, nexp):
    """raw(z) = B(z)^nexp * C(z) evaluated ENTIRELY in mpmath: the
    coefficients are O(1e37) and the value is O(1), so any float64
    re-summation of sum a_m B^(m)(z) is pure cancellation noise
    (fix batch 2; the x-side build_g keeps float64 because there the
    huge amplitudes are the true scale and relative precision holds)."""
    row = moment_row_mp(z, len(sol))
    val = mpmath.fsum(sol[m] * row[m] for m in range(len(sol)))
    return complex(mpmath.power(row[0], nexp) * val)


def build_g(a, nexp):
    """h = base^{*nexp} convolved with corr, as centered circular FFT
    convolutions of RESOLVED sample grids; g = e^{x/2} h.  (Fix batch 2:
    the frequency-product route needs GL accuracy up to pi/DX ~ 1.8e3,
    where 900 GL points under-resolve the oscillatory integrand at ~1.5
    points/wavelength - the aliased junk reappeared in the
    reconstruction as a Nyquist-periodic component, caught by the
    convention self-test before any S1 datum.)"""
    base = chi(XS)
    corr = np.zeros(NX, dtype=complex)
    xp = np.ones_like(XS)
    for am in a:
        corr += am * xp * base
        xp = xp * XS
    h = corr
    for _ in range(nexp):
        h = circular_conv_centered(h, base)
    return h * np.exp(XS / 2), h


def build_selftest():
    """shape guard: build_g([1], 0) must return chi exactly (assembly
    path).  convolution guard: build_g([1], 3) = chi^{*3} and its
    trapezoid Laplace must match the analytic B(i*xi)^3 (GL reference)
    to 1e-5 - a rule-mismatch tolerance (trapezoid on the sample grid
    vs Gauss-Legendre); gross index/normalization errors are O(1).
    Sign conventions on NON-even nodes are adjudicated downstream by
    the S0.3 Parseval gate.  (The first draft's nexp=1 expected chi but
    correctly got chi*chi - the guard works.)"""
    a1 = np.array([1.0 + 0j])
    _, h0 = build_g(a1, 0)
    shape_err = float(np.abs(h0 - chi(XS)).max())
    _, h3 = build_g(a1, 3)     # = chi^{*4}: corr=chi PLUS 3 base folds
    err = 0.0
    for xi in (0.7, 3.3, 12.9, 21.0):
        Gnum = np.trapezoid(np.exp(1j * xi * XS) * h3, dx=DX)
        Gana = moment_rows([1j * xi], 1)[0, 0] ** 4
        err = max(err, abs(Gnum - Gana) / max(abs(Gana), 1e-30))
    return err, shape_err


def circular_conv_centered(p, q):
    pp = np.fft.ifftshift(p)
    qq = np.fft.ifftshift(q)
    return np.fft.fftshift(np.fft.ifft(np.fft.fft(pp) * np.fft.fft(qq))) * DX


def prime_sum(qmax, Freal):
    n = qmax
    N = (n - 1) // 2
    sieve = np.ones(N, dtype=bool)
    sieve[0] = False
    for p in range(3, int(math.isqrt(n)) + 1, 2):
        if sieve[(p - 1) // 2]:
            sieve[(p * p - 1) // 2::p] = False
    primes = np.concatenate(([2], np.nonzero(sieve)[0] * 2 + 1))
    total = 0.0
    for lo in range(0, len(primes), 20_000_000):
        pr = primes[lo:lo + 20_000_000].astype(float)
        lq = np.log(pr)
        total += float(((np.log(pr) / np.sqrt(pr))
                        * (np.interp(lq, XS, Freal)
                           + np.interp(-lq, XS, Freal))).sum())
    for p in primes:
        p = int(p)
        if p * p > n:
            break
        pk, lp = p * p, math.log(p)
        while pk <= n:
            l = math.log(pk)
            total += lp / math.sqrt(pk) * (
                float(np.interp(l, XS, Freal))
                + float(np.interp(-l, XS, Freal)))
            pk *= p
    return total


def main():
    t0 = time.time()
    st, shp = build_selftest()
    print(f"convention self-test: freq rel err {st:.2e}  "
          f"shape max err {shp:.2e}")
    assert st <= 1e-5 and shp <= 1e-12, "grid convention self-test FAILED"
    results = []
    for delta in DELTAS:
        td = time.time()
        rho = complex(0.5 + delta, T)
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
        for gm in GAMMAS:
            for sgn_ in (1, -1):
                z = 0.5 + 1j * sgn_ * gm
                if abs(z - rho) <= R:
                    add(z, 0)
        # fix batch 3 (pre-run): registered "16" was a miscount - the
        # machine-enumerated set is 17 at every scan delta: 8 distinct
        # orbit/target entries and 9 forced line zeros {1/2 +- i*gamma_1}
        # U {1/2 + i*gamma_j, j=2..8} (for delta > 0 the gamma_1 pair
        # are NOT orbit members, and 1-rho <> 1-rho-bar are distinct).
        n_expect = 13 if delta == 0.0 else 17
        assert len(nodes) == n_expect, (
            f"node structure changed at delta={delta}: "
            f"{len(nodes)} != {n_expect}")
        sol, a, cond = solve_correction(nodes, NEXP)  # cond = residual

        err = max(abs(raw_val(z, sol, NEXP) - v) / max(1.0, abs(v))
                  for z, v in nodes)
        g, h = build_g(a, NEXP)
        # support gates are AMPLITUDE-RELATIVE (1e-12 * max|.|): the
        # favorable-branch coefficients are O(1e37), so an absolute
        # floor is the wrong yardstick (S0.2 as registered is about
        # vanishing outside the support relative to the function).
        support_h = float(np.abs(h[np.abs(XS) > 10.05]).max()
                          / max(float(np.abs(h).max()), 1e-300))
        cvec = np.conj(g[(-np.arange(NX)) % NX])       # conj(g(-t))
        F = circular_conv_centered(g, cvec)
        support_F = float(np.abs(F[np.abs(XS) > 20.05]).max()
                          / max(float(np.abs(F).max()), 1e-300))
        f0 = float((np.abs(g) ** 2).sum() * DX)

        # S0.3 as fixed batch 4 (pre-data): the identity
        # conj(G(-conj z))G(z) = raw(z+1/2)*conj(raw(1/2-conj(z)))
        # holds to ratio 1.0000e+00 at every probe ABOVE the x-side
        # noise floor, but the k=1 model has coefficients O(1e27)
        # against node values O(1) (C must cancel B^9 ~ e^-54 at the
        # gamma_1 heights), so deep-cancellation probes (|rhs| down to
        # 1e-41) measure float noise, not the function.  Test set =
        # low-|Re z| nodes where both sides are above 1e-8*max|F|;
        # non-even nodes still pin the conjugate and e^{x/2}-shift
        # conventions.  At least 3 nodes must be measurable.
        scaleF = float(np.abs(F).max())
        worst = 0.0
        nmeas = 0
        ratios = []
        for z in (0.7j, 3.3j, 0.3 + 0.5j, -0.25 + 2j, 0.3 + 7.5j,
                  -0.1 + 11j, rho):
            Gq = np.trapezoid(np.exp(z * XS) * g, dx=DX)
            Gn = np.trapezoid(np.exp(-np.conj(z) * XS) * g, dx=DX)
            rhs = raw_val(z + 0.5, sol, NEXP) * np.conj(
                raw_val(0.5 - np.conj(z), sol, NEXP))
            l = np.conj(Gn) * Gq
            sc = max(abs(l), abs(rhs), 1e-300)
            rat = abs(l - rhs) / sc
            ratios.append(rat)
            if sc >= 1e-8 * scaleF:
                nmeas += 1
                worst = max(worst, rat)
        assert nmeas >= 3, f"S0.3 no measurable nodes: {ratios}"
        # fix batch 5 (pre-data): the measured ratios are 5.0e-10
        # (0.7i), 7.5e-9 (3.3i), 5.7e-6 (0.3+0.5i), 8.4e-7
        # (-0.25+2i) - off-axis residuals match the QUANTIFIED x-side
        # noise: corr sample error ~ eps*sum|a_m| ~ 1e12, smeared by
        # the base^{*9} kernel (L1 norm 0.444^9) and amplified by
        # e^{Re z * 20}; structural failures (aliasing, index or
        # conjugation errors) appear at O(1), as they did in the
        # pre-batch-4 log.  1e-4 keeps a 57x margin over the observed
        # worst residual while rejecting O(1) breaks.
        assert worst <= 1e-4, f"S0.3 FAIL delta={delta}: {worst:.2e}"

        pos0 = NX // 2                                  # xs >= 0 block
        yp = XS[pos0:]
        Fp = F[pos0:]
        Fm = F[(NX - np.arange(pos0, NX)) % NX]
        num = np.exp(yp / 2) * (Fp + Fm) - 2 * f0
        integ = np.empty_like(num)
        integ[1:] = num[1:] / (2 * np.sinh(yp[1:]))
        integ[0] = f0 / 2.0
        tail = f0 * math.log(math.tanh(yp[-1] / 2))
        arch = LOG4PI_GAMMA * f0 + simpson_uniform(integ.real, DX) + tail
        psum = prime_sum(int(math.exp(2.0 * A_DET)), F.real)
        row = dict(delta=delta, R=R, cond=cond,
                   max_abs_a=float(np.abs(a).max()),
                   sum_abs_a=float(sum(abs(complex(sol[m]))
                                       for m in range(len(sol)))),
                   support_out_h=support_h, support_out_F=support_F,
                   s01_err=float(err), parseval_worst=float(worst),
                   n_meas=nmeas, ratios=[float(r) for r in ratios],
                   f0=f0, arch=arch, prime=psum, gate=arch + psum,
                   gate_over_f0=(arch + psum) / f0)
        results.append(row)
        print(f"delta={delta:8.5f} cond={cond:.1e} |a|max="
              f"{np.abs(a).max():.1e} S0.1={err:.1e} pvl={worst:.1e}"
              f"(n={nmeas}) f0={f0:.3e} arch={arch:+.6e} prime={psum:+.6e}"
              f" GATE={arch + psum:+.6e} GATE/f0={(arch + psum) / f0:+.4e}"
              f"  [{time.time() - td:.0f}s]")
        assert err <= 1e-8, f"S0.1 FAIL delta={delta}: {err:.2e}"
        assert support_h <= 1e-12, f"S0.2 h-support FAIL delta={delta}"
        # F-support floor 1e-8 (fix batch 4): F = |G|^2-scale samples
        # carry the x-side cancellation noise of the O(1e27)-coefficient
        # assembly; measured leak 6.1e-10 relative at delta=1/2 in the
        # aborted pre-S0.3-amendment run, with the S0.3 identity exact
        # at all measurable probes - 1e-8 keeps a 3-decade margin over
        # noise and still rejects structural aliasing (O(1)) errors.
        assert support_F <= 1e-8, f"S0.2 F-support FAIL delta={delta}"

    print("\n==== S1.2 GATE vs certified window margins (1112/1113 pins) ====")
    for r in results:
        print(f"delta={r['delta']:8.5f}  GATE/f0={r['gate_over_f0']:+.4e}  "
              f"GATE/pin(2)={r['gate'] / PIN2:+.4e}  "
              f"GATE/pin(3)={r['gate'] / PIN3:+.4e}  "
              f"GATE/pin(4)={r['gate'] / PIN4:+.4e}")
    with open(os.path.join(HERE, "1116_d1_model.json"), "w") as fh:
        json.dump(dict(record="1116", model=True, nexp=NEXP, a_det=A_DET,
                       gammas=GAMMAS, results=results), fh, indent=1)
    print(f"\nwrote 1116_d1_model.json   total {time.time() - t0:.0f}s  "
          "(MODEL; certifies nothing; RH NOT claimed)")


if __name__ == "__main__":
    main()
