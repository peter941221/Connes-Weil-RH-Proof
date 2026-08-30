#!/usr/bin/env python3
"""1062 - alpha campaign slices T2/T3: the mode dictionary validated
against the contract's own endpointSlope identity.

The contract (ConnesWeilRH/Source/CC20Concrete/EndpointKernelFormula.lean:38)
demands, verbatim:

    endpointSlope_eq_spectral :
      endpointSlope = tsum (fun n => weight n * analyticMode n 1 ^ 2)
    with weight n = eigenvalue n ^ 2 / (1 - eigenvalue n ^ 2)

and the file header (line 17) pins endpointSlope = epsilon'(1+), published
anchor ~ 22.9965 (tex:219).  This probe tests that identity end to end:

  (1) analyticMode via the BANDLIMITED INTEGRAL REPRESENTATION
        xi_n^an(x) = (1/lambda_n) *
            int_{-1}^{1} sin(2 pi (x - y)) / (pi (x - y)) xi_n(y) dy.
      The x-dependence of the integrand is ENTIRE, so "continuation across
      the regular-singular point x = 1" (1061 s1, T2) is automatic on the
      numerical side: the same quadrature gives xi_n on [0, 2].
  (2) ANCHOR test: S = sum_{n<=10} weight_n * xi_n(1)^2 vs 22.9965,
      per-mode contributions printed, stability across M = 44/56.
  (3) FALSIFICATION gate: the extension must satisfy the SL ODE
          ((1 - x^2) y')' + (chi_n - c^2 x^2) y = 0
      at x in {0.5, 1.5, 2.0} with the commutant chi_n (rebuilt here at MP
      precision as X@X of the Bonnet tridiagonal per AGENTS 7c law (13)).
      A nonzero residual would reject the eigenvectors, the normalization,
      the chi pairing, or the extension formula simultaneously.
  (4) independent float64 leg (numpy eigh, M = 600) re-derives the anchor.
  (5) THE DECISIVE BLOCK (F): the raw anchor in (2) came out 5.379, NOT
      22.9965, and the probe's failure to match found a CONVENTION BUG in
      the 1059 pin: the paper's lambda(n) is the WINDOWED FOURIER
      TRANSFORM eigenvalue (single F, alternating sign, tex prolateeq),
      whose square is the concentration eigenvalue computed in 1061, and
      the paper's L^2(R)_ev inner product (innerltwoeven) carries a
      factor 2.  Block F rebuilds the terms under the corrected
      convention and reproduces the paper's own t(n) list digit-for-digit
      (t(0)=11.9719 ... t(3)=0.0433983) and the 22.9965 anchor.

AGENTS 7c laws honored: (12) omega/chi computed at call site under workdps,
no import-time mp constants; (13) x^2 via X@X recurrence product, positivity
gated.  Eigenvector signs are irrelevant (anchor uses squares).
"""
import mpmath as mp
import numpy as np


def omega():
    return 2 * mp.pi


def gl_system(M, dps):
    """Gauss-Legendre nodes/weights on [-1,1] at arbitrary precision."""
    with mp.workdps(dps):
        guesses = [mp.cos(mp.pi * (4 * k - 1) / (4 * M + 2))
                   for k in range(1, M + 1)]
        xs = []
        for g in guesses:
            x = g
            for _ in range(40):
                pm = mp.legendre(M, x)
                pm1 = mp.legendre(M - 1, x)
                dpm = M * (pm1 - x * pm) / (1 - x * x)
                dx = pm / dpm
                x = x - dx
                if abs(dx) < mp.mpf(10) ** (-(dps - 5)):
                    break
            xs.append(x)
        ws = []
        for x in xs:
            pm1 = mp.legendre(M - 1, x)
            dpm = M * pm1 / (1 - x * x)
            ws.append(2 / ((1 - x * x) * dpm * dpm))
        return xs, ws


def k0(d):
    """K(d) = sin(2 pi d)/(pi d) and x-derivatives (call-site omega, 7c
    law (12)).  d == 0 hits the diagonal self-interaction of the
    collocation matrix (limit K(0) = 2) and is never hit at the extension
    evaluation points, which are all at positive distance from the
    strictly interior nodes."""
    if d == 0:
        return mp.mpf(2)
    return mp.sin(omega() * d) / (mp.pi * d)


def k1(d):
    """K'(d); the odd kernel has K'(0) = 0."""
    if d == 0:
        return mp.mpf(0)
    w = omega()
    return w * mp.cos(w * d) / (mp.pi * d) \
        - mp.sin(w * d) / (mp.pi * d * d)


def k2(d):
    """K''(d); Taylor K = (w/pi) - (w^3/(6 pi)) d^2 gives K''(0) = -w^3/(3 pi)."""
    if d == 0:
        return -omega() ** 3 / (3 * mp.pi)
    w = omega()
    return -w * w * mp.sin(w * d) / (mp.pi * d) \
        - 2 * w * mp.cos(w * d) / (mp.pi * d * d) \
        + 2 * mp.sin(w * d) / (mp.pi * d * d * d)


def parity_even_block(M, dps):
    xs, ws = gl_system(M, dps)
    half = M // 2
    pos = list(range(half, M))          # positive-side node indices
    neg = [M - 1 - i for i in pos]      # their reflections
    r = [mp.sqrt(w) for w in ws]
    mat = [[mp.mpf(0)] * half for _ in range(half)]
    for a in range(half):
        for b in range(half):
            i, j = pos[a], pos[b]
            val = (k0(xs[i] - xs[j]) + k0(xs[i] - xs[neg[b]])
                   + k0(xs[neg[a]] - xs[j]) + k0(xs[neg[a]] - xs[neg[b]]))
            mat[a][b] = val * r[i] * r[j] / 2
    return mat, (xs, ws, pos, neg, r)


def modes(M, dps, ncount=11):
    """Even-branch eigenvalues + node functions L2-normalized on ALL M
    nodes (even reflection duplicates the half vector, with the 1/sqrt2
    from the pairing - this is what the contract's normalization is)."""
    with mp.workdps(dps):
        mat, (xs, ws, pos, neg, r) = parity_even_block(M, dps)
        E, ER = mp.eig(mp.matrix(mat), left=False, right=True)
        pairs = sorted(((mp.re(E[i]), [mp.re(ER[j, i]) for j in
                                       range(len(E))])
                        for i in range(len(E))),
                       key=lambda p: abs(p[0]), reverse=True)
        out = []
        s2 = 1 / mp.sqrt(2)
        for lam, u in pairs[:ncount]:
            nrm = mp.sqrt(mp.fsum(v * v for v in u))
            u = [v / nrm for v in u]
            ffull = [mp.mpf(0)] * M
            for a in range(len(pos)):
                v = u[a] * s2 / r[pos[a]]
                ffull[pos[a]] = v
                ffull[neg[a]] = v
            # gate: full weighted L2 norm 1 on all nodes
            nn = mp.fsum(ws[j] * ffull[j] * ffull[j] for j in range(M))
            assert abs(nn - 1) < mp.mpf(10) ** -25
            out.append((lam, ffull))
        return out, (xs, ws)


def ext(x, lam, f, xs, ws, der=0):
    """xi^an and its x-derivatives via the bandlimited integral."""
    kf = {0: k0, 1: k1, 2: k2}[der]
    return mp.fsum(ws[j] * kf(x - xs[j]) * f[j]
                   for j in range(len(xs))) / lam


def chi_mp(n_eigen=6, basis=28, dps=60):
    """SL commutant chi_n, even branch, at MP precision:
    L = -d/dx((1-x^2) d/dx) + c^2 x^2 in the orthonormal Legendre basis;
    x^2 = (X)(X) with X the exact Bonnet tridiagonal (7c law (13))."""
    with mp.workdps(dps):
        c2 = omega() ** 2
        N = basis
        X = mp.zeros(N, N)
        for m in range(N - 1):
            off = mp.mpf(m + 1) / mp.sqrt((2 * m + 1) * (2 * m + 3))
            X[m + 1, m] = off
            X[m, m + 1] = off
        X2 = X * X
        A = mp.zeros(N, N)
        for m in range(N):
            A[m, m] = m * (m + 1) + c2 * X2[m, m]
            if m + 2 < N:
                A[m + 2, m] = c2 * X2[m + 2, m]
                A[m, m + 2] = c2 * X2[m + 2, m]
        even = list(range(0, N, 2))
        n2 = len(even)
        Ae = mp.zeros(n2, n2)
        for a in range(n2):
            for b in range(n2):
                Ae[a, b] = A[even[a], even[b]]
        E = mp.eig(Ae, left=False, right=False)
        vals = sorted(mp.re(e) for e in E)
        assert vals[0] > 0, "positivity gate (7c law 13)"
        return vals[:n_eigen]


def block_anchor(Ms=(44, 56), dps=60):
    print("=== (A) xi_n(1) values and the endpointSlope anchor "
          "sum weight_n * xi_n(1)^2 vs 22.9965 ===")
    results = {}
    with mp.workdps(dps):
        for M in Ms:
            mods, (xs, ws) = modes(M, dps)
            rows = []
            S = mp.mpf(0)
            for n, (lam, f) in enumerate(mods):
                x1 = ext(mp.mpf(1), lam, f, xs, ws)
                wt = lam * lam / (1 - lam * lam)
                term = wt * x1 * x1
                S += term
                rows.append((n, lam, x1, wt, term))
            results[M] = (rows, S)
            print(f"A1  M={M}: anchor sum n<=10 = {mp.nstr(S, 12)}")
            for (n, lam, x1, wt, term) in rows[:4]:
                print(f"    n={n}  lam={mp.nstr(lam, 12)}  "
                      f"xi({1})={mp.nstr(x1, 12)}  weight={mp.nstr(wt, 10)}"
                      f"  term={mp.nstr(term, 10)}")
            tail = mp.fsum(r[4] for r in rows[4:])
            print(f"    tail n=4..10 total = {mp.nstr(tail, 6)}")
    if len(Ms) == 2:
        a = results[Ms[0]][1]
        b = results[Ms[1]][1]
        print(f"A2  cross-M stability of the anchor: |S44-S56| = "
              f"{mp.nstr(abs(a - b), 6)}")
        va = {r[0]: r[2] for r in results[Ms[0]][0]}
        vb = {r[0]: r[2] for r in results[Ms[1]][0]}
        worst = max(abs(va[n] - vb[n]) / max(abs(va[n]), mp.mpf("1e-40"))
                    for n in range(11))
        print(f"A3  worst relative xi_n(1) disagreement M44 vs M56 = "
              f"{mp.nstr(worst, 6)}")
    return results


def block_extension_shape(dps=60):
    print("=== (B) extension smoothness across x = 1 (T2 continuation) "
          "=== ")
    with mp.workdps(dps):
        mods, (xs, ws) = modes(44, dps)
        grid = [mp.mpf("0.5"), mp.mpf("0.9"), mp.mpf("1"),
                mp.mpf("1.1"), mp.mpf("1.5"), mp.mpf("2")]
        for n in (0, 1):
            lam, f = mods[n]
            vals = [ext(x, lam, f, xs, ws) for x in grid]
            print(f"B1  n={n}: xi^an at [0.5,0.9,1,1.1,1.5,2] = "
                  f"{[mp.nstr(v, 9) for v in vals]}")


def block_ode_resid(dps=60):
    print("=== (C) SL ODE falsification gate on the extension ===")
    with mp.workdps(dps):
        c2 = omega() ** 2
        chis = chi_mp(n_eigen=6, dps=dps)
        print("C1  chi_n even branch (MP, basis=28): "
              + ", ".join(str(mp.nstr(v, 10)) for v in chis))
        mods, (xs, ws) = modes(44, dps)
        for n in (0, 1, 2):
            lam, f = mods[n]
            worst = mp.mpf(0)
            for x in [mp.mpf("0.5"), mp.mpf("1.5"), mp.mpf("2")]:
                y = ext(x, lam, f, xs, ws)
                yp = ext(x, lam, f, xs, ws, der=1)
                ypp = ext(x, lam, f, xs, ws, der=2)
                res = (1 - x * x) * ypp - 2 * x * yp \
                    + (chis[n] - c2 * x * x) * y
                rel = abs(res) / (c2 * (abs(y) + 1))
                worst = max(worst, rel)
            print(f"C2  n={n}: max |ODE residual| / (c^2 |y|) at x=0.5,1.5,2"
                  f" = {mp.nstr(worst, 4)}")


def bound_983(n):
    """Paper tex-(983)/rapid-decay bound for |lambda(n)|."""
    with mp.workdps(60):
        return (mp.mpf(2) ** (2 * n) * mp.pi ** (2 * n + mp.mpf('0.5'))
                * (mp.factorial(2 * n) ** 2)
                / (mp.factorial(4 * n) * mp.gamma(2 * n + mp.mpf('1.5'))))


PAPER_T = {0: 11.9719, 1: 8.77574, 2: 2.20528, 3: 0.0433983,
           4: 0.000125459}
PAPER_LAMBDA = [0.999971, -0.979485, 0.524086, -0.0589766, 0.00273233,
                -0.0000762914]


def block_correction(dps=60):
    """The CONVENTION CORRECTION discovered by this probe: the paper's
    lambda(n) is the eigenvalue of the WINDOWED FOURIER TRANSFORM
    P_1 F P_1 (tex prolateeq/cosalphan, single Fourier transform, signs
    alternating (minus)^n), NOT of the concentration/sinc operator
    P_1 F P_1 F (tex cosalphan1 gives lambda(n)^2 for the squared
    operator).  The collocation table of 1061 computed the squared
    operator's even-branch eigenvalues, so the paper's lambda(n) equals
    (-1)^n * sqrt(our table).  Inner product (innerltwoeven, tex:249):
    <eta|xi> = 1/2 int_R = int_0^infty, so the paper's unit-norm xi is
    sqrt(2) x our standard-L2 xi.  Then the contract's endpointSlope
    tsum (eigenvalue^2/(1-eigenvalue^2) * mode(1)^2) becomes
    t(n) = [lam_c/(1-lam_c)] * 2 * xi_n(1)^2  and the paper's own t(n)
    list (tex after (Rokh)) plus the anchor eps'(1+) ~ 22.9965 are the
    ground-truth test of the whole convention."""
    print("=== (F) CORRECTED convention: t(n) = weight_paper * "
          "xi_paper(1)^2 vs the paper's own list, anchor 22.9965 ===")
    with mp.workdps(dps):
        mods, (xs, ws) = modes(44, dps)
        S = mp.mpf(0)
        for n, (lam, f) in enumerate(mods):
            x1 = ext(mp.mpf(1), lam, f, xs, ws)
            mu = mp.sqrt(lam) * (mp.mpf(-1) ** n)      # paper lambda(n)
            wt_p = lam / (1 - lam)                     # mu^2/(1-mu^2)
            t_p = wt_p * 2 * x1 * x1                   # xi_paper = sqrt2 xi
            S += t_p
            extra = ""
            if n in PAPER_T:
                rel = abs(t_p - PAPER_T[n]) / PAPER_T[n]
                extra = f"  vs paper {PAPER_T[n]} (rel {mp.nstr(rel, 3)})"
            print(f"F1  n={n}: mu={mp.nstr(mu, 12)}  weight_p="
                  f"{mp.nstr(wt_p, 10)}  t(n)={mp.nstr(t_p, 10)}{extra}")
        print(f"F2  corrected anchor sum n<=10 = {mp.nstr(S, 12)}  vs paper "
              f"~22.9965")
        for n in range(6):
            b = bound_983(n)
            ok = abs(PAPER_LAMBDA[n]) <= b
            print(f"F3  n={n}: |mu| = {PAPER_LAMBDA[n]} <= (983) bound "
                  f"{mp.nstr(b, 8)} -> {ok}; bound^2 = "
                  f"{mp.nstr(b * b, 8)} vs lam_c = "
                  f"{mp.nstr(mp.mpf(str(mods[n][0])), 8)}")


def block_float64(M=600):
    print("=== (D) independent float64 leg (numpy eigh, M=600) ===")
    xs64, ws64 = np.polynomial.legendre.leggauss(M)
    half = M // 2
    order = np.argsort(xs64)
    xs64, ws64 = xs64[order], ws64[order]
    w = 2 * np.pi
    d = xs64[:, None] - xs64[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        K = np.sin(w * d) / (np.pi * d)
    K = np.where(d == 0, 2.0, K)
    r = np.sqrt(ws64)
    A = K * r[:, None] * r[None, :]
    pos = np.arange(half, M)
    neg = M - 1 - pos
    ev = (A[np.ix_(pos, pos)] + A[np.ix_(pos, neg)]
          + A[np.ix_(neg, pos)] + A[np.ix_(neg, neg)]) / 2
    ev = 0.5 * (ev + ev.T)          # kill any float64 asymmetry
    vals, vecs = np.linalg.eigh(ev)
    idx = np.argsort(-vals)
    tot = 0.0
    for k in idx[:11]:
        lam = vals[k]
        u = vecs[:, k]
        u = u / np.linalg.norm(u)
        ffull = np.zeros(M)
        v = u / (r[pos] * np.sqrt(2.0))
        ffull[pos] = v
        ffull[neg] = v          # even reflection (same convention as MP)
        assert abs(np.sum(ws64 * ffull * ffull) - 1.0) < 1e-10
        x1 = float(np.sum(ws64 * (np.sin(w * (1 - xs64))
                                  / (np.pi * (1 - xs64))) * ffull)) / lam
        wt = lam * lam / (1 - lam * lam)
        tot += wt * x1 * x1
    print(f"D1  float64 anchor sum n<=10 = {tot:.6f}")


def main():
    mp.mp.dps = 20
    block_anchor(Ms=(44, 56), dps=60)
    block_extension_shape(dps=60)
    block_ode_resid(dps=60)
    block_correction(dps=60)
    block_float64(M=600)
    print("=== END ===")


if __name__ == "__main__":
    main()
