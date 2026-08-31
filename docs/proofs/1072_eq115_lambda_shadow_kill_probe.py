# 1072 - B (lambda*-shadow) cheap kill probe (eq-115 table + archimedean chi).
#
# Design record: 1072_eq115_lambda_shadow_kill.md (fork B-K1/B-K2/B-K3 stated
# BEFORE the run).  Follows 1069 (SIDE = B cheap kill).
#
# Build v6 (the PSWF rebuild, sinc path).  Build history is in the record s5;
# entries (d)+(e): (d) the Qepsilon "Chebyshev" reading of (qe) was a
# MISREADING - the paper's T_n there is a paper-local integral function
# (tex:1341-1349), and tex:1370 states Qepsilon(1) = 0, killing the Chebyshev
# reading.  (e) an SL collocation of the prolate differential equation
# produced GHOST eigenpairs on the non-normal Chebyshev matrix (chi_0 = 0.48
# against the true 2.747; np.linalg.eig eigenvectors carry ~1e-4 noise there),
# so v6 drops that path entirely: xi_n is taken from the SINC-KERNEL
# collocation (symmetric rKr, machine-accuracy eigenvectors, eigenvalues
# gated against the paper's printed list), chi_n is read from the D_u
# identity ratio R(x) = [x xi' - (1/2)(1-x^2) xi'']/xi + 2 pi^2 x^2, which is
# constant to ~1e-11 on the true modes, and the power series at x=1 only
# provides the continuation to [1,2].  Pinned chain (all to the tex):
#
#   xi_n        = restriction of PS_{2n,0}(2 pi, .) to [-1,1], normalized by
#                 innerltwoeven (tex:249):  int_0^1 xi_n^2 dx = 1.
#   prolateeq   (tex:967): int_{-1}^1 xi_n(x) e^{i 2 pi w x} dx
#                 = lam(n) xi_n(w), lam(n) the SIGNED printed list (tex:977);
#                 the sign is intrinsic to the function (F linear), so this
#                 is a freedom-free gate.
#   Qeps(rho)   = sum_n w_n C_n(rho), w_n = lam(n)^2/(1-lam(n)^2)  (tex:1359);
#                 C_n (sonineQbis) is quadratic in xi => sign-free.
#   chi(x)      = Qeps(e^x)/(2 eps'(1+)); eps'(1+) pinned at tex:1367
#                 (22.9964756839, record 1062) and independently re-summed.
#   tau         unchanged (exact SHA-pinned table); TSPEC gate unchanged.
#
# NO zeta-zero input exists in this pipeline (the B-kill structural fact).
#
# Run (WSL, ONE command, log on the Linux side; SYNC the file first:
#   cp /mnt/c/Projects/Connes-Weil-RH-Proof/docs/proofs/<this file> \
#      /home/peter/rh/docs/proofs/ ):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with scipy --with mpmath \
#      python -u docs/proofs/1072_eq115_lambda_shadow_kill_probe.py \
#      > /home/peter/1072_probe.log 2>&1; echo DONE-RC=$?'

import json

import numpy as np
import scipy.optimize as opt
import mpmath as mp

mp.mp.dps = 40

L = float(np.log(2.0))
LAM_PAPER = 1.05158
MS = [64, 256, 1024, 1732]
NLB = 5                              # load-bearing modes n=0..4: the printed
                                     # t(n) list (tex:1367) carries eps'(1+) to
                                     # 5e-6; n>=5 weights are <= 6e-9 by the
                                     # rapid-decay bound (983), and eigh
                                     # eigenvectors below mu ~ 1e-9 sit at the
                                     # noise/gap floor (v7 finding).
EPS_PRIME_1PLUS = 22.9964756839      # tex:1367/219 pin (record 1062)
FACT1 = 0.00122                      # paper eq-(115), at lam = 1.05158
T_PRINTED = [11.9719, 8.77574, 2.20528, 0.0433983, 0.000125459]  # tex:1367
LAM_PRINTED = [0.999971, -0.979485, 0.524086, -0.0589766, 0.00273233,
               -0.0000762914]        # tex:977 (signed Fourier eigenvalues)
MGL = 256                            # GL nodes on [-1,1] for the collocation
NG = 3001                            # dense-grid half size


# ------------------------------------------------------- prolate construction
def bary_weights(x):
    """Barycentric weights 1/prod(x_j - x_k) for the GL node set."""
    n = x.size
    w = np.zeros(n)
    for j in range(n):
        d = 1.0
        for k in range(n):
            if k != j:
                d *= (x[j] - x[k])
        w[j] = 1.0 / d
    return w


def bary_eval(x, bw, vals, xq):
    out = np.empty(xq.shape)
    for k, x0 in enumerate(xq):
        d = x0 - x
        hit = np.abs(d) < 1e-14
        if hit.any():
            out[k] = vals[hit][0]
            continue
        out[k] = (bw / d @ vals) / (bw / d).sum()
    return out


def diff_matrix(x, bw):
    """Barycentric differentiation matrix for arbitrary nodes."""
    n = x.size
    D = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j:
                D[i, j] = (bw[j] / bw[i]) / (x[i] - x[j])
    D[np.arange(n), np.arange(n)] = -D.sum(axis=1)
    return D


def prolate_modes(count):
    """Even prolate modes from the sinc-kernel collocation (the trusted
    path):  P_1 F P_1 F  on [-1,1], kernel sin(2 pi (x-y))/(pi (x-y)).
    Returns a list of dicts with keys mu, x1, chi, dfull, fvals, rstd."""
    nodes, weights = np.polynomial.legendre.leggauss(MGL)
    r = np.sqrt(weights)
    dx = nodes[:, None] - nodes[None, :]
    # 2*sinc(2d) = sin(2 pi d)/(pi d): the factor 2 is load-bearing (1058).
    K = 2.0 * np.sinc(2.0 * dx)
    A = r[:, None] * K * r[None, :]
    ev, evec = np.linalg.eigh(A)
    lam = ev[::-1]
    U = evec[:, ::-1]
    flip = np.arange(MGL)[::-1]

    n140, w140 = np.polynomial.legendre.leggauss(140)
    r140 = np.sqrt(w140)
    K140 = 2.0 * np.sinc(2.0 * (n140[:, None] - n140[None, :]))
    ev140 = np.linalg.eigvalsh(r140[:, None] * K140 * r140[None, :])[::-1]
    err = np.max(np.abs(lam[:count] - ev140[:count]))
    print(f"LAMK-XCHK|M{MGL}-vs-M140|first {count}|max={err:.2e}  "
          f"(gate <= 1e-10)", flush=True)
    assert err < 1e-10, "collocation not converged"

    bw = bary_weights(nodes)
    D = diff_matrix(nodes, bw)
    out = []
    for col in range(MGL):
        if lam[col] < 1e-16:              # below the float64 eigh noise floor:
            break                         # eigenvectors are parity-mixed junk
        par = (U[flip, col] * U[:, col]).sum() / (U[:, col] ** 2).sum()
        if par < 0.9:                     # SIGNED parity: odd modes give -1
            continue
        f = U[:, col] / r                 # undo the r-scaling
        if f[0] < 0:
            f = -f                        # xi(1) > 0 (cosmetic; Qeps quadratic)
        f = f * np.sqrt(2.0 / (f ** 2 * weights).sum())  # int_0^1 xi^2 = 1
        dfull = D @ f
        # chi_n from the D_u identity ratio (constant on the true modes)
        num = nodes * dfull - 0.5 * (1 - nodes ** 2) * (D @ dfull)
        R = num / f + 2 * np.pi ** 2 * nodes ** 2
        good = (np.abs(nodes) < 0.85) & (np.abs(f) > 1e-2 * np.abs(f).max())
        chi = float(R[good].mean())
        rstd = float(R[good].std() / max(abs(chi), 1e-30))
        # endpoint values by barycentric extrapolation: f[0] sits at the
        # EDGE NODE x = 0.9999628, not at 1 (v9 finding: seeding the series
        # there costs ~ xi'(1) * 3.7e-5 ~ 1e-5..1e-3 per mode)
        x1e = float(bary_eval(nodes, bw, f, np.array([1.0]))[0])
        d1e = float(bary_eval(nodes, bw, dfull, np.array([1.0]))[0])
        out.append({"mu": float(lam[col]), "x1": x1e, "d1": d1e,
                    "chi": chi, "dfull": dfull, "fvals": f, "rstd": rstd,
                    "resolved": True})
        if len(out) == count:
            break
    n_res = len(out)
    assert n_res >= 6, "even fewer resolved modes than the printed list"
    # modes beyond the noise floor get zero weights (their w_n ~ 1e-14 or
    # less: the rapid-decay tail gate below bounds what they could carry)
    while len(out) < count:
        out.append({"mu": 0.0, "x1": 0.0, "chi": 0.0,
                    "dfull": np.zeros(MGL), "fvals": np.zeros(MGL),
                    "rstd": 0.0, "resolved": False})
    print(f"PROLATE|resolved even modes = {n_res} (of {count} requested; "
          f"the rest sit below the eigh noise floor)", flush=True)
    # printed-list gate: the even-branch sqrt(mu) IS |lam(n)| (tex:977)
    mu_even = np.array([o["mu"] for o in out[:6]])
    sq = np.sqrt(np.maximum(mu_even, 0.0))
    perr = max(abs(sq[k] - abs(LAM_PRINTED[k])) for k in range(6))
    print(f"LAMK-XCHK|even sqrt(mu_0..5) vs printed |lam(n)||max={perr:.2e}  "
          f"(gate <= 1e-5)", flush=True)
    assert perr < 1e-5, "prolate eigenvalue convention mismatch"
    rmax = max(o["rstd"] for o in out[:4])
    print(f"PROLATE|R-constancy chi_0..3 = "
          f"{out[0]['chi']:.6f}, {out[1]['chi']:.6f}, "
          f"{out[2]['chi']:.6f}, {out[3]['chi']:.6f}"
          f"|max rel std (n<=3) = {rmax:.2e}  (gate <= 1e-8)", flush=True)
    assert rmax < 1e-8, "D_u identity not constant on the collocation modes"
    return out, nodes, weights, bw, D


def series_coeffs(chi_half, a0, a1, nterms=90):
    """xi^an(x) = sum a_k t^k at x = 1+t.  Recursion from the prolate ODE
    (1-x^2) xi'' - 2 x xi' + (2 CHI - 4 pi^2 x^2) xi = 0:
    a_{m+1} = [(2 CHI - 4 pi^2 - m(m+1)) a_m - 8 pi^2 a_{m-1}
               - 4 pi^2 a_{m-2}] / (2 (m+1)^2).
    Seeded by BOTH endpoint values from the grid side (xi(1), xi'(1)),
    barycentrically extrapolated - NOT by f[0] (edge node, v9 finding)."""
    ch = mp.mpf(float(chi_half))
    a = [mp.mpf(0)] * nterms
    a[0] = mp.mpf(float(a0))
    a[1] = mp.mpf(float(a1))
    for m in range(1, nterms - 1):
        num = (2 * ch - 4 * mp.pi ** 2 - m * (m + 1)) * a[m] \
            - 8 * mp.pi ** 2 * a[m - 1] \
            - (4 * mp.pi ** 2 * a[m - 2] if m >= 2 else mp.mpf(0))
        a[m + 1] = num / (2 * (m + 1) ** 2)
    return a


def series_eval(a, t, deriv=False):
    """mpmath evaluation of sum a_k t^k (or sum k a_k t^{k-1})."""
    s = mp.mpf(0)
    for k, av in enumerate(a):
        if deriv:
            if k >= 1:
                s += k * av * mp.mpf(t) ** (k - 1)
        else:
            s += av * mp.mpf(t) ** k
    return float(s)


# ------------------------------------------------------- tau side (unchanged)
def load_table():
    """Exact-rational angles/coefficients from the committed manifest."""
    with open("scripts/cc20_eq115/data/cc20_eq115_manifest.json",
              encoding="utf-8") as fh:
        man = json.load(fh)
    ang = sorted(man["angles"], key=lambda r_: r_["index"])
    coef = sorted(man["coefficients"], key=lambda r_: r_["index"])
    m = int(man["m"])
    assert m == 1732 and len(ang) >= m and len(coef) >= m
    alphas = np.array([int(rr["numerator"]) / int(rr["denominator"])
                       for rr in ang[:m]])
    ds = np.array([int(rr["numerator"]) / int(rr["denominator"])
                   for rr in coef[:m]])
    print(f"MANIFEST|entries={m}|alpha_1={alphas[0]:.13f}|d_1={ds[0]:.13f}"
          f"|GATE-PASS", flush=True)
    return alphas, ds, m


def tau_shape(xgrid, alphas, ds, m):
    """A(x) = tau(1, x)/lam = (1/L)[1 + 2 sum (cos - d_n cos(alpha_n))]."""
    n = np.arange(1, m + 1)
    ph = 2.0 * np.pi / L
    C1 = np.cos(np.outer(xgrid, ph * n))
    C2 = np.cos(np.outer(xgrid, ph * alphas))
    return (1.0 + 2.0 * (C1.sum(1) - (ds * C2).sum(1))) / L


def energy(lam, Ashape, chi, xgrid):
    return np.trapezoid(np.abs(lam * Ashape - chi), xgrid)


def argmin_lambda(Ashape, chi, xgrid):
    r = opt.minimize_scalar(
        lambda lam: energy(lam, Ashape, chi, xgrid),
        bounds=(1.0, 1.2), method="bounded", options={"xatol": 1e-9})
    grid = np.linspace(1.0, 1.2, 20001)
    vals = [energy(l, Ashape, chi, xgrid) for l in grid]
    lamg = grid[int(np.argmin(vals))]
    ok = abs(r.x - lamg) < 1e-5
    print(f"CONVEXITY|brent={r.x:.7f}|grid={lamg:.7f}|agree={ok}", flush=True)
    assert ok, "E landscape not convex at certificate scale"
    return float(r.x)


def t_spectrum(alphas, ds, m, lam):
    """Compressed spectrum of (1/lam) T (opT, tex:1614); +-alpha sides (2m)."""
    J = m
    j = np.arange(-J, J + 1)
    Vp = np.sinc(alphas[None, :] - j[:, None])        # <xi_j, xi_alpha>
    Vm = np.sinc(alphas[None, :] + j[:, None])        # the -alpha_n side
    V = np.hstack([Vp, Vm])                           # (2J+1) x 2m
    ds_full = np.concatenate([ds, ds])                # d(|n|), both sides
    G = (np.sqrt(ds_full)[:, None] * (V.T @ V) * np.sqrt(ds_full)[None, :])
    eigG = np.linalg.eigvalsh(G)
    compressed = np.concatenate(([1.0], 1.0 - eigG[::-1]))
    top = np.sort(compressed)[::-1][:6]
    paper = np.array([1.0, 0.652824, 0.027475, 0.000290146,
                      0.0000877245, 0.0000756436])   # tex:1713-1730, m=1733
    err = np.max(np.abs(top - paper))
    print(f"TSPEC|lam={lam}|top-of-(1/lam)T = "
          f"{np.array2string(top, precision=6)}", flush=True)
    print(f"TSPEC|top-3 max abs err = {err:.2e}  (gate <= 5e-3)"
          f"|lam*0.652824 = {lam * paper[1]:.6f} (paper lam_2 = 0.686494)",
          flush=True)
    assert err < 5e-3, "compressed spectrum does not reproduce the paper list"


# ------------------------------------------------------------------ the build
def build_chi(xgrid):
    """The true chi(x) = Qeps(e^x)/(2 eps'(1+)) from the PSWF pipeline.
    Carries the first NLB modes only; the n >= NLB tail is BOUNDED by the
    rapid-decay weights (983), not computed (their eigenvectors sit at the
    eigh noise floor - v7 finding, record s5 (e))."""
    modes, nodes, weights, bw, D = prolate_modes(6)
    mu_all = np.array([modes[n]["mu"] for n in range(6)])
    wn = mu_all[:NLB] / (1.0 - mu_all[:NLB])           # tex:1359 weights
    print(f"QEPS|weights w_0..4 = {np.array2string(wn, precision=8)}",
          flush=True)

    xlo = np.linspace(0.5, 1.0, NG)
    xhi = np.linspace(1.0, 2.0, NG)
    # ASCENDING: np.interp requires a sorted xp grid (v9 finding: the old
    # [xlo[::-1], xhi[1:]] order silently poisoned every x < 1 interp)
    xgfull = np.concatenate([xlo, xhi[1:]])            # 0.5 -> 2.0
    XI = np.zeros((NLB, xgfull.size))                  # xi_n(x)
    DXI = np.zeros((NLB, xgfull.size))                 # x * xi_n'(x)
    x1s = np.zeros(NLB)                                # xi_n(1)
    mpmath_a = []

    for n in range(NLB):
        md = modes[n]
        x1s[n] = md["x1"]
        mpa = series_coeffs(md["chi"], md["x1"], md["d1"])
        mpmath_a.append(mpa)
        # seed identity (the ODE at t = 0):  xi'(1) = (chi - 2 pi^2) xi(1);
        # validates the extrapolated seeds AND the R-ratio chi jointly
        rhs = (md["chi"] - 2 * np.pi ** 2) * md["x1"]
        serr = abs(md["d1"] - rhs) / max(abs(md["d1"]), 1e-30)
        print(f"PROLATE|seed identity n={n}|xi(1)={md['x1']:.9f}"
              f"|xi'(1)={md['d1']:.6f}|rel={serr:.2e}  (gate <= 1e-6)",
              flush=True)
        assert serr < 1e-6, "series seed identity failed"
        coeffs = np.array([float(v) for v in mpa])
        dcoeffs = coeffs * np.arange(coeffs.size)
        # collocation side [0.5, 1]
        XI[n, :NG] = bary_eval(nodes, bw, md["fvals"], xlo)
        DXI[n, :NG] = bary_eval(nodes, bw, md["dfull"], xlo) * xlo
        # series side [1, 2]
        ks = np.arange(coeffs.size)
        Th = (xhi - 1.0)[:, None] ** ks[None, :]
        XI[n, NG - 1:] = Th @ coeffs
        Td = np.concatenate([np.zeros((NG, 1)),
                             (xhi - 1.0)[:, None] ** (ks[1:] - 1)[None, :]],
                            axis=1)
        DXI[n, NG - 1:] = xhi * (Td @ dcoeffs)

    # --- GATE: continuation continuity xi(1-h) vs xi(1+h), and xi'(1) match,
    #     PER MODE over the load-bearing set (hard 1e-6 each; n=4 vector
    #     noise ~ noise/gap ~ 5.6e-12 against the k=7 odd mode, so 1e-6 has
    #     two orders of margin)
    h = 1e-3
    for n in range(NLB):
        cv = abs(float(bary_eval(nodes, bw, modes[n]["fvals"],
                                 np.array([1 - h]))[0])
                 - series_eval(mpmath_a[n], -h))
        dv = abs(float(bary_eval(nodes, bw, modes[n]["dfull"],
                                 np.array([1 - h]))[0])
                 - series_eval(mpmath_a[n], -h, deriv=True))
        print(f"PROLATE|continuity n={n}|xi {cv:.2e}|xi' {dv:.2e}"
              f"  (gates <= 1e-6)", flush=True)
        assert cv < 1e-6 and dv < 1e-6, "continuation disagrees with grid"

    # --- GATE: prolateeq (tex:967), freedom-free (signs are intrinsic)
    gq, gw = np.polynomial.legendre.leggauss(160)
    xs = 0.5 * (gq + 1.0)                 # nodes on [0,1]
    errmax = 0.0
    for n in range(3):
        vals = bary_eval(nodes, bw, modes[n]["fvals"], xs)
        for w0, xi_w in (
                (0.0, float(bary_eval(nodes, bw, modes[n]["fvals"],
                                      np.array([0.0]))[0])),
                (0.7, float(bary_eval(nodes, bw, modes[n]["fvals"],
                                      np.array([0.7]))[0])),
                (1.3, series_eval(mpmath_a[n], 0.3))):
            lhs = 2.0 * float((vals * np.cos(2 * np.pi * w0 * xs)
                               * (0.5 * gw)).sum())
            rhs = LAM_PRINTED[n] * xi_w
            errmax = max(errmax, abs(lhs - rhs) / max(abs(rhs), 1e-30))
    print(f"PROLATE|prolateeq Fourier relation|max rel={errmax:.2e}"
          f"  (gate <= 1e-6)", flush=True)
    assert errmax < 1e-6, "prolateeq (tex:967) fails"

    # --- GATE: printed t(n) = w_n xi_n(1)^2   (tex:1367)
    tmine = wn * x1s[:NLB] ** 2
    terr = max(abs(tmine[k] - T_PRINTED[k]) / T_PRINTED[k] for k in range(5))
    print(f"PROLATE|t(n) anchor|max rel={terr:.2e}  (gate <= 5e-3)"
          f"|t={np.array2string(tmine[:5], precision=6)}", flush=True)
    assert terr < 5e-3, "printed t(n) anchor failed"

    # --- GATE: eps'(1+) self-sum vs pinned value
    ep = float(tmine.sum())
    eerr = abs(ep - EPS_PRIME_1PLUS) / EPS_PRIME_1PLUS
    print(f"PROLATE|eps'(1+) own sum={ep:.9f} vs pinned {EPS_PRIME_1PLUS}"
          f"|rel={eerr:.2e}  (gate <= 5e-3)", flush=True)
    assert eerr < 5e-3, "eps'(1+) sum mismatch"
    norm = 2.0 * EPS_PRIME_1PLUS          # the pinned value (1062-validated)

    # --- mpmath cross-check of the series (n=0,1,2 at x=1.5)
    for n in (0, 1, 2):
        ref = float(sum(mpmath_a[n][k] * mp.mpf("0.5") ** k
                        for k in range(len(mpmath_a[n]))))
        got = XI[n, NG - 1 + (NG - 1) // 2]
        rerr = abs(got - ref) / abs(ref)
        print(f"PROLATE|mpmath series xchk n={n} x=1.5|rel={rerr:.2e}  "
              f"(gate <= 1e-9)", flush=True)
        assert rerr < 1e-9

    # --- tail of the Qeps series: the paper's own rapid-decay bound (983)
    def rd_bound(n):
        nn = mp.mpf(2 * n)
        return (2 ** nn * mp.pi ** (nn + mp.mpf("0.5"))
                * mp.factorial(2 * n) ** 2
                / (mp.factorial(4 * n) * mp.gamma(nn + mp.mpf("1.5"))))
    tail_w = sum(rd_bound(n) ** 2 / (1 - rd_bound(n) ** 2)
                 for n in range(NLB, 30))
    print(f"QEPS|rapid-decay (983) tail sum_n>=5 w_n = {float(tail_w):.2e}  "
          f"(gate <= 1e-8; w_5/w_4 <= 1e-3, C_n ratios O(1) monitored below)",
          flush=True)
    assert tail_w < 1e-8, "series tail not negligible"

    # --- Qeps(rho), tex:1359 sonineQbis; quadratic in xi => sign-free
    def qterm(rho, n):
        a0 = 1.0 / rho
        xq = a0 + (1.0 - a0) * 0.5 * (gq + 1.0)
        wq = 0.5 * (1.0 - a0) * gw
        integ = float((np.interp(xq, xgfull, DXI[n])
                       * np.interp(rho * xq, xgfull, DXI[n]) * wq).sum())
        d_xinv = np.interp(a0, xgfull, DXI[n]) / a0
        d_rho = np.interp(rho, xgfull, DXI[n]) / rho
        return wn[n] * (np.sqrt(rho) * integ
                        + rho ** (-1.5) * d_xinv * x1s[n]
                        - rho ** 1.5 * x1s[n] * d_rho)

    def qeps(rho):
        return sum(qterm(rho, n) for n in range(NLB))

    # --- GATE (tex:1370 "Qeps(1) = 0"): the operational content is that
    #     Qeps extends LINEARLY through 0 at rho = 1+; the slope itself is
    #     O(sum w_n C_n'(1)) ~ 1e3 (NOT small - the old absolute 1e-5 gate
    #     at rho=1+1e-7 was mis-calibrated)
    eps_grid = np.array([1e-5, 2e-5, 4e-5])
    qvals = np.array([qeps(1.0 + e) for e in eps_grid])
    slopes = qvals / eps_grid
    sl_rel = float((slopes.max() - slopes.min()) / abs(slopes.mean()))
    print(f"QEPS|Qeps(1+eps) linear extension|slopes = "
          f"{np.array2string(slopes, precision=1)}|rel spread={sl_rel:.2e}"
          f"  (gate <= 5e-3)", flush=True)
    assert sl_rel < 5e-3, "Qeps does not extend linearly through Qeps(1)=0"

    # term-share monitor: no single included term may dwarf the sum shape
    dom_err = 0.0
    for r_ in (1.1, 1.3, 1.6, 2.0):
        tot = qeps(r_)
        shares = [qterm(r_, n) / max(abs(tot), 1e-30) for n in range(1, NLB)]
        dom_err = max(dom_err, max(abs(s) for s in shares))
    print(f"QEPS|max term share n>=1 = {dom_err:.3f}  (gate <= 0.6; "
          f"catches junk rows, the true shape is FACT1's business)",
          flush=True)
    assert dom_err < 0.6, "a single series term dominates Qeps"

    chi = np.array([qeps(float(np.exp(x))) / norm for x in xgrid])
    print(f"QEPS|chi range [{chi.min():.6f}, {chi.max():.6f}]"
          f"|mean={chi.mean():.6f}|tau-shape mean (lam=1) = {1.0 / L:.6f}",
          flush=True)
    return chi


def run():
    print("=== 1072 B kill probe, build v9 (PSWF chi, sinc path, "
          "endpoint-extrapolated seeds, ascending interp grid) ===",
          flush=True)
    alphas, ds, m_full = load_table()
    xgrid = np.linspace(0.0, L, 4001)
    chi = build_chi(xgrid)

    print("\n=== T-spectrum validation at the paper scale ===", flush=True)
    t_spectrum(alphas, ds, m_full, LAM_PAPER)

    print("\n=== the kill measurement: lambda*(m) trajectory ===", flush=True)
    Ashape_full = tau_shape(xgrid, alphas, ds, m_full)
    e_at_paper = energy(LAM_PAPER, Ashape_full, chi, xgrid)
    print(f"FACT1|2*E(1.05158; 1732)={2 * e_at_paper:.8f} "
          f"(paper eq-(115): ~{FACT1}; gate |diff| <= 5e-3)", flush=True)
    assert abs(2 * e_at_paper - FACT1) < 5e-3, "Fact-1 anchor failed"

    lamstars = {}
    for m in MS:
        Ashape = tau_shape(xgrid, alphas[:m], ds[:m], m)
        lam_star = argmin_lambda(Ashape, chi, xgrid)
        e_star = energy(lam_star, Ashape, chi, xgrid)
        e_paper = energy(LAM_PAPER, Ashape, chi, xgrid)
        lamstars[m] = lam_star
        print(f"KILL|m={m}|lam*(m)={lam_star:.6f}|E(lam*)={e_star:.3e}"
              f"|E(1.05158)={e_paper:.3e}"
              f"|paper-is-optimum={abs(lam_star - LAM_PAPER) < 5e-3}",
              flush=True)
    drift = max(abs(lamstars[MS[-1]] - lamstars[m]) for m in MS[:-1])
    print(f"KILL|trajectory={ {m: round(float(v), 6) for m, v in lamstars.items()} }"
          f"|max drift vs m={MS[-1]}: {drift:.6f}", flush=True)

    print("\n=== sensitivity: what the fit scale actually responds to ===",
          flush=True)
    base = lamstars[m_full]
    top5 = np.argsort(ds)[-5:]
    for eps in (1e-3,):
        dsp = ds.copy()
        dsp[top5] += eps
        up = argmin_lambda(tau_shape(xgrid, alphas, dsp, m_full), chi, xgrid)
        dsp = ds.copy()
        dsp[top5] -= eps
        dn = argmin_lambda(tau_shape(xgrid, alphas, dsp, m_full), chi, xgrid)
        print(f"SENS|top-5 d_n +-{eps}: lam* = {up:.6f} / {dn:.6f} "
              f"(base {base:.6f}) |dlam| ~ {max(abs(up-base), abs(base-dn)):.6f}",
              flush=True)

    print("=== done: grep 'MANIFEST|LAMK|PROLATE|QEPS|TSPEC|FACT1|KILL|SENS|"
          "CONVEXITY' ===", flush=True)


if __name__ == "__main__":
    run()
