"""1086 - the g3 carrier: closed-form gate + first direct measurement of the
Lean gate quantity arch(h.convSq).

Pre-registered fork: docs/proofs/1086_g3_carrier_design.md (BEFORE any run).
Follows 1085 (kernel (a) == the record-1080 scalar gate on one object).

Arms:
  G1  closed-form chirped Gaussian phi_cf (design record section 3) vs the
      1078-rig numerical Bromwich inverse (law-26 self-consistency).
  G2  the 1079 pipeline verbatim (hard truncation + polynomial bumps)
      reproduces fl2 ~ -1.294 (rig-reuse guard).
  G3-G5  the SMOOTH carrier h_r = chi_r * phi + sum_m c_m b_m,
      b_m = u^m chi_r (C-infinity legal, support strictly inside the open
      root window): 3x3 node-restoring solve at {0, 1/2, 1}, detection at
      rho_2, fl2 surrogate, and THE GATE QUANTITY
        arch(h.convSq) = c0*F(0) + int_0^{2a} I(y) dy + F(0)*log(tanh a),
      F = hermitian autocorrelation of h, c0 = log(4 pi) + gamma,
      F(0) = ||h||^2, integrand I(y) -> F(0)/2 at y -> 0+.

Run (WSL, through the resource runner):
  scripts/run_resource_aware_task.sh --workspace /home/peter/rh \
    --log /home/peter/rh/build-logs/probe-1086.log -- \
    /home/peter/.local/bin/uv run --with numpy --with mpmath \
    python -u docs/proofs/1086_g3_carrier_probe.py
Env: CD_1086 (1.50), BETA_1086 (0.49), RS_1086 ("0.95,0.8,0.6"), HP_1086 (1)
"""

import importlib.util
import os

import numpy as np
from mpmath import mp, mpf, exp as mexp, log as mlog, pi as mpi
from mpmath import tanh as mtanh

mp.dps = 30

_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1077", os.path.join(_here, "1077_pinned_detector_sign_probe.py"))
assert _spec is not None and _spec.loader is not None
p1077 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1077)
make_g3 = p1077.make_g3
normalize_family3 = p1077.normalize_family3
mu_3_star = p1077.mu_3_star
zero_cache = p1077.zero_cache

_trapz = getattr(np, "trapezoid", None) or np.trapz

CD = float(os.environ.get("CD_1086", "1.50"))
BETA = float(os.environ.get("BETA_1086", "0.49"))
RS = [float(x) for x in os.environ.get("RS_1086", "0.95,0.8,0.6").split(",")]
HP = os.environ.get("HP_1086", "1") == "1"

A = float(mlog(mpf(2)) / 2)           # root-window half-width log 2 / 2
C0 = float(mlog(4 * mpi) + mp.euler)  # the Lean constant log(4 pi) + gamma
M1079_FL2 = -1.294                    # 1079 corrected-object surrogate anchor

N_U = 8193                            # dense u-grid over [-a, a]
N_GL = 400                            # Gauss-Legendre nodes for Mellin values
_XG, _WG = np.polynomial.legendre.leggauss(N_GL)


def bsmooth(x):
    """float64 C-infinity profile b(x) = exp(-1/(1-x^2)) on |x| < 1."""
    arr = np.asarray(x, dtype=float)
    out = np.zeros_like(arr)
    inside = np.abs(arr) < 1.0
    xi = arr[inside]
    out[inside] = np.exp(-1.0 / (1.0 - xi * xi))
    return out


_B0 = float(bsmooth(np.array([0.0]))[0])   # b(0) = exp(-1); chi = b/b0


def bsmooth_hp(x):
    if abs(x) >= 1:
        return mpf(0)
    return mexp(-1 / (1 - x * x))


def run():
    print("=== 1086 g3 carrier: closed-form gate + arch measurement ===",
          flush=True)
    import mpmath as _mp
    g2 = mp.im(_mp.zetazero(2))
    gamma_2 = float(g2)
    delta_mp = mpf(str(CD)) / g2
    delta = float(delta_mp)
    d2 = delta * delta
    norm_mp, _ = normalize_family3(delta_mp)
    mu_mp = mu_3_star(delta_mp, BETA, g2)
    mu = float(mu_mp)
    print(f"cfg|cd={CD}|beta={BETA}|gamma2={gamma_2:.5f}|delta={delta:.6f}"
          f"|d2={d2:.6e}|N'={float(norm_mp):.6e}|mu*={mu:.6f}"
          f"|a={A:.6f}|c0={C0:.12f}", flush=True)

    lam = d2 - 1j * mu

    # ---- closed form (design record section 3).  The e^{-u/2} factor comes
    # from e^{-su} with s = 1/2 + it; the 1/(2 sqrt(pi lambda)) is the
    # normalization of the base Gaussian's inverse ((d4 - d2/4) applied to G,
    # NOT to the bare Gaussian). ----------------------------------------------
    def phi_cf(u):
        uu = np.asarray(u, dtype=float)
        q = (1.0 / (8 * lam) + 3.0 / (4 * lam * lam)
             - (1.0 / (16 * lam * lam) + 3.0 / (4 * lam ** 3)) * uu ** 2
             + uu ** 4 / (16 * lam ** 4))
        return (float(norm_mp) * np.exp(-lam / 4) * np.exp(-uu / 2) * q
                * np.exp(-uu ** 2 / (4 * lam)) / (2.0 * np.sqrt(np.pi * lam)))

    lamh = mpf(str(d2)) - 1j * mu_mp
    g3h = make_g3(delta_mp, norm_mp, mu_mp)

    def phi_cf_hp(u):
        q = (1 / (8 * lamh) + 3 / (4 * lamh ** 2)
             - (1 / (16 * lamh ** 2) + 3 / (4 * lamh ** 3)) * u ** 2
             + u ** 4 / (16 * lamh ** 4))
        return (norm_mp * mexp(-lamh / 4) * mexp(-u / 2) * q
                * mexp(-(u * u) / (4 * lamh)) / (2 * mp.sqrt(mpi * lamh)))

    # ---- Bromwich inverse on the 1078 rig grid ---------------------------------
    T = 10.0 / delta
    Nt = 8192
    tgrid = np.linspace(-T, T, Nt)
    qline = 0.25 + tgrid * tgrid
    g3_line = float(norm_mp) * qline * (tgrid * tgrid) * np.exp((-d2 + 1j * mu) * qline)
    u_max = max(6.0 * A, 4.0 / delta)
    ugrid = np.linspace(-u_max, u_max, 4097)
    phi_brom = np.empty_like(ugrid, dtype=complex)
    for iu in range(ugrid.size):
        integrand = g3_line * np.exp(-1j * ugrid[iu] * tgrid)
        phi_brom[iu] = np.exp(-0.5 * ugrid[iu]) / (2.0 * np.pi) * _trapz(integrand, tgrid)

    def phi_brom_exact(us):
        """Reference evaluated AT the point on a 4x finer t-grid
        (the 1079-grid trapezoid carries O(dt^2 |lambda|) ~ 1e-6
        discretization error; nearest-grid lookup is worse still)."""
        return np.exp(-0.5 * us) / (2.0 * np.pi) \
            * _trapz(g3_line_fine * np.exp(-1j * us * tgrid_fine), tgrid_fine)

    Nt_fine = 4 * Nt
    tgrid_fine = np.linspace(-T, T, Nt_fine)
    qf = 0.25 + tgrid_fine * tgrid_fine
    g3_line_fine = float(norm_mp) * qf * (tgrid_fine * tgrid_fine) \
        * np.exp((-d2 + 1j * mu) * qf)

    def phi_brom_coarse(us):
        return np.exp(-0.5 * us) / (2.0 * np.pi) \
            * _trapz(g3_line * np.exp(-1j * us * tgrid), tgrid)

    # G1 (AMENDED after three F-C firings; see record 1086 s6): two legs.
    # G1a ROUND-TRIP (definitional): M[phi_cf](s) == g_3(s) against the
    #     IMPORTED make_g3, at two complex s (the same check that validated
    #     the rig's own Bromwich object in 1078).
    # G1b SAME-POINT vs the Bromwich reference, with tolerance max(1e-6,
    #     2 x the reference's own grid-convergence residual).
    ug_rt = np.linspace(-u_max, u_max, 24001)
    p_rt = phi_cf(ug_rt)
    rt_rel = 0.0
    for sname, ss in (("0.3+0.4i", 0.3 + 0.4j),
                      ("rho2", BETA + 1j * gamma_2)):
        Mc = complex(_trapz(np.exp(ss * ug_rt) * p_rt, ug_rt))
        gm = complex(g3h(mpf(repr(ss.real)) + 1j * mpf(repr(ss.imag))))
        rt_rel = max(rt_rel, abs(Mc - gm) / abs(gm))
        print(f"G1a|roundtrip s={sname}|M[phi_cf]={Mc.real:.9e}"
              f"{Mc.imag:+.9e}j|g3={gm.real:.9e}{gm.imag:+.9e}j"
              f"|rel={abs(Mc - gm) / abs(gm):.2e}  (<= 1e-8)", flush=True)
    g1a = rt_rel <= 1e-8

    samples = [0.0, 0.3 * A, -0.3 * A, 0.6 * A, -0.6 * A, 0.9 * A, -0.9 * A,
               1.2 * A, -1.2 * A, 1.5 * A, -1.5 * A, 2.0 * A, -2.0 * A,
               3.0 * A, -3.0 * A]
    peak = float(np.max(np.abs(phi_brom)))
    maxrel = 0.0
    maxself = 0.0
    for us in samples:
        ref = phi_brom_exact(us)
        ref_c = phi_brom_coarse(us)
        if abs(ref) < 1e-12 * peak:
            continue
        maxrel = max(maxrel, abs(phi_cf(us) - ref) / abs(ref))
        maxself = max(maxself, abs(ref_c - ref) / abs(ref))
    g1b = maxrel <= max(1e-6, 2.0 * maxself)
    g1 = g1a and g1b
    print(f"G1b|closed-form vs Bromwich(fine)|maxrel={maxrel:.3e} over "
          f"{len(samples)} samples|ref self-conv={maxself:.3e}"
          f"|peak={peak:.3e}  "
          f"(<= max(1e-6, 2*self)) {'PASS' if g1b else 'FAIL'}", flush=True)
    print(f"G1|combined|{'PASS' if g1 else 'FAIL'}", flush=True)
    if not g1:
        print("=== VERDICT: F-C (closed form wrong; fix before anything) ===",
              flush=True)
        return

    # ---- G2: the 1079 pipeline verbatim (hard truncation + polynomial bumps) ---
    def Gwin(s):
        z = complex(s) - 0.5 - 1j * tgrid
        kern = A * np.sinc(1j * (z * A) / np.pi)     # sinh(z a)/z, limit-safe
        return complex(_trapz(g3_line * kern, tgrid) / np.pi)

    def Gwin_hp(s):
        a_mp = mpf(str(A))

        def f(t):
            z = s - mpf("0.5") - 1j * t
            k = a_mp if abs(z) < mpf("1e-20") else mp.sinh(z * a_mp) / z
            return g3h(mpf("0.5") + 1j * t) * k
        return complex(mp.quad(f, [-mpf(str(T)), 0, mpf(str(T))]) / mpi)

    a2 = A * A

    def Hm_poly_hp(m, s):
        f = lambda u: (u ** m) * ((A * A - u * u) ** 2) * mexp(s * u)
        return mp.quad(f, [-mpf(str(A)), 0, mpf(str(A))])

    nodes_mp = [mpf(0), mpf("0.5"), mpf(1)]
    Gn = [Gwin_hp(s) for s in nodes_mp]
    Mmat = mp.matrix([[Hm_poly_hp(m, s) for m in (0, 1, 2)] for s in nodes_mp])
    cvec = mp.lu_solve(Mmat, mp.matrix([-g for g in Gn]))
    resid_1079 = max(abs(complex(Gn[j])
                         + sum(Mmat[j, m] * cvec[m] for m in (0, 1, 2)))
                     for j in range(3))
    cfl = np.array([complex(x) for x in cvec])

    gam = zero_cache(120.0)
    gam_np = np.array([float(g) for g in gam])
    ncov = int(np.searchsorted(gam_np, 120.0))

    def Hm_poly(m, s):
        sc = complex(s)
        return complex(np.dot(A * _WG, (A * _XG) ** m * (a2 - (A * _XG) ** 2) ** 2
                              * np.exp(sc * A * _XG)))

    Gw = np.array([Gwin(0.5 + 1j * g) for g in gam_np[:ncov]])
    Hl = np.array([[Hm_poly(m, 0.5 + 1j * g) for g in gam_np[:ncov]]
                   for m in (0, 1, 2)])
    Hsum = cfl[0] * Hl[0] + cfl[1] * Hl[1] + cfl[2] * Hl[2]
    Gnew = Gw + Hsum
    rows = 2.0 * np.abs(Gnew) ** 2
    margin0 = float(np.sum(rows))
    P2 = float(rows[1])
    rho2 = complex(BETA) + 1j * gamma_2
    H_rho2 = complex(np.dot(cfl, np.array([Hm_poly(m, rho2) for m in (0, 1, 2)])))
    G_rho = Gwin(rho2) + H_rho2
    Acr = float(4.0 * (G_rho ** 2).real)
    lever = float(4.0 * abs(G_rho) ** 2)
    fl2_1079 = margin0 + Acr - P2
    g2_ok = abs(fl2_1079 - M1079_FL2) <= 2e-2
    print(f"G2|1079 anchor repro|fl2={fl2_1079:.6f} vs {M1079_FL2}"
          f"|node_resid={float(resid_1079):.2e}  "
          f"{'PASS' if g2_ok else 'FAIL'}", flush=True)

    # ---- G3-G5: the smooth carrier ----------------------------------------------
    ugrid_w = np.linspace(-A, A, N_U)
    du = ugrid_w[1] - ugrid_w[0]

    def gl_line_values(hfun, s):
        sc = complex(s)
        return complex(np.dot(A * _WG, hfun(A * _XG) * np.exp(sc * A * _XG)))

    def arch_pieces(hu, tag):
        """arch of the object sampled on the dense grid (design record s4)."""
        F0 = float(_trapz(np.abs(hu) ** 2, ugrid_w))
        L = 1 << int(np.ceil(np.log2(2 * N_U)))
        padded = np.zeros(L, dtype=complex)
        padded[:N_U] = hu
        # circular autocorrelation: c = ifft(|fft|^2) EXACTLY (no extra
        # factor; np.fft.ifft already carries the 1/L)
        R = np.fft.ifft(np.fft.fft(padded) * np.conj(np.fft.fft(padded)))
        tie = 0.0
        for k in (1, 7, 701):
            bf = np.dot(np.conj(hu[:N_U - k]), hu[k:]) * du
            tie = max(tie, abs(R[k] * du - bf))
        ymax = 2 * A
        K = int(round(ymax / du))
        ks = np.arange(1, K + 1)
        ys = ks * du
        Fy = R[ks].real * du
        imag_leak = float(np.max(np.abs(R[ks].imag)) * du / max(F0, 1e-300))
        Iy = (np.exp(ys / 2) * 2 * Fy - 2 * F0) / (np.exp(ys) - np.exp(-ys))
        window = float(_trapz(Iy, ys))
        # tail (Lean numerator is e^{y/2}(F y + F -y) - 2 F 0, so the F = 0
        # region contributes -2 F0 / sinh y):
        # -2 F0 * int_{2a}^oo dy/sinh y = 2 F0 * log(tanh a)   [int dy/sinh y
        # = log tanh(y/2)]
        tail = 2.0 * F0 * float(mlog(mtanh(mpf(str(A)))))
        arch = C0 * F0 + window + tail
        print(f"arch[{tag}]|arch={arch:.6f}|F0={F0:.6f}"
              f"|c0F0={C0 * F0:.6f}|window={window:.6f}|tail={tail:.6f}"
              f"|corr_tie={tie:.1e}|imag_leak={imag_leak:.1e}", flush=True)
        return arch, F0

    verdict = {}
    for r in RS:
        ra = r * A

        def h0_fun(u):
            arr = np.asarray(u, dtype=float)
            return (bsmooth(arr / ra) / _B0) * phi_cf(arr)

        def bfun(m):
            def f(u):
                arr = np.asarray(u, dtype=float)
                return (arr ** m) * (bsmooth(arr / ra) / _B0)
            return f

        def smooth_H_hp(m, s):
            rb = mpf(str(ra))

            def f(u):
                return ((u ** m) * (bsmooth_hp(u / rb) / bsmooth_hp(mpf(0)))
                        * mexp(s * u))
            return mp.quad(f, [-mpf(str(A)), 0, mpf(str(A))])

        # hp node values of h0 (closed form makes this a smooth 1-D quad)
        G0_hp = []
        for s in nodes_mp:
            sh = s

            def f0(u, sh=sh):
                return (mexp(sh * u) * (bsmooth_hp(u / mpf(str(ra)))
                                        / bsmooth_hp(mpf(0))) * phi_cf_hp(u))
            G0_hp.append(complex(mp.quad(f0, [-mpf(str(A)), 0, mpf(str(A))])))

        G0_fl = [gl_line_values(h0_fun, float(s)) for s in nodes_mp]
        rel_nodes = max(abs(a - b) / max(abs(b), 1e-30)
                        for a, b in zip(G0_fl, G0_hp))

        Msm = mp.matrix([[smooth_H_hp(m, s) for m in (0, 1, 2)] for s in nodes_mp])
        csv = mp.lu_solve(Msm, mp.matrix([-g for g in G0_hp]))
        res_r = max(abs(complex(G0_hp[j])
                        + sum(Msm[j, m] * csv[m] for m in (0, 1, 2)))
                    for j in range(3))
        csm = np.array([complex(x) for x in csv])

        hp1 = complex(mp.quad(lambda u: u * (bsmooth_hp(u / mpf(str(ra)))
                                             / bsmooth_hp(mpf(0)))
                              * mexp(mpf("0.5") * u),
                              [-mpf(str(A)), 0, mpf(str(A))]))
        rel_basis = abs(hp1 - gl_line_values(bfun(1), 0.5)) / max(abs(hp1), 1e-30)

        G0_rho2 = gl_line_values(h0_fun, rho2)
        Hrho = [gl_line_values(bfun(m), rho2) for m in (0, 1, 2)]
        Hl_r = np.array([[gl_line_values(bfun(m), 0.5 + 1j * g)
                          for g in gam_np[:ncov]] for m in (0, 1, 2)])
        G0_line = np.array([gl_line_values(h0_fun, 0.5 + 1j * g)
                            for g in gam_np[:ncov]])

        hc = h0_fun(ugrid_w) + sum(csm[m] * bfun(m)(ugrid_w) for m in (0, 1, 2))
        hw = sum(csm[m] * bfun(m)(ugrid_w) for m in (0, 1, 2))

        Gc_rho2 = G0_rho2 + sum(csm[m] * Hrho[m] for m in (0, 1, 2))
        detection = abs(Gc_rho2)
        Gc = G0_line + sum(csm[m] * Hl_r[m] for m in (0, 1, 2))
        rows_c = 2.0 * np.abs(Gc) ** 2
        m0c = float(np.sum(rows_c))
        P2c = float(rows_c[1])
        Acr_c = float(4.0 * (Gc_rho2 ** 2).real)
        lever_c = float(4.0 * abs(Gc_rho2) ** 2)
        fl2_c = m0c + Acr_c - P2c

        gbig = float(gam_np[ncov - 1])
        dense = complex(_trapz(h0_fun(ugrid_w)
                               * np.exp((0.5 + 1j * gbig) * ugrid_w), ugrid_w))
        rel_res = abs(dense - G0_line[-1]) / max(abs(dense), 1e-30)

        g3_ok = (float(res_r) <= 1e-9) and (detection >= 0.3) and (rel_res <= 1e-6)
        g4_ok = fl2_c < 0.0
        arch_c, F0_c = arch_pieces(hc, f"h_c r={r:.2f}")
        arch_0, _ = arch_pieces(h0_fun(ugrid_w), f"h0  r={r:.2f}")
        arch_w, _ = arch_pieces(hw, f"w   r={r:.2f}")
        g5_ok = (arch_c > 0.0) and (arch_c >= 1e-3 * C0 * F0_c)

        print(f"r={r:.2f}|node_resid={float(res_r):.2e}|nodes_fl_vs_hp={rel_nodes:.2e}"
              f"|rel_basis={rel_basis:.2e}|rel_resol={rel_res:.2e}"
              f"|detect={detection:.4f}|fl2={fl2_c:.4f}|margin0={m0c:.4f}"
              f"|lever={lever_c:.4f}"
              f"|G3={'PASS' if g3_ok else 'FAIL'}"
              f"|G4={'PASS' if g4_ok else 'FAIL'}"
              f"|G5={'PASS' if g5_ok else 'FAIL'}", flush=True)
        verdict[r] = (g3_ok, g4_ok, g5_ok, arch_c)

        if HP:
            rb = mpf(str(ra))

            def hh(u):
                acc = ((bsmooth_hp(u / rb) / bsmooth_hp(mpf(0))) * phi_cf_hp(u))
                for m in (0, 1, 2):
                    acc = acc + csm[m] * (u ** m) * (bsmooth_hp(u / rb)
                                                     / bsmooth_hp(mpf(0)))
                return acc

            F0_hp = mp.quad(lambda s: abs(hh(s)) ** 2, [-mpf(str(A)), 0, mpf(str(A))])
            rel_F0 = abs(F0_hp - F0_c) / F0_hp

            # float64 autocorrelation of hc once, reused for the y spot-checks
            # (same no-extra-factor convention as arch_pieces)
            L = 1 << int(np.ceil(np.log2(2 * N_U)))
            padded = np.zeros(L, dtype=complex)
            padded[:N_U] = hc
            R = np.fft.ifft(np.fft.fft(padded) * np.conj(np.fft.fft(padded)))
            ys = np.arange(1, int(round(2 * A / du)) + 1) * du
            yv = [0.02, 0.35, 0.68]
            for y in yv:
                y_mp = mpf(str(y))
                Fy_hp = mp.quad(lambda s: mp.conj(hh(s)) * hh(s + y_mp),
                                [-mpf(str(A)), mpf(str(A - y))])
                I_hp = (mexp(y_mp / 2) * 2 * mp.re(Fy_hp) - 2 * F0_hp) \
                    / (mexp(y_mp) - mexp(-y_mp))
                idx = int(np.argmin(np.abs(ys - y)))
                Fy_fl = R[idx].real * du
                I_fl = ((np.exp(ys[idx] / 2) * 2 * Fy_fl - 2 * F0_c)
                        / (np.exp(ys[idx]) - np.exp(-ys[idx])))
                rel_I = abs(I_hp - I_fl) / max(abs(I_hp), mpf("1e-30"))
                print(f"r={r:.2f}|HP|y={y}|I_hp={float(I_hp):.8f}"
                      f"|I_fl={float(I_fl):.8f}|rel={float(rel_I):.2e}  (<= 1e-6)",
                      flush=True)
            print(f"r={r:.2f}|HP|F0_hp={float(F0_hp):.8f}|F0_fl={F0_c:.8f}"
                  f"|rel={float(rel_F0):.2e}  (<= 1e-6)", flush=True)

    # ---- verdict branch ----------------------------------------------------------
    any_pass = any(g3 and g4 and g5 for (g3, g4, g5, _) in verdict.values())
    all_arch_neg = all(arch <= 0 for (_, _, _, arch) in verdict.values())
    print("\n=== VERDICT BRANCH ===", flush=True)
    print(f"  G1 closed-form: {'PASS' if g1 else 'FAIL'}", flush=True)
    print(f"  G2 anchor repro: {'PASS' if g2_ok else 'FAIL'}", flush=True)
    for r, (g3, g4, g5, arch) in verdict.items():
        print(f"  r={r:.2f}: G3={'PASS' if g3 else 'FAIL'}"
              f" G4={'PASS' if g4 else 'FAIL'}"
              f" G5={'PASS' if g5 else 'FAIL'} arch={arch:.6f}", flush=True)
    if any_pass:
        print("  => F-A: proceed to the B1 Lean carrier brick", flush=True)
    elif all_arch_neg:
        print("  => F-B: gate quantity NOT positive at any taper -", flush=True)
        print("     surrogate evidence does not certify the gate; freeze", flush=True)
    else:
        print("  => F-B* (mixed): legality/continuity gates failed;", flush=True)
        print("     hand-write the verdict from the rows", flush=True)


if __name__ == "__main__":
    run()
