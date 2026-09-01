"""1079 - windowed node-restoring correction: does the 25% sign margin absorb it?

Pre-registered fork: docs/proofs/1079_windowed_node_correction.md (BEFORE any run).

Object chain (1078 verdict): g_3 (1077 fired) -> Bromwich c=1/2 -> phi (Schwartz)
-> hard truncate -> phi_win keeps the field-#4 sign (sink 25.46%) but LOSES the
exact triple vanishing (node residuals ~12.5% of peak).  Arm 1 here builds the
MINIMAL correction  h = c_0 h_0 + c_1 h_1 + c_2 h_2,  h_m = u^m (a^2-u^2)^2
1_{|u|<=a},  with  Sigma c_m H_m(s_j) = -G_win(s_j)  at {0, 1/2, 1}  (3x3 mpmath
solve at dps 30), so G_new = G_win + H has EXACT node zeros; then re-evaluates
fl_j = margin0 + A - P_j  (rows_j = 2|G_new(1/2+i gamma_j)|^2, A = 4 Re
G_new(rho_2)^2) at zero #2 (target) and zero #3 (control), fired config
cd=1.5, beta=0.49.  Arm 2 (pre-registered fallback, only if arm 1 fails):
one kernel-steering null direction + multiplier scan, best achievable fl_2.

Key identity (kills the nested quadrature):
   G_win(s) = (1/pi) Int_{-T}^{T} g_3(1/2+it) sinh((s-1/2-it)a)/(s-1/2-it) dt,
the kernel evaluated limit-safely as  a * sinc(i (s-1/2-it) a / pi).

Run (WSL):
  MSYS_NO_PATHCONV=1 wsl.exe --cd /mnt/c/Projects/Connes-Weil-RH-Proof sh -c \
    '/home/peter/.local/bin/uv run --with numpy --with mpmath \
     python -u docs/proofs/1079_windowed_node_correction_probe.py \
     > /home/peter/1079_probe.log 2>&1'
"""

import os
import importlib.util

import numpy as np
from mpmath import mp, mpf, exp as mexp, log as mlog, pi as mpi
from mpmath import sinh as msinh


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {name} from {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_here = os.path.dirname(os.path.abspath(__file__))
p1077 = _load("p1077", os.path.join(_here, "1077_pinned_detector_sign_probe.py"))

make_g3 = p1077.make_g3              # g_3 closed form (mpmath), (delta, norm, mu)
normalize_family3 = p1077.normalize_family3
mu_3_star = p1077.mu_3_star
zero_cache = p1077.zero_cache

mp.dps = 30

_trapz = getattr(np, "trapezoid", None) or np.trapz   # numpy>=2 renamed trapz

CD = float(os.environ.get("CD_1079", "1.50"))          # fired config (1077)
BETA = float(os.environ.get("BETA_1079", "0.49"))

# 1078 authoritative values the tie-in gates compare against (bit-for-bit log)
M1078 = {
    "margin0": 4.318617,
    "P2": 1.736144,
    "G_rho2": -0.000946 + 0.930687j,
    "nodes": [1.173e-01, 1.152e-01, 1.173e-01],        # G_win at {0, 1/2, 1}
}


def run():
    print("=== 1079 windowed node-restoring correction (zero #2; arm 1 minimal) ===",
          flush=True)
    import mpmath as _mp
    g2 = mp.im(_mp.zetazero(2))
    gamma_2 = float(g2)
    delta = CD / gamma_2
    d2 = delta * delta
    norm, _ = normalize_family3(delta)                 # peak_t |g_3(1/2+it)| = 1
    mu_mp = mu_3_star(mpf(str(CD)) / g2, BETA, g2)
    mu = float(mu_mp)
    a = mlog(mpf(2)) / 2                               # root-window half-width
    af = float(a)
    T = 10.0 / delta
    Nt = 8192

    print(f"cfg|cd={CD}|beta={BETA}|gamma2={gamma_2:.5f}|delta={delta:.6f}"
          f"|d2={d2:.6e}|N'={float(norm):.6e}|mu*={mu:.6f}"
          f"|a=log2/2={af:.6f}|T={T:.3f}|Nt={Nt}", flush=True)

    # ---- on-line g_3 line (float64) + self-consistency gate ---------------------
    tgrid = np.linspace(-T, T, Nt)
    q = 0.25 + tgrid * tgrid
    # vf0(s) = s(s-1)  =>  on line: (-q) * (-(t^2)) = +q t^2   (NOT s(1-s); see
    # 1071:41 and the 1077 make_g3 docstring erratum fixed in this round)
    g3_line = float(norm) * q * (tgrid * tgrid) * np.exp((-d2 + 1j * mu) * q)

    g3h = make_g3(delta, norm, mu_mp)
    t_probe = mpf(str(gamma_2))
    ref = complex(g3h(mpf("0.5") + 1j * t_probe))
    qp = 0.25 + gamma_2 * gamma_2
    npl = complex(float(norm) * qp * (gamma_2 * gamma_2)
                  * np.exp((-d2 + 1j * mu) * qp))
    rel_g = abs(npl - ref) / abs(ref)
    print(f"GATE|g3 self-consistency np vs mpmath at t=gamma2|rel={rel_g:.3e}  (<= 1e-8)",
          flush=True)

    # ---- closed-form kernel for the TRUNCATED object G_win ----------------------
    def Gwin(s):
        z = complex(s) - 0.5 - 1j * tgrid
        kern = af * np.sinc(1j * (z * af) / np.pi)     # = sinh(z a)/z, limit-safe
        return complex(_trapz(g3_line * kern, tgrid) / np.pi)

    def Gwin_hp(s):
        g3t = lambda t: g3h(mpf("0.5") + 1j * t)

        def f(t):
            z = s - mpf("0.5") - 1j * t
            k = a if abs(z) < mpf("1e-20") else msinh(z * a) / z
            return g3t(t) * k
        return mp.quad(f, [-mpf(T), 0, mpf(T)]) / mpi

    # ---- basis Mellin transforms  H_m(s) = Int u^m (a^2-u^2)^2 e^{su} du --------
    xg, wg = np.polynomial.legendre.leggauss(200)
    ug = af * xg
    wgl = af * wg
    bump = (af * af - ug * ug) ** 2

    def Hm(m, s):
        sc = complex(s)
        return complex(np.dot(wgl, (ug ** m) * bump * np.exp(sc * ug)))

    a2 = a * a

    def Hm_hp(m, s):
        f = lambda u: (u ** m) * ((a2 - u * u) ** 2) * mexp(s * u)
        return mp.quad(f, [-a, 0, a])

    # hp-vs-GL cross-check on one element
    x0 = Hm_hp(1, mpf("0.5") + 1j * g2)
    x1 = Hm(1, 0.5 + 1j * gamma_2)
    rel_h = abs(complex(x0) - x1) / abs(x1)
    print(f"GATE|H basis hp vs Gauss-Legendre|rel={rel_h:.3e}  (<= 1e-10)", flush=True)

    # ---- ARM 1: minimal 3-term correction ---------------------------------------
    nodes = [mpf(0), mpf("0.5"), mpf(1)]
    Gn = [Gwin_hp(s) for s in nodes]
    node_rows = []
    for sj, gv, ref1078 in zip(("0", "1/2", "1"), Gn, M1078["nodes"]):
        rel = abs(complex(gv) - ref1078) / ref1078
        node_rows.append(f"G_win({sj})={complex(gv).real:.6f}|rel_vs_1078={rel:.3e}")
    ok_n = all(abs(complex(g) - r) / r <= 5e-2 for g, r in zip(Gn, M1078["nodes"]))
    print("GATE|N hp nodes vs 1078 grid (sanity tie; kink-dominated u-grid error)|"
          + " ".join(node_rows) + f"  (<= 5e-2) {'PASS' if ok_n else 'FAIL'}", flush=True)
    qres = max(abs(complex(Gwin(sj)) - complex(gj)) / abs(complex(gj))
               for sj, gj in zip(nodes, Gn))
    print(f"GATE|Q float64 kernel self-tie at nodes|maxrel={float(qres):.3e}  (<= 1e-3)",
          flush=True)

    # rows = nodes (j), cols = basis (m): lu_solve solves  Sigma_m M[j,m] c_m = -G(s_j)
    Mmat = mp.matrix([[Hm_hp(m, s) for m in (0, 1, 2)] for s in nodes])
    cvec = mp.lu_solve(Mmat, mp.matrix([-g for g in Gn]))
    cond = float(np.linalg.cond(np.array(Mmat.tolist(), dtype=complex)))
    print(f"arm1|cond(3x3)={cond:.3e}" + ("  (<= 1e8)" if cond <= 1e8 else "  ILL"),
          flush=True)

    cfl = np.array([complex(x) for x in cvec])
    resid = max(abs(complex(Gn[j]) + sum(Mmat[j, m] * cvec[m] for m in (0, 1, 2)))
                for j in range(3))
    print(f"NODE-GATE|corrected node residual max={float(resid):.3e}  (<= 1e-12)", flush=True)

    # ---- pipeline: on-line rows + rho_2 (float64 kernel, tied to 1078) ----------
    cutoff = max(3.0 * gamma_2, 5.0 / delta)
    gmax = min(6000.0, max(cutoff + 2.0, 120.0))
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])
    ncov = int(np.searchsorted(gam_np, cutoff))

    Gw = np.array([Gwin(0.5 + 1j * g) for g in gam_np[:ncov]])   # rows live ON the line
    Hl = np.array([[Hm(m, 0.5 + 1j * g) for g in gam_np[:ncov]] for m in (0, 1, 2)])
    Hsum = cfl[0] * Hl[0] + cfl[1] * Hl[1] + cfl[2] * Hl[2]

    rows_w = 2.0 * np.abs(Gw) ** 2
    margin0_w = float(np.sum(rows_w))
    rel_m = abs(margin0_w - M1078["margin0"]) / M1078["margin0"]
    p2_w = float(rows_w[1])
    rel_p2 = abs(p2_w - M1078["P2"]) / M1078["P2"]
    print(f"GATE|K kernel rows vs 1078|margin0={margin0_w:.6f} (rel {rel_m:.3e})"
          f"|P2={p2_w:.6f} (rel {rel_p2:.3e})  (<= 2e-3)", flush=True)

    rho2 = complex(BETA) + 1j * gamma_2
    Gw_rho2 = Gwin(rho2)
    rel_r = abs(Gw_rho2 - M1078["G_rho2"]) / abs(M1078["G_rho2"])
    print(f"GATE|R G_win(rho2) vs 1078|{Gw_rho2.real:.6f}{Gw_rho2.imag:+.6f}j"
          f"|rel={rel_r:.3e}  (<= 2e-3)", flush=True)

    Gnew = Gw + Hsum
    rows = 2.0 * np.abs(Gnew) ** 2
    margin0 = float(np.sum(rows))
    P2 = float(rows[1])
    P3 = float(rows[2])
    wall = margin0 - P2

    H_rho2 = complex(np.dot(cfl, np.array([Hm(m, rho2) for m in (0, 1, 2)])))
    G_rho = Gw_rho2 + H_rho2
    A = float(4.0 * (G_rho ** 2).real)
    lever = float(4.0 * abs(G_rho) ** 2)
    fl2 = margin0 + A - P2
    fl3 = margin0 + A - P3

    maxH_line = float(np.max(np.abs(Hsum)))
    print(f"arm1|c=[{cfl[0].real:.4f}{cfl[0].imag:+.4f}j "
          f"{cfl[1].real:.4f}{cfl[1].imag:+.4f}j "
          f"{cfl[2].real:.4f}{cfl[2].imag:+.4f}j]"
          f"|max|H_line|={maxH_line:.4f}"
          f"|H(rho2)=|{abs(H_rho2):.4f}| (perturbation sizes)", flush=True)

    print("\n--- CORRECTED object G_new: field #4 sign at zero #2 ---", flush=True)
    print(f"corr|margin0={margin0:.6f}|P2={P2:.6f}|P3={P3:.6f}|A={A:.6f}"
          f"|wall={wall:.6f}|lever={lever:.6f}|fl2={fl2:.6f}|fl3={fl3:.6f}", flush=True)
    print(f"corr|G_new(rho2)={G_rho.real:.6f}{G_rho.imag:+.6f}j"
          f"|detects={abs(G_rho):.4f} (must be != 0)", flush=True)
    wl = wall / lever if lever > 0 else float("inf")
    sinkpct = 100.0 * abs(fl2) / lever if lever > 0 else float("nan")
    o1 = (lever >= np.exp(-2.0)) and (wall >= np.exp(-2.0))
    print(f"corr|wall/lever={wl:.4f}|sink={sinkpct:.2f}% of lever"
          f"|O(1)scale={'Y' if o1 else 'n'}", flush=True)
    print(f"control|j=3 fl3={fl3:.6f} ({'FLIPS' if fl3 < 0 else 'holds'})"
          f"|wall3/lever={(margin0 - P3) / lever:.4f}", flush=True)

    node_ok = float(resid) <= 1e-12
    arm1_ok = node_ok and (fl2 < 0.0) and o1
    branch = "F-A" if arm1_ok else "F-B"

    best = (float("inf"), 0.0, False, float("inf"))
    if not arm1_ok:
        # ---- ARM 2: one kernel-steering direction (pre-registered fallback) -----
        print("\n--- ARM 2: +1 kernel-steering direction (fallback scan) ---", flush=True)
        nodes_np = np.array([0.0, 0.5, 1.0])
        M4 = np.array([[Hm(m, complex(s)) for s in nodes_np] for m in (3, 4, 5, 6)])
        _, _, vh = np.linalg.svd(M4.T)
        v4 = vh[-1]
        res4 = float(np.max(np.abs(M4.T @ v4)))
        print(f"arm2|null-vector node residual={res4:.3e}", flush=True)
        Hl_ext = np.array([[Hm(m, 0.5 + 1j * g) for g in gam_np[:ncov]]
                           for m in (3, 4, 5, 6)])
        Hl4 = v4[0] * Hl_ext[0] + v4[1] * Hl_ext[1] + v4[2] * Hl_ext[2] + v4[3] * Hl_ext[3]
        H4_rho2 = sum(complex(v4[m - 3]) * Hm(m, rho2) for m in (3, 4, 5, 6))
        scale0 = float(max(abs(x) for x in cfl))
        for l in np.linspace(-8.0, 8.0, 65):
            alpha = scale0 * (2.0 ** l)
            G2 = Gnew + alpha * Hl4
            rows2 = 2.0 * np.abs(G2) ** 2
            m0 = float(np.sum(rows2))
            Grho2 = G_rho + alpha * H4_rho2
            A2 = float(4.0 * (Grho2 ** 2).real)
            fl = m0 + A2 - float(rows2[1])
            lev2 = float(4.0 * abs(Grho2) ** 2)
            w2 = m0 - float(rows2[1])
            ok = (w2 >= np.exp(-2.0)) and (lev2 >= np.exp(-2.0))
            if fl < best[0]:
                best = (fl, alpha / scale0, ok, w2 / lev2 if lev2 > 0 else float("inf"))
        print(f"arm2|best fl2={best[0]:.6f} @ alpha/scale={best[1]:.3e}"
              f"|O(1)={'Y' if best[2] else 'n'}|wall/lever={best[3]:.4f}", flush=True)
        if best[0] < 0.0 and best[2]:
            branch = "F-B (arm 2 rescues: steering feasible)"

    print("\n=== VERDICT BRANCH ===", flush=True)
    print(f"  node residual max = {float(resid):.3e}   (F-A wants <= 1e-12)", flush=True)
    print(f"  fl2(corrected) = {fl2:.6f}   (F-A wants < 0)", flush=True)
    print(f"  O(1) clauses = {'Y' if o1 else 'n'};  detects rho2 = {abs(G_rho):.4f}", flush=True)
    print(f"  => preliminary: {branch}   (hand-write the .md verdict from these rows)",
          flush=True)


if __name__ == "__main__":
    run()
