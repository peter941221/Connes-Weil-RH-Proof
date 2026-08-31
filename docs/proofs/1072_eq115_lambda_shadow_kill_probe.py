# 1072 - B (lambda*-shadow) cheap kill probe (eq-115 table + archimedean chi).
#
# Design record: 1072_eq115_lambda_shadow_kill.md (fork B-K1/B-K2/B-K3 stated
# BEFORE the run).  Follows 1069 (SIDE = B cheap kill).
#
# Objects (pinned, record s1):
#   tau(lam,x)  = (lam/L) [1 + 2 sum_{n<=m} (cos(2 pi n x/L)
#                                     - d_n cos(2 pi alpha_n x/L))]   (tex:1617)
#   T/lam       = I - sum d_n P_{alpha_n} on L^2([-L/2, L/2]), L = log 2
#                 (v_n)_j = sin(pi (alpha_n - j)) / (pi (alpha_n - j))     (opT)
#   chi(x)      = Qeps(e^x),  Qeps(rho) = sum_{k=0}^{10}
#                 lam_k/sqrt(1-lam_k^2) T_k(rho)                 (tex:1567/169)
#   lam_k       = (-1)^k sqrt(concentration eig), 1062 corrected convention
#   E(lam; m)   = int_0^L |tau - chi| dx   (convex in lam);  lam*(m) = argmin
#   2 eps'(1+) is a positive constant: rescales E, not argmin -> set to 1.
#
# NO zeta-zero input exists in this pipeline (the B-kill structural fact).
#
# Run (WSL, ONE command, log on the Linux side):
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
SECOND_GAP_PAPER = 0.227784          # pinned by record 1057
KMAX = 10                            # the paper's 11-term Qeps


def load_table():
    """Exact-rational angles/coefficients from the committed manifest."""
    with open("scripts/cc20_eq115/data/cc20_eq115_manifest.json",
              encoding="utf-8") as fh:
        man = json.load(fh)
    ang = sorted(man["angles"], key=lambda r: r["index"])
    coef = sorted(man["coefficients"], key=lambda r: r["index"])
    m = int(man["m"])
    assert m == 1732 and len(ang) >= m and len(coef) >= m
    alphas = np.array([int(r["numerator"]) / int(r["denominator"])
                       for r in ang[:m]])
    ds = np.array([int(r["numerator"]) / int(r["denominator"])
                   for r in coef[:m]])
    print(f"MANIFEST|entries={m}|alpha_1={alphas[0]:.13f}|d_1={ds[0]:.13f}"
          f"|GATE-PASS", flush=True)
    return alphas, ds, m


def concentration_eigs(M):
    """Collocation spectrum of the sinc kernel sin(2 pi (x-y))/(pi (x-y)) on
    [-1,1] (the concentration operator P_1 F P_1 F)."""
    nodes, weights = np.polynomial.legendre.leggauss(M)
    r = np.sqrt(weights)
    dx = nodes[:, None] - nodes[None, :]
    K = np.sinc(2.0 * dx)          # np.sinc(u) = sin(pi u)/(pi u)
    A = r[:, None] * K * r[None, :]
    ev, evec = np.linalg.eigh(A)
    lam = ev[::-1]
    vecs = evec[:, ::-1]
    flip = np.arange(M)[::-1]
    parity = np.sign((vecs[flip, :] * r[:, None] * vecs * r[:, None]).sum(0))
    return lam, parity


def signed_prolate():
    """lam_k = (-1)^k sqrt(mu_k), even-parity branch, k = 0..KMAX."""
    lam100, par100 = concentration_eigs(100)
    even100 = lam100[par100[:len(lam100)] > 0][:KMAX + 1]
    lam140, par140 = concentration_eigs(140)
    even140 = lam140[par140[:len(lam140)] > 0][:KMAX + 1]
    err = np.max(np.abs(even100 - even140))
    print(f"LAMK-XCHK|M100-vs-M140|max={err:.2e}  (gate <= 1e-10)", flush=True)
    assert err < 1e-10, "collocation not converged"
    vals = np.array([(-1) ** k * np.sqrt(max(even100[k], 0.0))
                     for k in range(KMAX + 1)])
    paper5 = [0.999971, -0.979485, 0.524086, -0.0589766]
    perr = max(abs(vals[k] - paper5[k]) for k in range(4))
    print(f"LAMK-XCHK|signed lam_0..3 vs 1057/1062 list|max={perr:.2e}  "
          f"(gate <= 1e-5)|vals={np.array2string(vals[:5], precision=6)}",
          flush=True)
    assert perr < 1e-5, "signed prolate convention mismatch"
    return vals


def qeps_mpmath(rho, lamk):
    """Qeps(rho) at 40 dps; T_k(rho) = cosh(k acosh rho) for rho >= 1."""
    s = mp.mpf(0)
    for k in range(KMAX + 1):
        c = mp.mpf(float(lamk[k])) / mp.sqrt(1 - mp.mpf(float(lamk[k])) ** 2)
        s += c * mp.cosh(k * mp.acosh(mp.mpf(float(rho))))
    return s


def build_chi(xgrid):
    """chi on the grid, float64, with an mpmath cross-check."""
    lamk = signed_prolate()
    k = np.arange(KMAX + 1)
    c = lamk / np.sqrt(1.0 - lamk ** 2)
    rho = np.exp(xgrid)
    ac = np.arccosh(rho)
    # T_k(rho) = cosh(k acosh(rho)): outer product (len(grid) x 11)
    T = np.cosh(np.outer(ac, k))
    chi = T @ c
    errs = []
    for i0 in (0, len(xgrid) // 4, len(xgrid) // 2, 3 * len(xgrid) // 4,
               len(xgrid) - 1):
        ref = float(qeps_mpmath(rho[i0], lamk))
        errs.append(abs(chi[i0] - ref) / max(abs(ref), 1e-30))
    emax = max(errs)
    print(f"CHI-XCHK|float64-vs-mpmath|5 pts|max={emax:.2e}  (gate <= 1e-9)",
          flush=True)
    assert emax < 1e-9, "chi float64 construction failed its cross-check"
    return chi


def tau_shape(xgrid, alphas, ds, m):
    """A(x) = tau(1, x)/lam = (1/L)[1 + 2 sum (cos - d_n cos(alpha_n))]."""
    n = np.arange(1, m + 1)
    ph = 2.0 * np.pi / L
    # outer: grid x n may be big (4001 x 1732 = 7e6 entries, fine)
    C1 = np.cos(np.outer(xgrid, ph * n))
    C2 = np.cos(np.outer(xgrid, ph * alphas))
    return (1.0 + 2.0 * (C1.sum(1) - ds * C2).sum(1)) / L


def energy(lam, Ashape, chi, xgrid):
    return np.trapezoid(np.abs(lam * Ashape - chi), xgrid)


def argmin_lambda(Ashape, chi, xgrid):
    r = opt.minimize_scalar(
        lambda lam: energy(lam, Ashape, chi, xgrid),
        bounds=(1.0, 1.2), method="bounded",
        options={"xatol": 1e-9})
    # convexity cross-check: fine-grid argmin
    grid = np.linspace(1.0, 1.2, 20001)
    vals = [energy(l, Ashape, chi, xgrid) for l in grid]
    lamg = grid[int(np.argmin(vals))]
    ok = abs(r.x - lamg) < 1e-5
    print(f"CONVEXITY|brent={r.x:.7f}|grid={lamg:.7f}|agree={ok}", flush=True)
    assert ok, "E landscape not convex at certificate scale"
    return r.x


def t_spectrum(alphas, ds, m, lam):
    """Compressed spectrum of (1/lam) T = I - sum d_n P_{alpha_n}: eigenvalues
    {1 (mult N-m)} u {1 - eig(G)}, G = D^{1/2} V^T V D^{1/2} (m x m)."""
    J = m
    j = np.arange(-J, J + 1)
    V = np.sinc(alphas[None, :] - j[:, None])  # sin(pi u)/(pi u), (2J+1) x m
    G = (np.sqrt(ds)[:, None] * (V.T @ V) * np.sqrt(ds)[None, :])
    eigG = np.linalg.eigvalsh(G)
    compressed = np.concatenate(([1.0], 1.0 - eigG[::-1]))
    top = np.sort(compressed)[::-1][:6]
    paper = np.array([1.0, 0.652824, 0.027475, 0.000290146,
                      0.0000877245, 0.0000756436])       # tex:1713-1730, m=1733
    err = np.max(np.abs(top - paper))
    print(f"TSPEC|lam={lam}|top-of-(1/lam)T = "
          f"{np.array2string(top, precision=6)}", flush=True)
    print(f"TSPEC|paper list (m=1733)     = "
          f"{np.array2string(paper, precision=6)}", flush=True)
    print(f"TSPEC|top-3 max abs err = {err:.2e}  (gate <= 5e-3)"
          f"|lam*0.652824 = {lam * paper[1]:.6f} (paper lam_2 = 0.686494)",
          flush=True)
    assert err < 5e-3, "compressed spectrum does not reproduce the paper list"
    return top, 1.0 - top[1]


def run():
    print("=== 1072 B (lambda*-shadow) kill probe ===", flush=True)
    alphas, ds, m_full = load_table()
    xgrid = np.linspace(0.0, L, 4001)
    chi = build_chi(xgrid)

    print("\n=== T-spectrum validation at the paper scale ===", flush=True)
    t_spectrum(alphas, ds, m_full, LAM_PAPER)

    print("\n=== the kill measurement: lambda*(m) trajectory ===", flush=True)
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
    print(f"KILL|trajectory={ {m: round(v, 6) for m, v in lamstars.items()} }"
          f"|max drift vs m={MS[-1]}: {drift:.6f}", flush=True)

    print("\n=== sensitivity: what the fit scale actually responds to ===",
          flush=True)
    Ashape = tau_shape(xgrid, alphas, ds, m_full)
    base = argmin_lambda(Ashape, chi, xgrid)
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

    print("=== done: grep 'MANIFEST|LAMK|CHI|TSPEC|KILL|SENS|CONVEXITY' ===",
          flush=True)


if __name__ == "__main__":
    run()
