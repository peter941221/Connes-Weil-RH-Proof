# 1055 - Semilocal prolate P2b probe: the precision-wall verdict harness.
#
# Purpose (docs/proofs/1053, docs/proofs/1054): decide the first
# coefficient-complete go/no-go question for the surviving semilocal prolate
# route, whether the archimedean Gamma/Meixner cyclic family cancels the
# iterated first-harmonic second variation
#
#     Delta_lambda = E_lambda''(0) - delta_{cos(2 L s)} E_lambda(0)         (P2b)
#
# as lambda -> infinity. The verdict produced by this harness (record 1055)
# has three separable parts, each backed by its own measurement:
#
#   A. NO generic algebraic cancellation. The exact 1054 three-point
#      counterexample is reproduced by this harness (control_3point, PASS).
#
#   B. THE P2b GATE IS INFEASIBLE AT FIXED PRECISION. Any float64 evaluation
#      of E_lambda'' on this family requires recovering the deformed Jacobi
#      coefficients to depth ~ 4*pi*lambda^2 (the prolate band). The recovery
#      map (cyclic vector -> Jacobi coefficients) for a tridiagonal with
#      a_k ~ k amplifies vector noise by prod_(j<k) a_j ~ sqrt(k) * k!, so at
#      machine precision eps the decodable depth is k* ~ 15-20. The band 4*pi*
#      lambda^2 exceeds k* at lambda ~ 1.1. Measurements below (tail growth,
#      floorK, dE0) show the amplifier operating at every lambda in the
#      scaling regime: the base energy recomputed from a spectrally
#      reconstructed (1e-15 clean) starting vector instead of the exact one
#      changes by 10-1500%, and Lanczos coefficients diverge past a bound
#      impossible for any true Jacobi matrix of the truncation.
#      Hence no fixed-precision numerical experiment - at any lambda where
#      P2b is a nontrivial statement - can supply evidence either way.
#
#   C. The functional whose P2b is in doubt has no proved self-adjoint
#      realization (P0/P1 of 1053); CCM24 gives only the formal expression
#      (5). By 1054 section 5 the kill test becomes meaningful only after
#      P0/P1, and 1053 section 6 forbids any Lean owner until P0, P1, P2b are
#      analytic. Part B shows P2b can never become analytic by computation.
#
# Model, pinned to CCM24 (arXiv:2310.18423, Thm 3.1 / section 3.4): Jacobi
#   offdiag a_n = sqrt((n + 1/2)(n + 1)), diagonal 0;
#   W_lambda = -J^2 + 2*pi*lambda^2*(4N + 1) - 1/4 (formal expression (5));
#   Euler weight w_a = |1 - a exp(i L s)|^{-2}; deformed cyclic pair realized
#   as the Lanczos tridiagonal of J0 started at psi = sqrt(w(J0)) e_0, with
#   the multiplier sqrt(w) applied through the exact eigenbasis of J0.
#   Energy: E = || Pi_-(a) J_a Pi_+(a) ||_HS^2 (smoothed Heaviside
#   implementation, sigma -> infinity recovers the hard projector; see
#   energy_from_coeffs).
#
# Run:  python 1055_semilocal_p2b_probe.py   (writes p2b_probe_results.json)

import json
import math

import numpy as np
from scipy.linalg import eigh_tridiagonal

LAMS = [0.5, 0.7, 0.9, 1.1, 6.0, 12.0]
LS = {"log2": math.log(2.0), "log3": math.log(3.0)}
H = 1e-3          # finite-difference step (the amplifier is h-independent)
EPS = np.finfo(float).eps


def base_jacobi(m):
    """CCM24 section 3.4: offdiag sqrt((n+1/2)(n+1)), diagonal 0."""
    n = np.arange(m - 1) + 1.0
    return np.zeros(m), np.sqrt((n - 0.5) * n)


def eig_base(m):
    diag, off = base_jacobi(m)
    return eigh_tridiagonal(diag, off)


def lanczos(diag, off, v0, m, instrument=False):
    """Lanczos on the tridiagonal (diag, off) of size m from start vector v0.
    FULL reorthogonalization twice: with linearly growing coefficients any
    partial scheme drifts. If instrument, also record the norm of the r
    component in coordinates > k+1, which is exactly 0 in exact arithmetic
    for a tridiagonal J (the tail-growth amplifier)."""
    diag = diag[:m]
    off = off[:m - 1]
    v = np.array(v0[:m], dtype=float)
    v /= np.linalg.norm(v)
    Q = np.zeros((m, m))
    a = np.zeros(m - 1)
    b = np.zeros(m)
    tails = []
    Q[:, 0] = v
    for k in range(m):
        u = Q[:, k]
        Ju = diag * u
        Ju[:-1] += off * u[1:]
        Ju[1:] += off * u[:-1]
        b[k] = float(u @ Ju)
        if k == m - 1:
            break
        r = Ju - b[k] * u
        if k > 0:
            r -= a[k - 1] * Q[:, k - 1]
        for _ in range(2):
            r -= Q[:, :k + 1] @ (Q[:, :k + 1].T @ r)
        if instrument:
            tails.append(float(np.linalg.norm(r[k + 2:])))
        a[k] = float(np.linalg.norm(r))
        Q[:, k + 1] = r / a[k]
    return a, b, tails


def energy_from_coeffs(aoff, b, lam, sigma=1e4):
    """E_sigma = || (I-S) J S ||_HS^2 with S = (1 + tanh(sigma W))/2 the
    smoothed positive spectral projector of W = -J^2 + c(4N+1) - 1/4,
    c = 2 pi lam^2.  sigma -> infinity recovers the hard Pi_- J Pi_+ energy
    of proofs 1053/1054.  NOTE: for the prolate gaps measured here (min
    |eval| >= 225 at lam = 6) sigma = 8 already saturates every weight, so
    the smoothed and hard observables coincide in double precision at every
    lambda in the scaling regime."""
    m = len(b)
    c = 2.0 * math.pi * lam * lam
    n = np.arange(m)
    aj = np.zeros(m)
    aj[: m - 1] = aoff
    ajm1 = np.zeros(m)
    ajm1[1:] = aoff
    diag = -(ajm1**2 + b**2 + aj**2) + c * (4.0 * n + 1.0) - 0.25
    off1 = -(aoff * (b[: m - 1] + b[1:]))
    W = np.diag(diag)
    idx = np.arange(m)
    W[idx[:-1], idx[1:]] = off1
    W[idx[1:], idx[:-1]] = off1
    if m > 2:
        off2 = -(aoff[: m - 2] * aoff[1: m - 1])
        W[idx[:-2], idx[2:]] = off2
        W[idx[2:], idx[:-2]] = off2
    evals, QW = np.linalg.eigh(W)
    JQ = QW * b[:, None]
    JQ[:-1] += aoff[:, None] * QW[1:]
    JQ[1:] += aoff[:, None] * QW[:-1]
    B = QW.T @ JQ
    f = 0.5 * (1.0 + np.tanh(sigma * evals))
    wt = ((1.0 - f) ** 2)[:, None] * (f ** 2)[None, :]
    E = float(np.sum(B * B * wt))
    gap = float(np.min(np.abs(evals)))
    return E, int((evals > 0).sum()), gap


def psi_of(gfun, theta, Qm):
    """gfun(J0) e_0 in the J0 coordinate (orthonormal polynomial) basis:
    J0 = Qm diag(theta) Qm^T, so gfun(J0) e_0 = Qm (gfun(theta) * Qm[0,:])."""
    return Qm @ (gfun(theta) * Qm[0, :])


def euler_sqrt(s, L, a):
    """sqrt(|1 - a e^{i L s}|^{-2}) = |1 - a e^{i L s}|^{-1}."""
    return 1.0 / np.sqrt(1.0 - 2.0 * a * np.cos(L * s) + a * a)


def band_depth(lam):
    """The prolate band: coordinates 0 <= n <= 4*pi*lam^2 carry the W-spectrum
    crossing zero, so E_lambda and its a-derivatives need coefficients to
    roughly this depth."""
    return int(math.ceil(4.0 * math.pi * lam * lam))


# ---------------- measurement 1: exact arithmetic control (claim A) --------
def control_3point():
    """Reproduce the exact 1054 three-point counterexample: atoms {-1,0,1},
    L = pi/2, lambda^2 = 1/(4 pi), x(a) = 2(1-a)^2/(3-4a+3a^2),
    E(x) = 1/2 + (8x-3)/(2 sqrt(9+16x)); closed form (3.3):
    Delta = E_x(-8/27) + E_xx(16/81) < 0."""
    atoms = np.array([-1.0, 0.0, 1.0])

    def orthonormal(dens):
        w = dens / dens.sum()
        V = np.vander(atoms, 3, increasing=True)
        G = V * np.sqrt(w)[:, None]
        Qm = np.linalg.qr(G)[0]
        J = Qm.T @ np.diag(atoms) @ Qm
        return np.diag(J), np.diag(J, 1)

    lam = math.sqrt(1.0 / (4.0 * math.pi))

    def energy(dens):
        b, a = orthonormal(dens)
        return energy_from_coeffs(a, b, lam, sigma=1e4)[0]

    base = np.array([1.0, 1.0, 1.0])
    Lp = math.pi / 2.0
    h = 1e-4
    E0 = energy(base)
    wE = lambda a: np.abs(1.0 - a * np.exp(1j * Lp * atoms)) ** (-2)
    E_pp = (energy(base * wE(h)) - 2 * E0 + energy(base * wE(-h))) / (h * h)
    # delta_{cos(2 L s)} E is the FIRST variation along exp(2 t cos(2 L s))
    # dm (proof 1054 (1.2)-(1.3)): the a^2 Euler-log coefficient enters that
    # path at t = a^2/2.
    wD = lambda t: np.exp(2.0 * t * np.cos(2.0 * Lp * atoms))
    D_dot = (energy(base * wD(h)) - energy(base * wD(-h))) / (2.0 * h)
    delta = E_pp - D_dot

    def closed_form_delta():
        Ex = 16.0 * (13.0 / 3.0) / (59.0 / 3.0) ** 1.5
        Exx = -3104.0 / (3.0 * (59.0 / 3.0) ** 2.5)
        return Ex * (-8.0 / 27.0) + Exx * (16.0 / 81.0)

    ref = closed_form_delta()
    ok = abs(delta - ref) < 0.02 * abs(ref) and (delta < 0) == (ref < 0)
    print(f"A  control: pipeline Delta={delta:.6f} closed-form={ref:.6f} "
          f"-> {'PASS' if ok else 'FAIL'}")
    return ok


# ---------------- measurement 2: the precision wall (claim B) --------------
def tail_growth_demo():
    """Lanczos started at a spectrally reconstructed e_0: print the norm of
    the r-component in coordinates > k+1, which is identically zero in exact
    arithmetic. Its per-step growth is the Pi a_j amplifier."""
    M = 200
    theta, Qm = eig_base(M)
    bD, bO = base_jacobi(M)
    psi = psi_of(lambda t: np.ones_like(t), theta, Qm)
    e0 = np.zeros(M)
    e0[0] = 1.0
    err = np.linalg.norm(psi - e0)
    print(f"B1 tail growth demo (M={M}, start error {err:.2e}):")
    a1, _b1, tails = lanczos(bD, bO, psi, 20, instrument=True)
    print("    k:  " + " ".join(f"{k:>7d}" for k in range(len(tails))))
    print("  tail: " + " ".join(f"{t:7.1e}" for t in tails))
    print("    a:  " + " ".join(f"{v:7.2f}" for v in a1[:len(tails)]))
    print("true a:" + " ".join(f"{v:7.2f}" for v in bO[:len(tails)]))
    a2, b2, _ = lanczos(bD, bO, e0, M)
    maxerr = max(np.abs(a2 - bO[: M - 1]).max(), np.abs(b2).max())
    print(f"    exact-e0 start reproduces base coefficients to {maxerr:.2e} "
          f"over depth {M}: the difference is purely the deep-vector noise")
    return maxerr < 1e-9


def precision_wall():
    """For each lambda: base energy from the exact cyclic vector versus from
    the reconstructed cyclic vector (identical in exact arithmetic, g = 1);
    coefficient-recovery floor at the band depth; amplifier prediction
    eps*sqrt(k!)*sqrt(k) in log10."""
    print("B2 precision wall (g=1: two representations of the SAME base "
          "cyclic vector must give one energy):")
    rows = []
    for lam in LAMS:
        band = band_depth(lam)
        M = band + 140
        theta, Qm = eig_base(M)
        bD, bO = base_jacobi(M)
        e0 = np.zeros(M)
        e0[0] = 1.0
        psiB = psi_of(lambda t: np.ones_like(t), theta, Qm)
        aP, bP, _ = lanczos(bD, bO, psiB, M)
        aE, bE, _ = lanczos(bD, bO, e0, M)
        dK = min(band + 12, M - 2)
        floorK = max(float(np.abs(aP[:dK] - bO[:dK]).max()),
                     float(np.abs(bP[:dK]).max()))
        Ee = energy_from_coeffs(aE[: M - 1], bE, lam)[0]
        Ep = energy_from_coeffs(aP[: M - 1], bP, lam)[0]
        log10_amp = (math.log10(EPS)
                     + math.lgamma(dK + 1.0) / (2.0 * math.log(10.0))
                     + 0.5 * math.log10(dK))
        row = dict(lam=lam, band=band, M=M, E0_exact=Ee, E0_recon=Ep,
                   dE0_rel=abs(Ee - Ep) / Ee, floorK=floorK,
                   log10_amplifier=log10_amp)
        rows.append(row)
        print(f"  lam={lam:5.2f} band={band:4d} E0_exact={Ee:.4e} "
              f"dE0/E0={row['dE0_rel']:.2e} coeffFloor@band={floorK:.2e} "
              f"log10(eps*sqrt(k!)*sqrt(k))={log10_amp:+.1f}")
    return rows


def p2b_fd_table(wall_rows):
    """The P2b finite-difference numbers at fixed H. The label is the MEASURED
    base-energy discrepancy dE0 between the exact and the reconstructed
    representations of the g=1 base cyclic vector (precision_wall): if dE0 is
    macroscopic the FD inputs are already amplifier output, so every row is
    labelled and the verdict does not depend on the artefact values."""
    dE0 = {r["lam"]: r["dE0_rel"] for r in wall_rows}
    print("B3 P2b finite-difference output (labelled by measured floor blowup):")
    rows = []
    for lam in LAMS:
        band = band_depth(lam)
        M = band + 140
        theta, Qm = eig_base(M)
        bD, bO = base_jacobi(M)
        for name, L in LS.items():
            if lam >= 6.0 and name != "log2":
                continue
            runs = {}
            for tag, gf in [
                ("base", lambda t: np.ones_like(t)),
                ("Ep", lambda t, L=L: euler_sqrt(t, L, H)),
                ("Em", lambda t, L=L: euler_sqrt(t, L, -H)),
                ("Dp", lambda t, L=L: np.exp(H * np.cos(2.0 * L * t))),
                ("Dm", lambda t, L=L: np.exp(-H * np.cos(2.0 * L * t))),
            ]:
                psi = psi_of(gf, theta, Qm)
                aT, bT, _ = lanczos(bD, bO, psi, M)
                E = energy_from_coeffs(aT[: M - 1], bT, lam)[0]
                runs[tag] = E
            e_pp = (runs["Ep"] - 2 * runs["base"] + runs["Em"]) / (H * H)
            d_dot = (runs["Dp"] - runs["Dm"]) / (2.0 * H)
            row = dict(lam=lam, L=name, epp=e_pp, d_dot=d_dot,
                       delta=e_pp - d_dot, ratio=(e_pp - d_dot) / abs(d_dot),
                       base_floor_blowup=dE0[lam])
            rows.append(row)
            print(f"  lam={lam:5.2f} {name}: epp={e_pp:+.3e} ddot={d_dot:+.3e} "
                  f"Delta={row['delta']:+.3e} ratio={row['ratio']:+.2e} "
                  f"(base-energy floor blowup dE0={dE0[lam]:.0%})")
    return rows


# ---------------- measurement 3: base physics sanity ----------------------
def base_physics():
    print("B0 base (exact-start) energies and prolate gaps:")
    out = []
    for lam in [0.5, 1.1, 6.0, 9.0, 12.0, 18.0]:
        M = band_depth(lam) + 140
        theta, Qm = eig_base(M)
        bD, bO = base_jacobi(M)
        e0 = np.zeros(M)
        e0[0] = 1.0
        aE, bE, _ = lanczos(bD, bO, e0, M)
        E0, rpos, gap = energy_from_coeffs(aE[: M - 1], bE, lam)
        out.append(dict(lam=lam, M=M, E0=E0, rank_pos=rpos, gap=gap))
        print(f"  lam={lam:5.1f} M={M} E0={E0:.4e} rank+={rpos} minGap={gap:.3f}")
    return out


def main():
    okA = control_3point()
    okB1 = tail_growth_demo()
    if not (okA and okB1):
        print("harness sanity failed - abort")
        return
    base = base_physics()
    wall = precision_wall()
    fd = p2b_fd_table(wall)
    with open("p2b_probe_results.json", "w") as f:
        json.dump(dict(base=base, wall=wall, fd=fd), f, indent=1)
    print("verdict data written to p2b_probe_results.json")


if __name__ == "__main__":
    main()
