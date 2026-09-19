#!/usr/bin/env python3
# Record 1694 rig (v3): the Sonin meet's spectral dimension density D(xi).
#
# Hand-derived reduction (F27/F28: this rig is a CHECK, not authority):
#   mass face  <=>  Summable_i ||J^dag C J e_i||^2  <=>  tr(P_meet M_{|kappa|^2} P_meet) < inf
#              <=>  int |kappa(xi)|^2 D(xi) dxi < inf,
# D(xi) = diagonal of F P_meet F^{-1} (spectral density of the carrier
# projection).  Lean meet: { u : supp u subset [a,inf), supp Tu subset
# [a,inf) }, a = log lambda, readback (Tu)^ = m(xi)(Fu)(-xi),
# m = Gamma_R(1/2-2 pi i xi)/Gamma_R(1/2+2 pi i xi).
#
# v1 lesson: spectral-side sampling of the support condition is
# under-determined (failed F52).  v2 lesson: coarse/fine grid mixing creates
# Dirichlet-sidelobe rows of unit norm that the SVD counts as constraints
# (failed F52: 0.52 instead of 2).  v3: conditions and functions on the SAME
# grid - then for m=1 the Dirichlet sums vanish EXACTLY off the alignment and
# the meet is exactly the grid window; the density readout is
#     D(xi_j) = dt * ftilde_j^* Pi ftilde_j,   ftilde_j[k] = e^{2 pi i xi_j t_k},
# which reproduces the continuum kernel diagonal (Riemann dt^2 with the
# 1/dt of the delta diagonal = dt).
#
# F52 known answer: m = 1 => meet = grid window [a,-a], dim = 2|a|/dt,
# D(xi) = 2|a| for ALL xi.  Shear/normal-form prediction for the real ratio:
# D(xi) ~ (log|xi| - 2a)_+, vanishing on |xi| < lambda^2.  N-scaling is the
# emptiness discriminator (stable profile => nonempty meet; decay => {0}).

import numpy as np

TWO_PI = 2.0 * np.pi


def scattering_phase(xi):
    from scipy.special import gamma as cgamma
    s = 0.5 + TWO_PI * 1j * xi
    gr = np.pi ** (-0.5 * s) * cgamma(0.5 * s)
    return np.conj(gr) / gr


def meet_model(a, use_real_m, T=16.0, N=1024, svd_tol=1e-10):
    dt = 2.0 * T / N
    t = -T + dt * np.arange(N)
    xi = np.fft.fftfreq(N, d=dt)         # DFT-conjugate grid, cycles/unit t
    if use_real_m:
        m = scattering_phase(xi)
    else:
        m = np.ones(N, dtype=complex)

    # M[f,k] = (1/N) sum_j m(xi_j) exp(2 pi i xi_j (t_f + t_k))
    #        = IFFT of m evaluated at (t_f + t_k): build via FFT matrices.
    E = np.exp(TWO_PI * 1j * np.outer(t, xi))      # t x xi, e^{+2 pi i xi t}
    M = (E * m[None, :]) @ E.T / N                 # (t_f + t_k) structure

    # Support coordinates: the meet = {u : supp u subset [a,inf), Mu|_{t<a} = 0}
    # is ker(A_s) INSIDE the support coordinates (v2/v3 bug: ker(M.P1) contains
    # all of ker(P1) - the intersection must be taken inside the support).
    rows = t < a - 1e-12
    supp = t >= a - 1e-12
    A_s = M[np.ix_(rows, supp)]                    # rows t<a, cols t>=a
    n_s = int(supp.sum())

    _, s, Vh = np.linalg.svd(A_s, full_matrices=True)
    rank = int(np.sum(s > svd_tol * s[0]))
    Vr = Vh.conj()[:rank, :].T
    P_s = np.eye(n_s) - Vr @ Vr.conj().T           # meet projection, support coords

    # embed back to the full grid
    P = np.zeros((N, N), dtype=complex)
    P[np.ix_(supp, supp)] = P_s

    # density readout (delta-normalized; real part; clip roundoff)
    Efull = np.exp(TWO_PI * 1j * np.outer(t, xi))
    D = dt * np.einsum('ji,jk,ki->i', Efull.conj(), P, Efull).real

    # density readout (delta-normalized; real part; clip roundoff)
    D = np.maximum(D, 0.0)
    return xi, D, n_s - rank


def main():
    print("== F52 calibration: m = 1 ==")
    print("expect dim = 2|a|/dt and D(xi) = 2|a| for all xi")
    for a in (-1.0, -0.5):
        for N in (512, 1024):
            xi, D, dim = meet_model(a, use_real_m=False, N=N)
            T = 16.0
            dt = 2 * T / N
            mid = np.abs(xi) < 0.9 * xi.max()
            print(f"  a={a:+.2f} N={N:5d}: dim={dim:5d} (expect {2*abs(a)/dt:.0f})"
                  f"  D interior mean={D[mid].mean():.4f} (expect {2*abs(a):.3f})"
                  f"  min={D[mid].min():.4f} max={D[mid].max():.4f}")

    print()
    print("== real Gamma-ratio: profile + N-scaling (emptiness discriminator) ==")
    for a in (-2.0, -1.0, -0.5):
        lam = float(np.exp(a))
        print(f"  a={a:+.2f} (lambda={lam:.4f}, lambda^2={lam*lam:.4f})")
        for N in (512, 1024, 2048):
            xi, D, dim = meet_model(a, use_real_m=True, N=N)
            probes = [0.1, 0.3, 1.0, 2.0, 4.0, 7.5]
            vals = []
            for p in probes:
                k = int(np.argmin(np.abs(xi - p)))
                vals.append(D[k])
            pv = " ".join(f"D({q:g})={v:.3f}" for q, v in zip(probes, vals))
            print(f"    N={N:5d} dim={dim:5d}  {pv}")
        print(f"    shear prediction (log|xi|-2a)_+ at 1,4,7.5: "
              f"{max(np.log(1.0)-2*a,0):.2f} {max(np.log(4.0)-2*a,0):.2f} "
              f"{max(np.log(7.5)-2*a,0):.2f}; D=0 predicted on |xi|<{lam*lam:.3f}")

    print()
    print("== mass-face reading: int |kappa|^2 D dxi, a = -1 (N=2048) ==")
    a = -1.0
    xi, D, dim = meet_model(a, use_real_m=True, N=2048)
    dxi = xi[1] - xi[0]
    tests = [("gaussian kappa=exp(-xi^2/2)", lambda x: np.exp(-x * x / 2)),
             ("bump kappa (C_c^inf)", lambda x: np.where(np.abs(x) < 12,
              np.exp(-1.0 / np.maximum(1e-30, 1 - (x / 12.0) ** 4)), 0.0)),
             ("rational kappa=(1+xi^2)^(-3/2)", lambda x: (1 + x * x) ** (-1.5))]
    for name, kap in tests:
        k2 = np.abs(kap(xi)) ** 2
        mass = float(np.sum(k2 * D) * dxi)
        plain = float(np.sum(k2) * dxi)
        print(f"  {name}: int|kappa|^2 D = {mass:.6f}  (int|kappa|^2 = {plain:.4f})")


if __name__ == "__main__":
    main()
