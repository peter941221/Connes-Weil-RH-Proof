#!/usr/bin/env python3
"""Probe 837 (BRAVE): exact Gate-3U prolate factor with the REAL archimedean
phase and a STABLE direct-intersection R0.

Repo objects:
    R   = radial log-support projection,  diag(1[t >= loglambda])
          CCM24FiniteSProjectionTrace.lean:76-78
    Q   = archimedean Fourier-support projection = orth-proj onto range(H^dag R)
          CCM24FiniteSProjectionTrace.lean:81-83
    H   = Hardy-Titchmarsh unitary, built from real scattering phase
          m(xi) = Gamma_R(1/2 - 2pi i xi)/Gamma_R(1/2 + 2pi i xi)
          CCM24HardyTitchmarsh.lean:104-106
    R0  = proj onto range(R) ∩ range(Q)
          = starProjection (LogRadialSupport ⊓ FourierSupport)
          CCM24HardyTitchmarsh.lean:376-379
    Factor = Q (R - R0)            CCM24FiniteSProjectionTrace.lean:35-38
    Gate HS majorant = sum ||Q(R-R0) b_k||^2 over ONB {b_k} of range(R)
          CCM24FiniteSCanonicalSupportGate3U.lean:167-176

New vs 818/819/836:
  - 818/819: R0 = ALTERNATING projection -> rank-0 degeneration.
  - 836: R0 = Slepian radial cut, WITHOUT the real Fourier-support Q.
  - Here: R0 = DIRECT orthogonal projector onto range(R) ∩ range(Q) via
    per-column threshold over an ONB of range(R); Q uses the REAL phase.
Run: source .venv-probe/bin/activate && python3 837_real_sonin_gate_factor_probe.py
"""
from __future__ import annotations
import numpy as np
from scipy.special import gamma


def archFactor(xi):
    z = 0.5 - 1j * 2 * np.pi * np.asarray(xi, dtype=complex)
    return np.pi ** (-z / 2.0) * gamma(z / 2.0)


def phase(xi):
    ax = np.asarray(xi, dtype=complex)
    return archFactor(ax) / archFactor(-ax)


def ht_unitary(m, n):
    F = np.fft.fft(np.eye(n), axis=0) / np.sqrt(n)
    idx = np.array([(-j) % n for j in range(n)])
    return F.conj().T @ np.diag(m) @ np.eye(n)[idx] @ F


def proj_onto_range(M, tol_ratio=1e-9):
    U, s, _ = np.linalg.svd(M, full_matrices=False)
    r = int((s > (s.max() * tol_ratio)).sum()) if len(s) else 0
    return U[:, :r] @ U[:, :r].conj().T, r


def radial_projector(t, logla):
    return np.diag((t >= logla - 1e-12).astype(float))


def onb_of_range(R, tol=1e-9):
    ev, V = np.linalg.eigh(R)
    keep = np.abs(ev) > tol
    return V[:, keep]


def intersect_projector(R, Q, tol=1e-7):
    Br = onb_of_range(R)
    if Br.shape[1] == 0:
        return np.zeros(R.shape, dtype=complex), 0
    S = (np.eye(R.shape[0]) - Q) @ Br
    sz = np.linalg.norm(S, axis=0)
    sel = sz < tol
    basis = Br[:, sel]
    if basis.shape[1] == 0:
        return np.zeros(R.shape, dtype=complex), 0
    Qs, _ = np.linalg.qr(basis)
    R0 = Qs @ Qs.conj().T
    return R0, Qs.shape[1]


def min_deviation(R, Q):
    Br = onb_of_range(R)
    if Br.shape[1] == 0:
        return 0.0
    S = (np.eye(R.shape[0]) - Q) @ Br
    return float(np.linalg.norm(S, axis=0).min())


def gate_factor_measure(R, Q, R0):
    Br = onb_of_range(R)
    if Br.shape[1] == 0:
        return 0.0, 0.0, 0
    fac = Q @ (R - R0)
    fh = fac @ Br
    hs2 = float(np.sum(np.abs(fh) ** 2))
    op = float(np.linalg.norm(fac, 2))
    return hs2, op, Br.shape[1]


def main():
    for logla in [0.0, 1.0]:
        print(f"\n==== loglambda={logla} ====")
        for n in [80, 160, 320]:
            Lt = 3.0
            t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]
            R = radial_projector(t, logla)
            xi = np.fft.fftfreq(n, d=dt)
            H = ht_unitary(phase(xi), n)
            Q, rQ = proj_onto_range(H.conj().T @ R)
            R0, rk = intersect_projector(R, Q)
            hs2, op, rankR = gate_factor_measure(R, Q, R0)
            mdev = min_deviation(R, Q)
            print(f"  n={n:4d} rank(R)={rankR:3d} rank(Q)={rQ:3d} "
                  f"dim(RnQ)={rk:3d} HS={hs2:9.3f} opNorm={op:8.3f} "
                  f"minDev={mdev:.2e}")


if __name__ == "__main__":
    main()