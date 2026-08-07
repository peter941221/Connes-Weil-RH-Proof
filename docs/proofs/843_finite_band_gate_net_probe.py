#!/usr/bin/env python3
"""Probe 843 (BRAVE): the SIGNED Net Gate-3B bound at unit-lambda (loglambda=0).

Repository Lean facts driving this probe (via 842 audit + TransportedOuterCollapse):
  canonicalRealGate3UAt  ==>  |completedCycle real trace| <= 1
    completedCycle real trace = (outer trace) - (moving-band trace)
    and for the genuine finite-Euler transport outer = 0 (a Lean `=` theorem).
  So the real 3U quantity is the signed trace of the band R - R0 (the
  "three-branch" response).  837/836/818 only measured HS summability / op norms;
  they never measured the SIGNED trace that the Gate <= 1 actually bounds.

Unit-lambda objects (HS summability axiom-clean per 839/842):
  R    = radial log-support proj  = diag(1[t>=0])                 (E)
  Q    = arch Fourier-support proj = orth-proj onto range(H^dag E)
  R0   = Sonin proj = orth-proj onto range(R) cap range(Q)
  band = R - R0
  factor = Q (R - R0)
  Gate = |signed trace of band over an ONB|   <- the signed real bound

Run on Windows:  /c/Users/Peter/AppData/Local/Programs/Python/Python313/python.exe 843_...
"""
from __future__ import annotations
import numpy as np
from scipy.special import gamma


def arch_factor(xi):
    z = 0.5 - 1j * 2.0 * np.pi * np.asarray(xi, dtype=complex)
    return np.pi ** (-z / 2.0) * gamma(z / 2.0)


def phase(xi):
    ax = np.asarray(xi, dtype=complex)
    return arch_factor(ax) / arch_factor(-ax)


def ht_unitary(m, n):
    F = np.fft.fft(np.eye(n), axis=0) / np.sqrt(n)
    idx = np.array([(-j) % n for j in range(n)])
    return F.conj().T @ np.diag(m) @ np.eye(n)[idx] @ F


def proj_onto_range(M, tol_ratio=1e-9):
    U, s, _ = np.linalg.svd(M, full_matrices=False)
    if len(s) == 0:
        return np.zeros(M.shape, dtype=complex), 0
    r = int((s > (s.max() * tol_ratio)).sum())
    return U[:, :r] @ U[:, :r].conj().T, r


def onb_of_eigen(M, tol=1e-9):
    ev, V = np.linalg.eigh(M)
    keep = np.abs(ev) > tol
    return V[:, keep]


def intersect_projector(R, Q, tol=1e-7):
    Br = onb_of_eigen(R)
    if Br.shape[1] == 0:
        return np.zeros(R.shape, dtype=complex), 0
    Sz = (np.eye(R.shape[0]) - Q) @ Br
    sel = np.linalg.norm(Sz, axis=0) < tol
    basis = Br[:, sel]
    if basis.shape[1] == 0:
        return np.zeros(R.shape, dtype=complex), 0
    Qs, _ = np.linalg.qr(basis)
    return Qs @ Qs.conj().T, Qs.shape[1]


def signed_trace(H, Br):
    if Br.shape[1] == 0:
        return 0.0
    return float(np.trace(Br.conj().T @ H @ Br).real)


def main():
    np.set_printoptions(precision=6, suppress=True)
    print("PROBE 843: SIGNED NET Gate-3B at unit-lambda (logla=0)")
    print("+" + "-" * 72)
    Lt = 3.0
    for n in [192, 384, 768]:
        t = np.linspace(-Lt, Lt, n)
        dt = t[1] - t[0]
        R = np.diag((t >= 0).astype(float))
        xi = np.fft.fftfreq(n, d=dt)
        H = ht_unitary(phase(xi), n)
        Q, rQ = proj_onto_range(H.conj().T @ R)
        R0, r0 = intersect_projector(R, Q)
        Br = onb_of_eigen(R)
        band = R - R0
        factor = Q @ (R - R0)
        s_band = signed_trace(band, Br)
        hs = np.sum(np.abs(factor @ Br) ** 2)
        op_band = float(np.linalg.norm(band, 2))
        op_factor = float(np.linalg.norm(factor, 2))
        # explicit bump detection <f, band f> on the negative half-line
        neg = (t < 0).astype(float)
        ftest = np.zeros(n, dtype=complex)
        ftest[neg > 0] = 1.0
        ftest = ftest / np.linalg.norm(ftest)
        signed_bump = float(np.real(np.vdot(ftest, band @ ftest)))
        print(f"  n={n:4d}  rank(R)={Br.shape[1]:3d} rank(Q)={rQ:3d} dim(RnQ)={r0:3d}")
        print(f"      signed band trace = {s_band: .6f}    signed <f,band f>(bump) = {signed_bump: .6f}")
        print(f"      HS factor = {hs:11.4f}    op band = {op_band:7.4f}   op factor = {op_factor:7.4f}")
        print(f"      => |signed Gate bound| = {abs(s_band): .6f}   (the < 1 door)")
        print()


if __name__ == "__main__":
    main()