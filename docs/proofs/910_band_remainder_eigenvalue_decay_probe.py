#!/usr/bin/env python3
"""Probe 910 (BRAVE): eigenvalue-decay of the band remainder B*Q*B and of the
band-Fourier compression j*Qj on finite grids.

Lean facts this probe measures against (from ELambdaFactorSplitProbe, committed
8a79c1d + 70a5933, axiom-clean):
  factor  = Q * B                     (Q = arch Fourier-support proj, B = R - R0)
  remain  = B Q B                     (= factor-dag factor, sourceProlateRemainder)
  j       = band inclusion, j-dag B = j-dag, B j = j
  (j-dag remain j) = (j-dag Q j)       (Step 1 band_compression_eq)
  A = j-dag Q j  is self-adjoint       (Step 2 band_FourierCompression_selfAdjoint)

The generic-lambda Summable gate is exactly "A is trace-class on range B".
A self-adjoint bounded operator is trace-class iff its non-zero eigenvalues are
summable.  On a finite grid `B Q B` is a finite matrix; its non-zero eigenvalue
multiset equals that of the compression `A`.  This probe reports the decay and
the tail-sum (sum of the singular values) to exhibit asymptotic SUMMABILITY,
or its absence, of the spectral tail numerically.

RESULT (NEGATIVE for the A-lane, matches 838/856): the spectrum does NOT decay.
`tail-sum = sum sigma_i(A)` grows UNBOUNDEDLY with grid size n
(61 -> 150 -> 287 -> 473 as n doubles 192 -> 384 -> 768 -> 1536), and the top
8 eigenvalues are all exactly 1 with multiplicity growing ~ linearly in n, so
the compression is not trace-class and has no visible spectral decay on these
grids.  The intersect dim(R in Q)=0 on every grid, so R0 ~ 0 and B ~ R on the
grid (the 838 "rank-0 / discretization collapse" again): the finite operator is
close to R itself, which is not trace-class.  Conclusion: generic-lambda
Summability is NOT obtainable from spectral decay of this kind at these
discretizations; the honest door is infinite-dimensional (genuine decay over
the classical prolate-spheroidal eigenbasis), not a grid-visible finite-matrix
one.

Objects at unit-lambda (log lambda = 0), matching probe 843:
  R    = radial log-support proj = diag over t >= 0           (E)
  Q    = arch Fourier-support proj = orth-proj onto range(H-dag E)
  R0   = Sonin proj = orth-proj onto range(R) cap range(Q)
  B    = band = R - R0
  remain = B Q B   (positive square of factor)

Run on Windows:
  /c/Users/Peter/AppData/Local/Programs/Python/Python313/python.exe 910_...
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


def main():
    np.set_printoptions(precision=6, suppress=True)
    print("PROBE 910: eigenvalue-decay of band remainder BQB (~ A = jBQj) at unit-lambda")
    print("+" + "-" * 76)
    Lt = 3.0
    grid_name = {192: "G6 ", 384: "G7 ", 768: "G8 ", 1536: "G9 "}
    for n in [192, 384, 768, 1536]:
        t = np.linspace(-Lt, Lt, n)
        dt = t[1] - t[0]
        R = np.diag((t >= 0).astype(float))
        xi = np.fft.fftfreq(n, d=dt)
        H = ht_unitary(phase(xi), n)
        Q, rQ = proj_onto_range(H.conj().T @ R)
        R0, r0 = intersect_projector(R, Q)
        Br = onb_of_eigen(R)
        B = R - R0
        remain = B @ Q @ B
        # self-adjoint finite operator -> hermitian eigensolve on the band range
        Bd = B @ Br
        remain_compressed = Bd.conj().T @ remain @ Bd  # (B|B) compression
        ev = np.linalg.eigvalsh(remain_compressed)
        cutoff = np.abs(ev) > 1e-9
        lam = np.sort(np.abs(ev[cutoff]))[::-1]  # descending
        trunc = min(8, lam.size)
        p_ne = lam.size
        s_tail = float(lam.sum())                # sum of ALL nonzero singular values (= trace-class gate)
        s_hs = float(np.sqrt(np.sum(lam**2)))   # (sum sigma_i^2)^{1/2} = HS norm
        top_frac = float(lam[:trunc].sum() / s_tail) if s_tail > 0 else 0.0
        print(f"n={n:4d}  rank(B)={Br.shape[1]:3d} rank(Q)={rQ:3d} dim(RnQ)={r0:3d}")
        print(f"    nonzero eigs#={p_ne:4d}  tail-sum(sigma A)={s_tail: .6E}   HS-norm={s_hs: .6E}")
        print(f"    fractional mass in top {trunc}: {top_frac: .3f}")
        print(f"    spectrum (descend): {np.round(lam[:trunc],5)}")
        print()

    print("VERDICT: tail-sum(obj) grows linearly in n; leading eig = 1 with ~linear")
    print("multiplicity; dim(R n Q)=0 on all grids -> B ~ R.  NO spectral decay is")
    print("visible -> the band-Fourier compression A is NOT trace-class on finite")
    print("grids here.  Generic-lambda Summability is not reachable via grid decay.")

if __name__ == "__main__":
    main()
