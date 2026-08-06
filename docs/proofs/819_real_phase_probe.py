#!/usr/bin/env python3
"""Probe 819: does the REAL archimedean phase rescue R0 (vs 818's toy clone)?

818's numeric R0 (alternating projection onto range(R) ∩ range(Q0)) collapsed to
rank 0.  But 818 used a TOY pure-phase clone for HT.  This probe installs the
ACTUAL archimedean phase from CCM24HardyTitchmarsh.lean:
    archFactor(xi) = GammaR(1/2 - 2 pi i xi) = pi^-(z/2) Gamma(z/2),  z = 1/2 - 2 pi i xi
    proved archFactor(-xi) = conj(archFactor xi) (:74), archFactor != 0 (:47)
    m(xi) = archFactor(xi) / archFactor(-xi),  |m| = 1  (CCM24 :104-106)
    HT0  = F^dag . m . spectralReflection .   (CCM24HardyTitchmarsh:331-336)
and re-runs the 818 alternating-projection intersection probe.

QUESTION: was 818's degeneracy a toy-phase artifact or a finite-grid-geometry
fact?  If R0 still collapses with the REAL Gamma phase, numeric R0 is
unreachable by ANY finite intersection, confirming 818's honest verdict and
pushing the inner channel out of reach of grid methods.

Run: python3 819_real_phase_probe.py   (WSL venv: .venv-probe)
"""
from __future__ import annotations
import numpy as np
from scipy.special import gamma


def archFactor(xi):
    """CCM24ArchimedeanFactor; z = 1/2 - 2 pi i xi, factor = pi^-(z/2) Gamma(z/2)."""
    z = 0.5 - 1j * 2 * np.pi * np.asarray(xi, dtype=complex)
    return np.pi ** (-z / 2.0) * gamma(z / 2.0)


def phase(xi):
    """m(xi) = archFactor(xi)/archFactor(-xi); |m|=1 (archFactor(-)=conj)."""
    ax = np.asarray(xi, dtype=complex)
    return archFactor(ax) / archFactor(-ax)


def ht_from_m(m, n):
    """HT = F^dag . diag(m) . spectralReflection . F, F unitary DFT."""
    F = np.fft.fft(np.eye(n), axis=0) / np.sqrt(n)
    idx = np.array([(-j) % n for j in range(n)])
    return F.conj().T @ np.diag(m) @ np.eye(n)[idx] @ F


def shift_op(p, dt, n, sign):
    sh = int(round(float(np.log(p)) / dt))
    S = np.eye(n)
    for i in range(n):
        j = i + sign * sh
        if 0 <= j < n:
            S[i, j] -= p ** -0.5
    return S


def T_matrix(primes, dt, n, sign):
    T = np.eye(n)
    for p in primes:
        T = shift_op(p, dt, n, sign) @ T
    return T


def make_RQ(Rl, H, t):
    n = len(t)
    Rm = np.diag((t >= Rl - 1e-12).astype(float))
    B = H.conj().T @ Rm
    U, s, _ = np.linalg.svd(B, full_matrices=False)
    r = int((s > s.max()*1e-9).sum())
    Qm = U[:, :r] @ U[:, :r].conj().T
    return Rm, Qm


def R0_alt(Rm, Qm, n, iters=150):
    e = np.eye(n); P = np.zeros((n, n), dtype=complex)
    for i in range(n):
        v = e[:, i].copy()
        for _ in range(iters):
            v = Qm @ (Rm @ v)
        P[:, i] = v
    return P


def main():
    for Rl in [0.0, 1.0]:
        Lt = 4.0; n = 80
        t = np.linspace(-Lt, Lt, n); dt = t[1]-t[0]
        car = np.where(t >= Rl - 1e-12)[0]
        under = np.where(t < Rl - 1e-12)[0]
        print(f"\n==== logl={Rl} n={n} (carrier={len(car)}) ====")
        # two HTs: real archimedean phase vs toy tanh
        xi = np.fft.fftfreq(n, d=dt)
        H_real = ht_archim(n, dt)
        H_toy = ht_archim(n, dt, toy=True)
        for kind, H in [('REAL-Gamma', H_real), ('toy', H_toy)]:
            err = np.linalg.norm(H.conj().T @ H - np.eye(n))
            Rm, Qm = make_RQ(Rl, H, t)
            R0 = R0_alt(Rm, Qm, n, iters=150)
            sv = np.linalg.svd(R0, compute_uv=False)
            rank0 = int(np.sum(sv > 1e-7))
            idem = np.linalg.norm(R0@R0 - R0)
            BndP = Rm - R0@R0
            print(f"[{kind}] H-err={err:.1e} rank(R0)={rank0}/{n} idemp={idem:.1e}")
            for pr in [[2],[2,3],[2,3,5]]:
                Tp = T_matrix(pr, dt, n, +1); Td = T_matrix(pr, dt, n, -1)
                A = Tp[:, car]; G = A.conj().T @ A
                Ginv = np.linalg.inv(G + 1e-16*np.eye(len(car)))
                tbl = []
                for jidx in {0, len(car)//2, len(car)-1}:
                    u = np.zeros(n); u[car[jidx]] = 1.0
                    Du = Td @ (A @ (Ginv @ (A.conj().T @ u)))
                    fn = np.linalg.norm(Du)+1e-30
                    tbl.append((np.linalg.norm(Du[under])/fn,
                                np.linalg.norm((np.eye(n)-Qm)@(Rm@Du))/fn,
                                np.linalg.norm(BndP@Du)/fn))
                a = np.mean([x[0] for x in tbl]); b = np.mean([x[1] for x in tbl])
                c = np.mean([x[2] for x in tbl])
                print(f"     pr={pr}: OUTER={a:.3f} second={b:.3f} band={c:.3f}")


def ht_archim(n, dt, toy=False):
    F = np.fft.fft(np.eye(n), axis=0) / np.sqrt(n)
    xi = np.fft.fftfreq(n, d=dt)
    m = np.exp(1j*(0.5*np.pi*np.tanh(xi))) if toy else phase(xi)
    idx = np.array([(-j) % n for j in range(n)])
    return F.conj().T @ np.diag(m) @ np.eye(n)[idx] @ F


if __name__ == "__main__":
    main()