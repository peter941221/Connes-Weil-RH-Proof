#!/usr/bin/env python3
"""Probe the FULL Gate-3U channels using a numerically-exact R0 (Sonin intersection
                 R0 = proj onto  range(R) ∩ range(Q0),  Q0 = HT^d R HT.

Why new: prior probes (814-817) reached only the OUTER channel (I-R)oD because
the exact Sonin projection R0 was not numerically available.  Here we materialize
R0 by von Neumann alternating projection onto two closed subspaces:
  - range(R)   : radial support  t >= loglambda
  - range(Q0)  : "Fourier-support", Q0 = orth-projector onto range(H^dag R),
                 H the pure-phase spectral-reflection isometry
                 (CCM24HardyTitchmarsh.lean:330-380).
We SELF-CHECK R0: idempotent, self-adjoint, range contained in both (so it is a
genuine orthogonal projection).  Then we measure the channels Lean 815 §5 named
actionable:
  Second   S   = R (I - Q0) R D        (sourceSecondSupportCoframeLeakage)
  Band     Bnd = forward + (R - R0) D
  Outer    O   = (I - R) D
  Sonin    s0  = R0 D
Run: python3 818_full_gate_r0_probe.py   (WSL venv: .venv-probe)
"""
from __future__ import annotations
import numpy as np


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


def mk_HT(n, dt, kind):
    """Pure-phase spectral-reflection clone of the archimedean Hardy-Titchmarsh.
    The repo's actual phase = archFactor/conj(archFactor)
    (CCM24HardyTitchmarsh.lean:104-106) is not exported with a closed form, so
    we must choose a proxy pure phase |m|=1.  HONESTY: the second/band channels
    below are only trustworthy if stable across these clones (kind 0..2)."""
    F = np.fft.fft(np.eye(n), axis=0) / np.sqrt(n)
    Fh = F.conj().T
    xi = np.fft.fftfreq(n, d=dt)
    if kind == 0:
        phase = 0.5*np.pi*np.tanh(xi)
    elif kind == 1:
        phase = np.pi*np.sin(xi)/(1.0+xi**2)
    else:
        phase = 0.5*np.pi*(xi/(1.0+xi**2))
    m = np.exp(1j * phase)                              # |m|=1
    idx = np.array([(-j) % n for j in range(n)])
    M = np.diag(m)
    Rf = np.eye(n)[idx]
    return Fh @ M @ Rf @ F


def make_RQ(Rl, H, t):
    """Radial projector R; Fourier-support projector Q0 = orth-proj onto range(H^dag R)."""
    n = len(t)
    Rm = np.diag((t >= Rl - 1e-12).astype(float))
    B = H.conj().T @ Rm
    U, s, _ = np.linalg.svd(B, full_matrices=False)
    r = int((s > s.max()*1e-9).sum())
    U = U[:, :r]
    Qm = U @ U.conj().T
    return Rm, Qm


def R0_alt(Rm, Qm, n, iters=150):
    """Von Neumann alternating projection onto range(R) ∩ range(Q). Basis by basis."""
    e = np.eye(n)
    P = np.zeros((n, n), dtype=complex)
    for i in range(n):
        v = e[:, i].copy()
        for _ in range(iters):
            v = Qm @ (Rm @ v)
        P[:, i] = v
    return P


def check_proj(X, Rm, Qm, name):
    n = X.shape[0]; I = np.eye(n)
    idem = np.linalg.norm(X @ X - X)
    selfa = np.linalg.norm(X - X.conj().T)
    inR = np.linalg.norm((I - Rm) @ X)
    inQ = np.linalg.norm((I - Qm) @ X)
    ok = idem < 1e-7 and selfa < 1e-7 and inR < 1e-7 and inQ < 1e-7
    print(f"  [{name}] idemp={idem:.1e} selfadj={selfa:.1e} "
          f"(I-R)X={inR:.1e} (I-Q)X={inQ:.1e}  -> {'OK' if ok else 'FAIL'}")
    return ok


def main():
    for Rl in [0.0, 1.0]:
        Lt = 4.0; n = 80
        t = np.linspace(-Lt, Lt, n); dt = t[1]-t[0]
        car = np.where(t >= Rl - 1e-12)[0]
        under = np.where(t < Rl - 1e-12)[0]
        I = np.eye(n)
        print(f"==== logl={Rl} n={n}  (kind-sweep over HT phase clones) ====")
        for kind in range(3):
            H = mk_HT(n, dt, kind)
            herr = np.linalg.norm(H.conj().T @ H - I)
            Rm, Qm = make_RQ(Rl, H, t)
            R0 = R0_alt(Rm, Qm, n, iters=150)
            sv = np.linalg.svd(R0, compute_uv=False)
            rankR0 = int(np.sum(sv > 1e-7))
            check_proj(R0, Rm, Qm, f"R0 kind{kind}")
            BndP = Rm - R0 @ R0
            print(f"  kind={kind} H-err={herr:.1e} rank(R0)={rankR0}/{n} "
                  f"(carrier={len(car)}, R-rank={int(np.trace(Rm))})")
            for pr in [[2],[2,3],[2,3,5]]:
                T = T_matrix(pr, dt, n, +1); Td = T_matrix(pr, dt, n, -1)
                A = T[:, car]; G = A.conj().T @ A
                Ginv = np.linalg.inv(G + 1e-16*np.eye(len(car)))
                def D(u):
                    return Td @ (A @ (Ginv @ (A.conj().T @ u)))
                js = sorted(set(int(x) for x in np.linspace(0, len(car)-1, 3)))
                acc = []
                for jidx in js:
                    u = np.zeros(n); u[car[jidx]] = 1.0
                    Du = D(u); fn = np.linalg.norm(Du)+1e-30
                    outer =  np.linalg.norm(Du[under])/fn
                    second = np.linalg.norm((I-Qm) @ (Rm @ Du))/fn
                    band  =  np.linalg.norm(BndP @ Du)/fn
                    sonin =  np.linalg.norm(R0  @ Du)/fn
                    acc.append((outer, second, band, sonin))
                a = np.mean([x[0] for x in acc]); b = np.mean([x[1] for x in acc])
                c = np.mean([x[2] for x in acc]); d = np.mean([x[3] for x in acc])
                print(f"     pr={pr}: mean outer={a:.3f} second={b:.3f} "
                      f"band={c:.3f} sonin={d:.3f}")


if __name__ == "__main__":
    main()