#!/usr/bin/env python3
"""Probe 824c: push resolution to n=6000 and interval to L=32 — is the
transported-Sonin outer-leak plateau stable (true floor) or does it break?"""
from __future__ import annotations
import numpy as np
from scipy.signal.windows import dpss

def shift_op(p, dt, n, sign):
    sh = int(round(float(np.log(p)) / dt)); S = np.eye(n)
    for i in range(n):
        j = i + sign * sh
        if 0 <= j < n:
            S[i, j] -= p ** -0.5
    return S

def T_matrix(pr, dt, n, sign):
    T = np.eye(n)
    for p in pr:
        T = shift_op(p, dt, n, sign) @ T
    return T

def slepian_radial(t, logla, nw, nwant):
    n = len(t); j0 = np.searchsorted(t, logla - 1e-12)
    Lwin = min(max(4, int(4 * nw)), max(4, n - j0))
    win = dpss(Lwin, nw, nwant); nc = win.shape[0]
    W = np.zeros((n, nc)); W[j0:j0 + Lwin, :] = win.T; W[t < logla - 1e-12, :] = 0.0
    for k in range(nc):
        nz = np.linalg.norm(W[:, k])
        if nz > 0:
            W[:, k] /= nz
    return W, nc

def outer_leak(pr, logla, n, Lt):
    t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]; under = t < logla - 1e-12
    T = T_matrix(pr, dt, n, +1); Td = T_matrix(pr, dt, n, -1)
    car = np.where(t >= logla - 1e-12)[0]; A = T[:, car]
    G = A.conj().T @ A; Ginv = np.linalg.pinv(G)
    def D(u): return Td @ (A @ (Ginv @ (A.conj().T @ u)))
    Blk, nc = slepian_radial(t, logla, nw=4, nwant=6)
    leaks = []
    for k in range(nc):
        Bt = T @ Blk[:, k]; u = Bt / (np.linalg.norm(Bt) + 1e-30); Du = D(u)
        fn = np.linalg.norm(Du) + 1e-30; leaks.append(np.linalg.norm(Du[under]) / fn)
    return max(leaks)

pr = [2, 3, 5, 7, 11, 13]
print("Transported-Sonin outer-leak, extended resolution a (families) plateau-check")
print(f"{'n':>6} {'L=8':>7} {'L=16':>7} {'L=32':>7}")
for n in [2000, 3000, 4000, 6000]:
    row = [f"{outer_leak(pr, 0.0, n, Lt):.4f}" for Lt in [8.0, 16.0, 32.0]]
    print(f"{n:>6} {'  '.join(row)}")