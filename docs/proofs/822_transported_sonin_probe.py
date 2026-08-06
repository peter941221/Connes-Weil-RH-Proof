#!/usr/bin/env python3
"""Probe 822 (route b): measure the outer channel on the EXACT TRANSPORTED-Sonin
frame, not a generic subspace intersection.

The repo PROVES (CCM24FiniteEulerSoninTransport.lean:69-77) that the finite
Euler transport T = ccm24FiniteEulerTransportEquiv sends the source Sonin
intersection EXACTLY onto the target one:
    T(sourceRadial ∩ sourceFourierSupport) = radial ∩ targetFourierSupport
i.e. the correct SON-IN-space basis for the gate is T applied to real band-
limited radial (Slepian) functions — the TRANSPORTED prolate/Sonin frame.  This
is the analytic object 815 named as "not a grid number" and 818/819 tried (and
failed) to reach by subspace intersection.  Here we build it EXPLICITLY:

    frame_k = T . (exact Slepian column cut to radial support)

and measure the outer channel (I-R)oD on exactly this frame.  This is the
transported-Sonin-frame computation route (b) points at, using the repo's
proven transport-on-Sonin identity as the object selector.

Run: python3 822_transported_sonin_probe.py   (WSL venv: .venv-probe)
"""
from __future__ import annotations
import numpy as np
from scipy.signal.windows import dpss


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


def slepian_radial(t, logla, nw, nwant):
    n = len(t)
    lo = np.searchsorted(t, logla - 1e-12)
    Lwin = min(max(4, int(4*nw)), max(4, n - lo))
    win = dpss(Lwin, nw, nwant)
    nc = win.shape[0]
    W = np.zeros((n, nc))
    W[lo:lo+Lwin, :] = win.T
    W[t < logla-1e-12, :] = 0.0
    for k in range(nc):
        nz = np.linalg.norm(W[:, k])
        if nz > 0:
            W[:, k] /= nz
    return W, nc


def main():
    for logla in [0.0, 1.0]:
        Lt = 8.0; n = 600
        t = np.linspace(-Lt, Lt, n); dt = t[1]-t[0]
        car = np.where(t >= logla - 1e-12)[0]; under = np.where(t < logla - 1e-12)[0]
        for pr in [[2], [3], [5], [2,3], [2,3,5], [7,11], [2,5,7]]:
            T = T_matrix(pr, dt, n, +1); Td = T_matrix(pr, dt, n, -1)
            A = T[:, car]; G = A.conj().T @ A
            Ginv = np.linalg.inv(G + 1e-14*np.eye(len(car)))
            def D(u):
                return Td @ (A @ (Ginv @ (A.conj().T @ u)))
            # source Sonin frame = Slepian radial functions (band-limited ∩ radial)
            Blk, nc = slepian_radial(t, logla, nw=4, nwant=6)
            # transported frame = T applied to the source-Sonin frame (route-b object)
            leaks = []
            for k in range(nc):
                Bsrc = Blk[:, k]                     # source Sonin (radial∩band)
                Bt = T @ Bsrc                          # transported (into transported Sonin)
                u = Bt / (np.linalg.norm(Bt)+1e-30)  # normalize (this is the frame elt)
                Du = D(u)
                fn = np.linalg.norm(Du)+1e-30
                leaks.append(np.linalg.norm(Du[under])/fn)
            mx = max(leaks) if leaks else 0.0
            print(f"logl={logla} pr={str(pr):8s} transmitted-Sonin outer leak "
                  f"max={mx:.3f}  all=[" + " ".join(f"{v:.3f}" for v in leaks) + "]")


if __name__ == "__main__":
    main()