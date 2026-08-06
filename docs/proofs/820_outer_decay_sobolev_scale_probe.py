#!/usr/bin/env python3
"""Probe 820: does the OUTER channel decay with radial cutoff (Sobolev-at-threshold)?

Track (b) — the analytic/Sobolev hypothesis for the gate.  815 section 5 route 1
is: "show (I-R)oD does not leak" i.e. an estimate that the metric coframe maps
the source Sonin carrier INTO radial support with controllable decay.  A
Sobolev-style mechanism would manifest as: the OUTER leak
    Outer(u) = ||D(u)|_[below loglambda]||  /  ||D(u)||
decaying at some known (power / exponential) rate as the radial cutoff loglambda
is pushed inward / the ring is deepened.  This probe MEASURES the decay rate,
which is the analytic content that would feed a Lean Sobolev / decay lemma.

Key difference from 815-819: no R0, no Q0, no subspace-intersection artifact.
It is a pure self-similar decay measurement in the radial variable on the metric
coframe.  Decay <= NoVer the gate's Sobolev claim is the same while (815).

method: for increasing rings (radial high-frequency = narrow support at the
boundary), compute outer-frame leak of D on the SINGLE most-outer radial probe
(the bump supported just inside logla).  Trend  -> 0 = supports a Sobolev/
boundedness of the map A -> radial support.  Saturation at O(1) = the map is not
radial-support-preserving on the derivative scale.

Run: python3 820_outer_decay_sobel_scale_probe.py   (WSL venv: .venv-probe)
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


def main():
    for pr in [[2], [2, 3], [2, 3, 5]]:
        # depth sweep: raise resolution and push the probe deeper into the radial wall
        for scale in [1.0, 2.0, 4.0, 8.0]:
            n = int(40 * scale); Lt = 4.0
            t = np.linspace(-Lt, Lt, n); dt = t[1]-t[0]
            # radial support at the LEFT edge (probe sits AT threshold), probe = a
            # narrow bump pinned at the first in-support grid cab; deepen by
            # pushing the cutoff LEFT (negative) so more high-frequencies are under
            for Rl_off in [0.0, -0.5, -1.0, -1.5]:
                Rl = Rl_off
                car = np.where(t >= Rl - 1e-12)[0]
                under = np.where(t < Rl - 1e-12)[0]
                if len(under) == 0 or len(car) == 0:
                    continue
                T = T_matrix(pr, dt, n, +1); Td = T_matrix(pr, dt, n, -1)
                A = T[:, car]; G = A.conj().T @ A
                Ginv = np.linalg.inv(G + 1e-14*np.eye(len(car)))
                # probe bump at the boundary: delta at the first in-support index
                u = np.zeros(n); u[car[0]] = 1.0
                Du = Td @ (A @ (Ginv @ (A.conj().T @ u)))
                outr = np.linalg.norm(Du[under]); full = np.linalg.norm(Du)
                print(f"pr={pr} scale={scale:4.0f} cutoff_off={Rl_off:+.1f} "
                      f"outer/full={outr/full:.4f}  (raw outer={outr:.4f} full={full:.4f})")


if __name__ == "__main__":
    main()