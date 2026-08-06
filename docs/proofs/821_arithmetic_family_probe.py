#!/usr/bin/env python3
"""Probe 821: outer channel on REALISTIC arithmetic prime families (route a).

The toy run (815-820) used {2}, {2,3}, {2,3,5} all with exponent 1.  Route (a)'s
real content: the concrete CCM24 transport factor is
    (I - p^(-1/2) U_{`-log p`})   per VISIBLE PRIME p   (CCM24VisiblePrime, p>1)
with coefficient p^(-1/2) (CCM24EulerTransport.lean:32-52).  The stored exponent
is arithmetic ownership only; the operator runs over deduplicated prime bases
(CCM24FiniteSProjectionTrace.lean:46 visiblePrimes).  So the real arithmetic
families to test are DISTINCT PRIME SETS and higher primes, not exponent
multiplicity.  QUESTION (route a): is there any realistic arithmetic family on
which the outer channel (I-R)oD leaks -> 0, or is it always O(1)?

Tested families: singles (2..13), pairs, larger composites like {2,3,5,7,11},
{3,5,7}, {2,13}, {5,7,11,13}, and a "large prime" probe {101}, {97,103}.

Run: python3 821_arithmetic_family_probe.py   (WSL venv: .venv-probe)
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


def outer_leak(primes, Rl, n=600, Lt=8.0, probe='boundary'):
    t = np.linspace(-Lt, Lt, n); dt = t[1]-t[0]
    car = np.where(t >= Rl - 1e-12)[0]; under = np.where(t < Rl - 1e-12)[0]
    T = T_matrix(primes, dt, n, +1); Td = T_matrix(primes, dt, n, -1)
    A = T[:, car]; G = A.conj().T @ A
    Ginv = np.linalg.inv(G + 1e-14*np.eye(len(car)))
    leaks = []
    probes = [0, len(car)//2, len(car)-1] if probe=='interior' else [0]
    for jidx in probes:
        u = np.zeros(n); u[car[jidx]] = 1.0
        Du = Td @ (A @ (Ginv @ (A.conj().T @ u)))
        fn = np.linalg.norm(Du)+1e-30
        leaks.append(np.linalg.norm(Du[under])/fn)
    return float(np.mean(leaks))


def main():
    families = {
        'singles': [ [2],[3],[5],[7],[11],[13] ],
        'pairs':   [ [2,3],[2,5],[3,5],[3,7],[5,7],[7,11],[11,13] ],
        'triples': [ [2,3,5],[2,3,7],[3,5,7],[5,7,11] ],
        'fours':   [ [2,3,5,7],[3,5,7,11],[5,7,11,13] ],
        'large-count': [ [2,3,5,7,11,13], [3,5,7,11,13,17] ],
        'large-prime': [ [101], [97,103], [101,103] ],
    }
    print("Route (a): outer leak vs REAL arithmetic family (logl=0, boundary probe)")
    print(f"{'family':14s} {'primes':<28s} outer_leak")
    for cat, fml in families.items():
        for fam in fml:
            leak = outer_leak(fam, 0.0)
            print(f"{cat:<14s} {str(fam):<28s} {leak:.3f}")


if __name__ == "__main__":
    main()