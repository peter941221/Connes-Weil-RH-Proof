#!/usr/bin/env python3
"""Probe 825 (idea A): does a per-prime WEIGHT renormalization of the finite-Euler
transport factor collapse the outer-channel leak (I-R)oD on the transported-Sonin
frame?

Base measurement is IDENTICAL to 822/824 (transported-Sonin frame, scale-invariant
leak = ||(D-I)u[under]|| / ||Du||).  The only new degree of freedom is a per-prime
relative strength w_p in the transport factor:

    T_w = prod_{p} ( I - p^(-1/2) . w_p . shift_{-log p} )

with w_p = 1 recovering exactly 824.  Because the leak is a ratio, giving the WHOLE
operator a common scale does nothing; only RELATIVE per-prime weights that reshape
the projection D can change the leak.  That is precisely the degree of freedom the
"the outer channel would vanish under the correct normalization" hypothesis names.

w_p = p^(-alpha) has a concrete analytic anchor: alpha=1 -> weight p^-1 (the
ERH/Mertens "each prime weighs 1/p"); alpha=-1 -> weight p (heavier small primes);
alpha=0 -> bench.  We also try w_p = log(p)^-beta and a Mertens PRIME-weight (per
prime count).

Run: python3 825_prime_weight_renormalization_probe.py  (WSL venv .venv-probe)
Expected guard: at alpha=0 the probe must reproduce the 824 number (outer leak
~0.62 for family {2,3,5,7,11,13}, ~0.39/[2], ~0.55/[2,3,5]).  Only re-normalized
configs may move OFF 824's plateau; if all of them stay well above 0, that is a
clean NEGATIVE for idea A (no per-prime weight closes the outer channel).
"""
from __future__ import annotations
import numpy as np
from scipy.signal.windows import dpss


def shift_op_weighted(p, w_p, dt, n, sign):
    sh = int(round(float(np.log(p)) / dt))
    S = np.eye(n)
    amp = w_p * p ** -0.5
    for i in range(n):
        j = i + sign * sh
        if 0 <= j < n:
            S[i, j] -= amp
    return S


def T_matrix(primes, weights, dt, n, sign):
    T = np.eye(n)
    for p, w in zip(primes, weights):
        T = shift_op_weighted(p, w, dt, n, sign) @ T
    return T


def slepian_radial(t, logla, nw, nwant):
    n = len(t); lo = np.searchsorted(t, logla - 1e-12)
    Lwin = min(max(4, int(4 * nw)), max(4, n - lo))
    win = dpss(Lwin, nw, nwant); nc = win.shape[0]
    W = np.zeros((n, nc)); W[lo:lo + Lwin, :] = win.T
    W[t < logla - 1e-12, :] = 0.0
    for k in range(nc):
        nz = np.linalg.norm(W[:, k])
        if nz > 0:
            W[:, k] /= nz
    return W, nc


def weights_alpha(pr, alpha):
    return [p ** (-alpha) for p in pr]


def _inner(pr, weights, logla, n, Lt):
    t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]
    under = t < logla - 1e-12
    T = T_matrix(pr, weights, dt, n, +1)
    Td = T_matrix(pr, weights, dt, n, -1)
    car = np.where(t >= logla - 1e-12)[0]
    A = T[:, car]; G = A.conj().T @ A
    Ginv = np.linalg.pinv(G)
    def d(u): return Td @ (A @ (Ginv @ (A.conj().T @ u)))
    Blk, nc = slepian_radial(t, logla, nw=4, nwant=6)
    leaks = []
    for k in range(nc):
        Bt = T @ Blk[:, k]
        u = Bt / (np.linalg.norm(Bt) + 1e-30)
        du = d(u); fn = np.linalg.norm(du) + 1e-30
        leaks.append(np.linalg.norm(du[under]) / fn)
    return max(leaks)


def main():
    families = {
        "[2]": [2],
        "[2,3,5]": [2, 3, 5],
        "all6": [2, 3, 5, 7, 11, 13],
    }
    print("Probe 825: per-prime weight renormalization of transport factor")
    print("ID matrix: at w_p=1 every family must reproduce 824's floor:")
    print("   [2]~0.39  [2,3,5]~0.55  all6~0.62\n")
    for name, pr in families.items():
        print(f"== family {name}  n=600 L=8 ==")
        print("  [baseline] w_p=1 (must match 824)  leak =",
              f"{_inner(pr, [1.0]*len(pr), 0.0, 600, 8.0):.4f}")
        for alpha in [-1.0, -0.5, 0.5, 1.0, 2.0]:
            w = weights_alpha(pr, alpha)
            print(f"  [w=p^-a] a={alpha:+.1f}  leak = "
                  f"{_inner(pr, w, 0.0, 600, 8.0):.4f}")
        # Mertens-type: weight each prime by 1/log p (equal "spacing" mass)
        w_ml = [1.0 / np.log(p) for p in pr]
        print("  [w=1/logp]  leak =", f"{_inner(pr, w_ml, 0.0, 600, 8.0):.4f}")
        # p^{-1/2} extra (damping small primes by extra sqrt)
        w_h = [p ** -0.5 for p in pr]
        print("  [w=p^-1/2]  leak =", f"{_inner(pr, w_h, 0.0, 600, 8.0):.4f}")
        # accent small primes more strongly (heavier weight = stronger shift)
        w_up = [p ** +0.5 for p in pr]
        print("  [w=p^+1/2]  leak =", f"{_inner(pr, w_up, 0.0, 600, 8.0):.4f}")
        # fine scan of alpha well past a=2 to separate "non-trivial zero inside the
        # family" from "T->I degradation as w_p->0" (the latter converges to 0 only
        # because the whole transport turns off, i.e. TRIVIAL).  A real normalized
        # weight would hit ~0 at a FINITE alpha while T still varies.
        print("  -- monotonicity tail: does the leak hit 0 at FINITE alpha? --")
        for a in [1.5, 2.0, 2.5, 3.0, 4.0, 5.0]:
            w = weights_alpha(pr, a)
            print(f"  [w=p^-a] a={a:.1f}  leak = {_inner(pr, w, 0.0, 600, 8.0):.4f}")
        # resolution guard at the strongest damping: keep a=3, move n
        w3 = weights_alpha(pr, 3.0)
        leak_n600 = _inner(pr, w3, 0.0, 600, 8.0)
        leak_n1200 = _inner(pr, w3, 0.0, 1200, 8.0)
        leak_n2000 = _inner(pr, w3, 0.0, 2000, 8.0)
        print(f"  n-sweep at a=3: n600={leak_n600:.4f} n1200={leak_n1200:.4f} "
              f"n2000={leak_n2000:.4f}  (if this decays, a=3 leak is a box artifact)")
        print()


if __name__ == "__main__":
    main()