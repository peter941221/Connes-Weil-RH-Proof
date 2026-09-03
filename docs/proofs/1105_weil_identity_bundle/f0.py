import math
import numpy as np
from numpy.polynomial.legendre import legvander
from scipy.linalg import eigh
from scipy.signal import fftconvolve

C_ARCH = math.log(4.0 * math.pi) + 0.5772156649015328606   # c0
VANISH_S = (0.0, 0.5, 1.0)

def smooth_bump(x):
    out = np.zeros_like(x); ins = np.abs(x) < 1.0
    out[ins] = np.exp(-1.0 / (1.0 - x[ins] ** 2)); return out

def simpson(n, h):
    w = np.ones(n); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0; return w * h / 3.0

def lam_sieve(bound):
    lam = np.zeros(bound + 1); sieve = np.ones(bound + 1, dtype=bool)
    for p in range(2, bound + 1):
        if sieve[p]:
            sieve[p::p] = False
            pw = p
            while pw <= bound:
                lam[pw] = math.log(p); pw *= p
    return lam

def null_setup(a, K, n=4001, drop_moments=()):
    """V-basis: Legendre x bump on [-a,a], L2-orthonormal, with
    selected moment rows dropped (ablation P-3)."""
    t = np.linspace(-a, a, n); h = t[1] - t[0]
    x = t / a
    basis = (legvander(x, K - 1).T * smooth_bump(x)).astype(float)
    quad = simpson(n, h)
    rows = [np.sum(quad * basis * np.exp(s * t)[None, :], axis=1)
            for s in VANISH_S if s not in drop_moments]
    if rows:
        M = np.stack(rows)
        _, sv, vh = np.linalg.svd(M, full_matrices=True)
        rank = int(np.sum(sv > 1e-11 * max(float(sv[0]), 1.0)))
        wn = (basis.T * math.sqrt(h)) @ vh[rank:].T
        q, r = np.linalg.qr(wn, mode="reduced")
        coeffs = vh[rank:].T @ np.linalg.inv(r)
    else:  # ablation: no constraints, orthonormalize the full basis
        q, r = np.linalg.qr(basis.T * math.sqrt(h), mode="reduced")
        coeffs = np.linalg.inv(r)
    return t, h, coeffs, basis

def arch_of(f, h):
    """arch quadratic form of one grid function (first-cell corrected)."""
    corr = fftconvolve(f[::-1], f, mode="full") * h
    lags = h * np.arange(-(f.size - 1), f.size)
    f0 = corr[f.size - 1]
    y = lags[f.size:]; fy = corr[f.size:]
    num = np.expm1(y / 2.0) * fy + (fy - f0)
    body = float((np.trapezoid if hasattr(np, "trapezoid") else np.trapz)(
        num / np.sinh(y), y))
    f1 = corr[f.size]
    i1 = (np.expm1(h / 2.0) * f1 + (f1 - f0)) / np.sinh(h)
    first = h * (f0 / 2.0 + i1) / 2.0
    tail = f0 * math.log(math.tanh(abs(lags[-1]) / 2.0))
    return C_ARCH * f0 + body + first + tail

def arch_matrix(funcs, h):
    d = len(funcs)
    diag = np.array([arch_of(f, h) for f in funcs])
    A = np.diag(diag).copy()
    for i in range(d):
        for j in range(i):
            A[i, j] = A[j, i] = 0.5 * (arch_of(funcs[i] + funcs[j], h)
                                       - diag[i] - diag[j])
    return (A + A.T) / 2.0

def shifted_values(coeffs, basis, t, h, a, K, xi):
    tp = t + xi; x = tp / a; ins = np.abs(x) < 1.0
    vals = np.zeros((K, t.size)); xs = x[ins]
    if xs.size:
        vals[:, ins] = (legvander(xs, K - 1).T * smooth_bump(xs))
    return coeffs.T @ vals

def prime_matrix(funcs, coeffs, basis, t, h, a, K,
                 shifts=None, weights=None):
    if shifts is None and weights is None:   # both given (even []) = override
        two_r = 2.0 * a
        bound = int(math.floor(math.exp(two_r)))
        lam = lam_sieve(bound)
        pairs = [(q, lam[q] / math.sqrt(q)) for q in range(2, bound + 1)
                 if lam[q] > 0 and math.log(q) < two_r - 1e-9]
        shifts = [math.log(q) for q, _ in pairs]
        weights = [w for _, w in pairs]
    d = len(funcs)
    P = np.zeros((d, d))
    for xi, w in zip(shifts, weights):
        sh = shifted_values(coeffs, basis, t, h, a, K, xi)
        P += (2.0 * w) * (h * (funcs @ sh.T))
    return (P + P.T) / 2.0

def tops(a, K, n=4001, drop_moments=(), scale=1.0,
         shifts=None, weights=None):
    t, h, coeffs, basis = null_setup(a, K, n, drop_moments)
    funcs = coeffs.T @ basis
    A = arch_matrix(funcs, h)
    P = prime_matrix(funcs, coeffs, basis, t, h, a, K, shifts, weights)
    ev = lambda m: eigh((m + m.T) / 2.0, np.eye(m.shape[0]), eigvals_only=True)
    res = dict(top_total=float(ev(A + scale * P)[-1]),
               top_arch=float(ev(A)[-1]),
               top_prime=float(ev(P)[-1]),
               min_prime=float(ev(P)[0]))
    res["top_arch_minus_prime"] = float(ev(A - scale * P)[-1])
    return res
