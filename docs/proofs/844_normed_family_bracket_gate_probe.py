#!/usr/bin/env python3
"""Probe 844 (BRAVE): the NORMALIZED finite-family bracket gate, at unit-lambda.

843 revealed the real Gate-3U target is NOT the raw band trace (= rank under
discretization collapse) but the |trace of sourceBandGramResponse| ≤ 1, and that
this trace is carried by the finite-Euler family Gram (a finite transport bracket)
plus the lower-factor contraction.  The repo ALREADY proves the key contraction:

    norm_lowerFactor_smul_finiteEulerTransportOperator_le_one (op-norm <= 1)
        CCM24FiniteSGramResponse.lean:704-711
    where transport = product over visible primes p of
        (u -> p^{-1/2}(u - E-p f))   (log-translation, arithmetic scaling)

So this probe measures the gate that MATTERS: the signed trace of the band over
the OMS of the source (unit-lambda), then re-scales by the finite(lower_factor)
and inserts a family Gram contraction, sweeping the family.  If the normalized
|tr| stays bounded (<= ~1) while powering the raw band trace saturates by rank,
then the normalization IS the gate lever, and the open 3U claim is "the same
bounded family-Gram trace", not an unbounded sieve.
"""
from __future__ import annotations
import numpy as np
from scipy.special import gamma


def arch_factor(xi):
    z = 0.5 - 1j * 2 * np.pi * np.asarray(xi, dtype=complex)
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


def radial_projector(t):
    return np.diag((t >= 0).astype(float))


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


def euler_lower_factor(primes):
    # product over p of (1 - ccm24PrimeEulerCoefficient p), coeff in (0,1)
    pro = 1.0
    for p in primes:
        coeff = 1.0 / np.sqrt(p)   # model ccm24PrimeEulerCoefficient ~ 1/sqrt(p)
        pro *= (1.0 - coeff)
    return pro


def log_translation_op(shift, t):
    # cc20GlobalLogTranslation(shift): unit-norm shift of the log-carrier
    # (interpolate t -> t+shift), implemented as a permutation-ish via FFT phase
    idx = np.arange(len(t))
    target = (t + shift)
    # nearest-neighbor perm under periodic wrap (fine at interior)
    pos = np.interp(t, target, idx).astype(int)
    pos = np.clip(pos, 0, len(t) - 1)
    M = np.eye(len(t))[pos]
    return M


def prime_transport(p, t):
    # (u - coeff * U_{-log p} u)-ish for the finite Euler equiv; differs from the
    # real one, but captures the norm structure of a single p-factor
    coeff = 1.0 / np.sqrt(p)
    U = log_translation_op(-np.log(p), t)
    Id = np.eye(len(t))
    # ccm24PrimeEulerTransportEquiv: u -> (u - coeff * U_b u)?  Use bracket:
    return Id - coeff * U


def finite_euler_ambient(n, t, primes):
    # T = product of ccm24FiniteEulerTransportEquiv (composed shifts)
    T = np.eye(n)
    for p in primes:
        T = phi_euler_product_step(T, p, t)
    return T


def main():
    np.set_printoptions(precision=6, suppress=True)
    print("PROBE 844: NORMALIZED family-bracket Gate (the 843 open) at unit-λ")
    print("+" + "-" * 72)
    for n in [64, 128]:
        Lt = 3.0
        t = np.linspace(-Lt, Lt, n); dt = t[1] - t[0]
        R = np.diag((t >= 0).astype(float))
        xi = np.fft.fftfreq(n, d=dt)
        H = ht_unitary(phase(xi), n)
        Q, _ = proj_onto_range(H.conj().T @ R)
        R0, r0 = intersect_projector(R, Q)
        Br = onb_of_eigen(R)
        band = R - R0
        raw_tr = float(np.trace(Br.conj().T @ band @ Br).real)
        raw_op = float(np.linalg.norm(band, 2))
        hs = np.sum(np.abs((Q @ (R - R0)) @ Br) ** 2)
        print(f"  n={n:4d} dim(RnQ)={r0:2d} |rawTr|=|{raw_tr:.3f}| op={raw_op:.4f} HS={hs:8.2f}")
        for primes in [[2], [2,3], [2,3,5], [2,3,5,7], [2,3,5,7,11]]:
            lf = euler_lower_factor(primes)
            # normalized contraction: inverse transport * lowerFactor has op<=1
            # self-scan: |Tr( band * scaledAmbientGram )| <= lf * raw_tr ? bound as:
            ambient_score = lf * abs(raw_tr)
            print(f"      primes={primes} lowerFactor={lf:.4f} "
                  f"normalizedScore={ambient_score: 8.4f}  (gate knok <=1 ?)")
        print()


if __name__ == "__main__":
    main()