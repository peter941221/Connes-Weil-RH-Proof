#!/usr/bin/env python3
# Record 1695 rig: heq numerical truth check (the sign face de-risk).
#
# heq (C1G8R5AggregateExpansion.lean:327):
#   Re tr_carrier( A_end ) = qw(g),
#   A_end = J^dag C^dag (id+N) W (id+N)^dag C J   (four-term form :273; = D^dag D,
#          D = C (id+N)^dag C, positive by :112)
# Operator stack, pinned from committed defs (F27/F28 hand derivation, rig = CHECK):
#   C = cc20GlobalLogConvolution h            (GlobalLogConvolution.lean:43)
#       = convolution by h, (Cf)(t) = int h(s) f(t-s) ds   [Mathlib FT: e^{-2 pi i x xi},
#        fourierIntegral_eq_integral_exp_smul, FourierTransform.lean:375]
#   h = g.involution.test = conj g(-t)        (CompactLogConvolution.lean:73)
#   W = detectorOperator = C^dag C            (ConvolutionCrossing.lean:22)
#   N = finiteEulerPulledTargetProjection - sourceSoninProjection
#     = E^{-1} P_target E - P_source          (PulledObliqueReduction.lean:51,
#                                              GatePhysicalObliqueShearReduction.lean:92)
#   E = E_2 = id - (1/sqrt 2) T_{-log 2},  (T_b u)(t) = u(t+b)
#                                             (EulerTransport.lean:33,70-85,
#                                              GlobalLogCrossing.lean:140-143)
#   P_source = proj { supp u subset [a,inf), supp(Hu) subset [a,inf) },  a = log lambda
#                                             (LogRadialSupport.lean:48 = ker lower
#                                              restriction; HardyTitchmarsh.lean:374-380)
#   P_target = proj { radial meet E_2(archFourier) }     (SemilocalFourierSupport.lean:134
#                                              + ccm24FiniteEulerTransport_maps_fourierSupport)
#   H readback (Tu)^ = m(xi) (Fu)(-xi)        (HardyTitchmarsh.lean:340-344)
#     => H_grid[f,k] = (1/N) sum_j m(xi_j) exp(+2 pi i xi_j (t_f+t_k))   (= the 1694 v4 matrix)
#   m(xi) = GammaR(1/2-2 pi i xi)/GammaR(1/2+2 pi i xi),
#           GammaR(s) = pi^{-s/2} Gamma(s/2)  (Mathlib Deligne.lean:43; = 1694 rig verbatim)
# qw (C1SameOwnerWeil.lean:31-64,145-162,196):
#   qw(g) = psi(F), F = g^* * g (autocorrelation, CompactLogConvolution.lean:114-119)
#   psi(F) = poleTerm(F) - archimedeanTerm(F) - finitePrimeSum(F)
#   poleTerm(F)  = Re( laplaceAt F (1/2) + laplaceAt F (-1/2) ) = 4 int_0^c F cosh(t/2)
#   arch(F)      = Re( (log 4pi + gamma) F(0) + int_0^inf [e^{y/2}(F(y)+F(-y))-2F(0)]
#                      /(e^y-e^{-y}) dy )
#   finite(F)    = sum over prime powers n of Lambda(n)/sqrt(n) (F(log n)+F(-log n))
# Instance: lambda* = e^{-1} (a=-1), g = even real C_c^inf bump support [-0.42,0.42],
# family = {(2,1)} (only prime power inside supp F).  Controls: F66 orientation
# discriminator (m vs conj m in the H slot), N-stability, dimension bookkeeping.

import json
import numpy as np
from scipy.integrate import quad
from scipy.special import gamma as cgamma

TWO_PI = 2.0 * np.pi
LOG2 = float(np.log(2.0))
EULER_GAMMA = 0.57721566490153286060651209008240243


def scattering_phase(xi, conj_m=False):
    """Committed ccm24ArchimedeanScatteringPhase(xi) = GammaR(1/2-2pi i xi)/GammaR(1/2+2pi i xi)."""
    s = 0.5 + TWO_PI * 1j * xi
    gr = np.pi ** (-0.5 * s) * cgamma(0.5 * s)          # = GammaR(s), Deligne form
    m = np.conj(gr) / gr
    return np.conj(m) if conj_m else m


def bump(t, c):
    """Even real C_c^inf bump, support [-c, c]."""
    x = np.abs(np.asarray(t, dtype=float)) / c
    return np.where(x < 1.0, np.exp(-1.0 / np.maximum(1e-300, 1.0 - x * x)), 0.0)


def hardy_titchmarsh_matrix(t, xi, m):
    """H_grid[f,k] = (1/N) sum_j m(xi_j) exp(+2 pi i xi_j (t_f+t_k))  (v4 matrix)."""
    E = np.exp(TWO_PI * 1j * np.outer(t, xi))
    return (E * m[None, :]) @ E.T / len(t)


def shift_matrix(t, xi, b):
    """T_b with (T_b u)(t) = u(t+b): periodic band-limited interpolant
    (1/N) E_plus diag(e^{+2 pi i xi b}) E_minus."""
    E_plus = np.exp(TWO_PI * 1j * np.outer(t, xi))
    E_minus = np.exp(-TWO_PI * 1j * np.outer(t, xi))
    return (E_plus * np.exp(TWO_PI * 1j * xi * b)[None, :]) @ E_minus / len(t)


def conv_matrix(t, h_of_s, dt):
    """(Cf)(t) = int h(s) f(t-s) ds as circulant: C[f,k] = dt h(t_k - t_m)."""
    diff = t[:, None] - t[None, :]
    return dt * h_of_s(diff)


def null_space(A, svd_tol=1e-10):
    """Right null space ONB (columns) of A."""
    _, s, Vh = np.linalg.svd(A, full_matrices=True)
    rank = int(np.sum(s > svd_tol * (s[0] if len(s) and s[0] > 0 else 1.0)))
    return Vh.conj()[rank:, :].T, rank


def run(N=1024, T=16.0, a=-1.0, conj_m=False, c=0.42):
    dt = 2.0 * T / N
    t = -T + dt * np.arange(N)
    xi = np.fft.fftfreq(N, d=dt)
    rows = t < a - 1e-12

    g = bump(t, c)
    g /= np.linalg.norm(g) * np.sqrt(dt)               # L2-normalize on the grid
    h_of_s = lambda s: bump(s, c) / (np.linalg.norm(bump(t, c)) * np.sqrt(dt))
    # h(t) = g(-t) = g(t) (even); keep the normalized sample for consistency checks
    h = g[::-1]

    m = scattering_phase(xi, conj_m=conj_m)
    H = hardy_titchmarsh_matrix(t, xi, m)
    C = conv_matrix(t, h_of_s, dt)
    W = C.conj().T @ C
    S = shift_matrix(t, xi, -LOG2)                     # T_{-log 2}
    E = np.eye(N, dtype=complex) - (1.0 / np.sqrt(2.0)) * S
    Einv = np.linalg.inv(E)

    # P_source: meet = {supp u in [a,inf)} cap {Hu in [a,inf)}  (v4, inside support coords)
    supp = ~rows
    n_s = int(supp.sum())
    A_s = H[np.ix_(rows, supp)]
    Q_s, _ = null_space(A_s)                           # (n_s, d_meet) meet basis, support coords
    dim_meet = Q_s.shape[1]
    Q_c = np.zeros((N, dim_meet), dtype=complex)
    Q_c[np.ix_(supp, np.arange(dim_meet))] = Q_s
    P_source = Q_c @ Q_c.conj().T

    # archFourier = ker(R_neg H), full grid
    Q_f, _ = null_space(H[rows, :])
    dim_af = Q_f.shape[1]

    # target = radial meet E_2(archFourier): u = E_2(Q_f c) supported in [a,inf)
    W_cols = E @ Q_f
    A_t = W_cols[rows, :]
    nullc, _ = null_space(A_t)
    Z = W_cols @ nullc
    # orthonormalize inside the support coordinates to kill roundoff leakage
    Q_t = np.zeros_like(Z)
    Q_t[supp, :] = orthonormalize(Z[supp, :])
    dim_target = Q_t.shape[1]
    P_target = Q_t @ Q_t.conj().T

    Nop = Einv @ P_target @ E - P_source
    I = np.eye(N, dtype=complex)
    A_end = C.conj().T @ (I + Nop) @ W @ (I + Nop).conj().T @ C
    lhs = float(np.trace(Q_c.conj().T @ A_end @ Q_c).real)
    hcore = float(np.trace(Q_c.conj().T @ W @ Q_c).real)   # sum_i ||J^dag C J e_i||^2

    # RHS: F = g * g (autocorrelation) on a fine direct grid
    M = 4096
    tf = np.linspace(-2.0, 2.0, M)
    df = tf[1] - tf[0]
    gf = bump(tf, c)
    gf /= np.sqrt(np.sum(gf * gf) * df)
    Fs = df * np.array([np.sum(gf * np.interp(tf - x, tf, gf, left=0.0, right=0.0))
                        for x in tf])
    F0 = float(Fs[np.argmin(np.abs(tf - 0.0))])
    Flog2 = float(np.interp(LOG2, tf, Fs))
    F_at = lambda x: float(np.interp(x, tf, Fs, left=0.0, right=0.0))
    pole = 4.0 * quad(lambda y: F_at(y) * np.cosh(y / 2.0), 0.0, 0.84, limit=400)[0]

    def integrand(y):
        num = np.exp(y / 2.0) * (F_at(y) + F_at(-y)) - 2.0 * F0
        den = np.exp(y) - np.exp(-y)
        if den < 1e-12:
            return F0 / 2.0                            # removable singular: num ~ y F0
        return num / den
    arch = (np.log(4.0 * np.pi) + EULER_GAMMA) * F0 + \
        quad(integrand, 0.0, 0.84, limit=400)[0]
    finite = (LOG2 / np.sqrt(2.0)) * (Flog2 + Flog2)   # only n=2 in supp F
    rhs = pole - arch - finite

    return dict(N=N, a=a, conj_m=conj_m, dim_meet=dim_meet, dim_archF=dim_af,
                dim_target=dim_target, lhs=lhs, hcore=hcore, pole=pole,
                arch=arch, finite=finite, rhs=rhs,
                ratio=(lhs / rhs if abs(rhs) > 1e-14 else float("nan")))


def orthonormalize(Z, tol=1e-9):
    if Z.shape[1] == 0:
        return np.zeros((Z.shape[0], 0), dtype=complex)
    U, s, _ = np.linalg.svd(Z, full_matrices=False)
    keep = s > tol * (s[0] if s[0] > 0 else 1.0)
    return U[:, keep]


def main():
    print("== heq truth check: Re tr_carrier(A_end)  vs  qw(g) ==")
    print("   lambda*=e^{-1} (a=-1), g=even bump supp 0.42, family={(2,1)}")
    results = []
    for conj_m in (False, True):
        for N in (1024, 2048):
            r = run(N=N, conj_m=conj_m)
            results.append(r)
            tag = "m       " if not conj_m else "conj m  "
            print(f"  {tag} N={N:5d}: dims (meet/archF/target)="
                  f"{r['dim_meet']}/{r['dim_archF']}/{r['dim_target']}  "
                  f"LHS={r['lhs']:+.8f}  qw={r['rhs']:+.8f}  "
                  f"ratio={r['ratio']:.6f}  [hcore={r['hcore']:.6f}]")
            print(f"           pole={r['pole']:+.6f} arch={r['arch']:+.6f} "
                  f"finite={r['finite']:+.6f}")
    with open("results/1695_heq_trace_check.json", "w") as f:
        json.dump(results, f, indent=1)
    print("saved results/1695_heq_trace_check.json")


if __name__ == "__main__":
    main()
