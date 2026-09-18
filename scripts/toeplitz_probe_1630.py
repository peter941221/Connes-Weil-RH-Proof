#!/usr/bin/env python3
"""1630 numeric, map 043 item 4: finite-section probe of the Toeplitz kernel.

Committed carrier base (1629 sec 3, map 043 line 88), the form this rig probes:

    carrier != {0}   <=>   exists H in H^2(C_+) \\ {0}  with  U . H in H^2(C_-),
    U(xi) = e^{4 pi i (log lambda) xi} m(-xi) = e^{2 pi i c xi} m(-xi),
    c = 2 log lambda <= 0,   m(-xi) = 1/m(xi) = conj(m(xi))   (|m| = 1).

Dictionary used here (validated by the two model calibrations below, which the
rig asserts): with the transform  F(h)(xi) = INT h(u) e^{-2 pi i u xi} du,

    H^2(C_+)  <->  supp F^{-1}(H) subset (-inf, 0]  <->  H has xi-spectrum in
                                                         eta > 0,
    H^2(C_-)  <->  supp F^{-1}(G) subset [0, inf)   <->  G has eta < 0,

where eta is the conjugate variable of xi (so P_{C_+} = keep eta > 0 is one
line of FFT masking).  The finite section is the translate family

    H_j(xi) = e^{2 pi i j xi} H(xi) = F(h(. + j))(xi),   j = 0 .. K-1,

for one fixed C^inf bump h supported in [-1, 0] (so every H_j in H^2(C_+) and
-the finite-type shadow: h compactly supported, H_j of exponential type).  The
section matrix of the Toeplitz operator  T_U = P_{C_+} M_U P_{C_+}  is

    M_{jk} = <P_{C_+}(U H_j), P_{C_+}(U H_k)>,   N_{jk} = <H_j, H_k>,

and the probe reports  sigma_min(K) = sqrt(smallest generalized eigenvalue of
(M_K, N_K)) = the smallest relative defect  ||P_{C_+}(U H)|| / ||H||  over the
section.  sigma_min is exactly 0 iff the section contains a finite-type
witness, which record 1627 proved does not exist (no witness of finite
exponential type); the informative content is therefore the *decay rate* of
sigma_min(K): a plateau is evidence that the base is not merely unattained but
not approximable either; a power-law decay toward the numerical floor is
evidence for the opposite.  Calibrations:

  model m := 1, c = -2 (lambda = e^{-1}): the exact finite-type witness
      h(.-1)+h(.-2)-type span {H_0, H_1} satisfies U H in H^2(C_-) exactly,
      so sigma_min(K >= 2) must sit on the numerical floor;
  model m := 1, c = 0 (lambda = 1):  U = 1, so P_{C_+}(U H_j) = H_j and
      sigma_min(K) = 1 exactly, for every K.

Run: WSL, numpy (+ scripts/rh_symbol_num for m).  Deterministic.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

# N = 2**NBITS samples on the spatial window [-(N*DU)/2, (N*DU)/2); DU fixed, so
# the xi-window is always |xi| <= 1/(2 DU) = 64 and refining NBITS only shrinks
# dxi = 1/(N DU) and raises the eta-resolution 1/(2 dxi).  Running with larger
# NBITS is the floor calibration: the model case below has an exact witness, so
# its sigma_min is a pure measure of the pipeline's numerical floor.
NBITS = int(sys.argv[1]) if len(sys.argv) > 1 else 15
DU_DEN = int(sys.argv[2]) if len(sys.argv) > 2 else 128
N = 1 << NBITS
DU = 1.0 / DU_DEN
U_W = N * DU / 2.0
XI_MAX = 1.0 / (2.0 * DU)
DXI = 1.0 / (N * DU)
ETA = np.fft.fftfreq(N, d=DXI)
POS = ETA > 0                    # H^2(C_+) mask
KS = [1, 2, 4, 8, 16, 32, 48]
LOG_PI = float(np.log(np.pi))


def bump(u):
    """C^inf bump supported on [-1, 0], peak 1 at -1/2."""
    out = np.zeros_like(u)
    inside = (u > -1.0) & (u < 0.0)
    s = 2.0 * (u[inside] + 0.5)
    out[inside] = np.exp(1.0 - 1.0 / (1.0 - s * s))
    return out


def proj_pos(f):
    """P_{C_+}: keep xi-spectrum with eta > 0 (samples in fftfreq order)."""
    spec = np.fft.fft(np.fft.fftshift(f))
    return np.fft.ifftshift(np.fft.ifft(np.where(POS, spec, 0.0)))


def generalized_sigma_min(M, Nrm):
    """sqrt of the smallest generalized eigenvalue of (M, Nrm), Nrm > 0."""
    L = np.linalg.cholesky(Nrm)
    Y = np.linalg.solve(L, M)
    T = np.linalg.solve(L, Y.conj().T).conj().T
    T = 0.5 * (T + T.conj().T)
    ev = np.linalg.eigvalsh(T)
    return float(np.sqrt(max(ev[0], 0.0)))


def run(name, lam, model_symbol, xi_grid, h, m_minus):
    c = 2.0 * float(np.log(lam))
    H0 = np.fft.fft(np.fft.fftshift(h)) * DU           # H at xi_k = fftfreq(N, DU)
    if model_symbol:
        U = np.exp(2j * np.pi * c * xi_grid)
    else:
        U = np.exp(2j * np.pi * c * xi_grid) * m_minus
    Hj = [np.exp(2j * np.pi * j * xi_grid) * H0 for j in range(max(KS))]
    proj = [proj_pos(U * H) for H in Hj]
    print("setting: %s   (lambda = %s, c = 2 log lambda = %s)"
          % (name, repr(lam), repr(round(c, 6))))
    print("  K   sigma_min(K)      D[H_0]        D[H_1]        D[H_2]")
    for K in KS:
        M = np.empty((K, K), dtype=complex)
        Nrm = np.empty((K, K), dtype=complex)
        for a in range(K):
            for b in range(K):
                M[a, b] = DXI * np.vdot(proj[a], proj[b])
                Nrm[a, b] = DXI * np.vdot(Hj[a], Hj[b])
        s = generalized_sigma_min(M, Nrm)
        ds = []
        for j in range(min(3, K)):
            ds.append(np.linalg.norm(proj[j]) / np.linalg.norm(Hj[j]))
        # norm of the finite-type test functions on the window (sanity)
        print("  %2d   %12.6e   %12.6e  %12.6e  %12.6e"
              % (K, s, ds[0], ds[1] if len(ds) > 1 else float("nan"),
                 ds[2] if len(ds) > 2 else float("nan")))
    # single-function absolute checks
    nrm = np.linalg.norm(Hj[0])
    full = np.linalg.norm(U * Hj[0])
    print("  single H_0: ||H|| = %.10f, ||U H|| = %.10f, ||P_+ U H||/||H|| = %.6e"
          % (nrm, full, np.linalg.norm(proj[0]) / nrm))
    print("  ||P_+ U H|| / ||U H|| = %.6e  (1 == purely analytic in C_+)"
          % (np.linalg.norm(proj[0]) / full))
    print()
    return


def main():
    u = -U_W + np.arange(N) * DU
    xi = np.fft.fftfreq(N, d=DU)
    h = bump(u)
    m_minus = np.conj(m_of_real(xi))       # m(-xi) = 1/m(xi) = conj(m(xi))
    print("Toeplitz finite-section probe, N = %d, du = %s, xi in [%s, %s), dxi = %s"
          % (N, DU, -XI_MAX, XI_MAX, DXI))
    print("eta grid: |eta| <= %s;  ||h|| = %.10f, h support in [-1, 0]"
          % (1.0 / (2.0 * DXI), np.linalg.norm(h)))
    print()
    run("model m = 1, lambda = e^-1  (witness expected: sigma_min -> floor)",
        1.0 / np.e, True, xi, h, m_minus)
    run("model m = 1, lambda = 1     (no witness: sigma_min = 1)",
        1.0, True, xi, h, m_minus)
    run("model m = 1, lambda = 1/2", 0.5, True, xi, h, m_minus)
    run("real  m,     lambda = 1", 1.0, False, xi, h, m_minus)
    run("real  m,     lambda = 1/2", 0.5, False, xi, h, m_minus)
    run("real  m,     lambda = 1/e", 1.0 / np.e, False, xi, h, m_minus)
    run("real  m,     lambda = 0.1", 0.1, False, xi, h, m_minus)
    run("real  m,     lambda = 0.01", 0.01, False, xi, h, m_minus)


if __name__ == "__main__":
    main()