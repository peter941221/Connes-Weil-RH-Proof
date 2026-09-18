#!/usr/bin/env python3
"""1633 (map 043 item 3, stage 2): real defect vs same-family floor, per lambda.

Stage 1 (carrier_scaling_1633.py) used indicator pixels; their built-in
L2-approximation error (~(cell)^{3/2}) is ~1e-2, so every reading was
approximation-limited (law F43: a rig floor is a rig property).

The honest calibration runs the SAME family at the SAME lambda twice:

    model  m := 1   ->  U is a pure shift, so the reading is the family's
                        floor under the shift by |c| = 2|log lambda|;
    real   m        ->  the object reading.

The floor only informs if the model's exact witness is NOT in the family.
A bump of width W with |c| >= W lands fully on x > 0, so a family of
width-W translates has floor 0 for |c| >= W: degenerate.  Wide trial
functions (W > |c|) are what make the floor live, and they are also the
right probe, because the obstruction is exactly the part of the trial
function that reaches beyond the shift.

Prediction key:
    real ~ floor at every lambda and every width   ->  P1 (B1: the symbol
        obstructs no more than the pure shift does);
    real / floor -> infinity, with a stable power law sigma_min ~ lambda^p
        that survives refinement                    ->  P2 (B2: the
        m-distortion is the whole obstruction).

Family: unit-L2 C^inf bump of width W on [-W, 0], translates at spacing
W/2 over a window, for W in {1, 2, 4, 8, 16}.  Everything is done in the
xi-picture on one grid: F(h)(xi) = fft(h)*du, u = F^{-1}(U * F(h)) with
U = exp(2 pi i c xi) * m(-xi) (real) or U = exp(2 pi i c xi) (model),
D(v) = ||P_{x<0} u_v|| / ||u_v||; sigma_min = sqrt(min gen-eig of (A, M))
with A_ij = <P_{x<0} u_i, P_{x<0} u_j>, M_ij = <u_i, u_j> (Parseval: the
xi-sum carries DXI, not DU -- the stage-1 draft got this wrong and every
value was low by sqrt(du/dxi) = 1/sqrt(2)).

Run: WSL, uv run --with numpy --with scipy --with mpmath python <this file>.
"""

import numpy as np
import scipy.linalg as sla
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rh_symbol_num import m_of_real  # noqa: E402

N = 1 << 15
DU = 1.0 / 128.0
DXI = 1.0 / (N * DU)
XI = np.fft.fftfreq(N, d=DU)
X = np.fft.fftfreq(N, d=DXI)
NEG = X < 0.0


def bump_of_width(W):
    """C^inf bump supported on [-W, 0], L2 norm 1 in the du-grid sense."""
    out = np.zeros_like(X)
    inside = (X > -W) & (X < 0.0)
    s = 2.0 * (X[inside] / W + 0.5)
    out[inside] = np.exp(1.0 - 1.0 / (1.0 - s * s))
    nrm = np.sqrt(np.sum(out ** 2) * DU)
    return out / nrm


def family_shifts(W, window):
    """Translate positions: spacing W/2 over [-window, 0]."""
    step = W / 2.0
    n = int(round(window / step))
    return np.arange(-n, 0.5) * step


def hats(W):
    h = bump_of_width(W)
    hh = np.fft.fft(h) * DU
    return hh


def span_reading(U, hh, shifts):
    """sigma_min over the span of the given translates, for symbol U."""
    n = len(shifts)
    cols = np.empty((n, int(NEG.sum())), dtype=complex)
    for i, k in enumerate(shifts):
        G = U * (hh * np.exp(-2j * np.pi * k * XI))
        cols[i, :] = np.fft.ifft(G)[NEG] / DU
    A = (cols.conj() @ cols.T) * DU
    A = 0.5 * (A + A.conj().T)
    dk = shifts[:, None] - shifts[None, :]
    M = np.empty((n, n), dtype=complex)
    base = np.conj(hh) * hh
    for i in range(n):
        M[i, :] = np.sum(base[None, :]
                         * np.exp(2j * np.pi * XI[None, :] * dk[i, :][:, None]),
                         axis=1) * DXI
    M = 0.5 * (M + M.conj().T)
    w = sla.eigh(A, M, eigvals_only=True)
    return float(np.sqrt(max(w[0], 0.0)))


def main():
    m_minus = np.conj(m_of_real(XI))
    m_model = np.ones_like(XI)
    widths = [1.0, 2.0, 4.0, 8.0, 16.0]
    fams = {}
    for W in widths:
        sh = family_shifts(W, 24.0)
        fams[W] = (hats(W), sh)
        print("family W = %4.1f : %2d translates at spacing %.2f over [%.0f, 0]"
              % (W, len(sh), W / 2.0, -24.0))
    print()
    print("item = sigma_min of the span; floor_W = same family, model m := 1")
    print()

    lams = [1.0, 0.5, 1.0 / np.e, 0.2, 0.1, 0.05, 0.02, 0.01]
    for lam in lams:
        c = 2.0 * np.log(lam)
        mod = np.exp(2j * np.pi * c * XI)
        print("lambda = %-8g  |c| = %.3f" % (lam, -c))
        print("   +--------+--------------+--------------+-----------+")
        print("   |   W    |  floor_W     |  real_W      |  real/floor|")
        print("   +--------+--------------+--------------+-----------+")
        for W in widths:
            hh, sh = fams[W]
            fl = span_reading(mod * m_model, hh, sh)
            re = span_reading(mod * m_minus, hh, sh)
            ratio = re / fl if fl > 1e-300 else float("inf")
            print("   | %6.1f | %12.4e | %12.4e | %9.2e |" % (W, fl, re, ratio))
        print("   +--------+--------------+--------------+-----------+")
        print()

    print("cross-check of the 1630 probe D[H_0] column (single vector, W = 1, k = 0):")
    hh1 = fams[1.0][0]
    for lam in [1.0, 0.5, 1.0 / np.e, 0.1]:
        c = 2.0 * np.log(lam)
        u = np.fft.ifft(np.exp(2j * np.pi * c * XI) * m_minus * hh1) / DU
        d = np.linalg.norm(u[NEG]) / np.linalg.norm(u)
        print("    lambda = %-6g D[H_0] = %.6e" % (lam, d))


if __name__ == "__main__":
    main()