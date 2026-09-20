#!/usr/bin/env python3
# Debug v2: validator-g scale check + D3-root cross-check on the padded grid.
import numpy as np
import sys
sys.path.insert(0, "/home/peter/rh/scripts")
from arch_eigen_1700 import (build_M, star_square, arch_direct, moment_matrix,
                             N_PAD, A_COEF)

w = 0.29
xgrid = -4.0 * w + (8.0 * w) / N_PAD * np.arange(N_PAD)
dx = xgrid[1] - xgrid[0]
act = np.abs(xgrid) <= w + 1e-12
M = build_M(xgrid, w)
print("M diag[0] =", M[0, 0], " (expect ~ A*dx - 2*dx*wall.sum ~ small)")

rng = np.random.default_rng(7)
xa = xgrid[act]
Cm = moment_matrix(xa, dx)
pinvCC = np.linalg.pinv(Cm @ Cm.T)
gv = rng.standard_normal(len(xgrid)) * act
for _ in range(2):
    gv[act] = gv[act] - Cm.T @ (pinvCC @ (Cm @ gv[act]))
gvn = gv / (np.linalg.norm(gv) * np.sqrt(dx))
mom = Cm @ gvn[act]
print("gvn mass =", dx * gvn @ gvn, " moments =", mom)
F = star_square(gvn, dx)
print("F0 =", F[0].real, " q_dir(gvn) =", arch_direct(gvn, xgrid),
      " q_form(gvn) =", float(gvn @ M @ gvn))

# D3 root of the even bump, padded grid, L2-normalized: expect arch ~ -2.7
t = xgrid
hh = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (t / w) ** 2)) * (np.abs(t) < w)
hh /= np.linalg.norm(hh) * np.sqrt(dx)
kk = 2.0 * np.pi * 1j * np.fft.fftfreq(N_PAD, d=dx)
dsh = lambda u, a: np.fft.ifft(kk * np.fft.fft(u)) + a * u
g = dsh(dsh(dsh(hh, 1.0 + 0j), 0.5 + 0j), 0.0j)
g = g / (np.linalg.norm(g) * np.sqrt(dx))
gm = Cm @ g[act]
print("D3 root moments (want 0):", gm)
print("D3 root q_dir =", arch_direct(g, xgrid),
      " q_form =", float(np.real(g @ M @ g)))
