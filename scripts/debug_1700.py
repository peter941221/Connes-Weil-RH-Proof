#!/usr/bin/env python3
# Debug for arch_eigen_1700: isolate form-vs-direct discrepancy.
import numpy as np
from scipy.linalg import circulant
import sys
sys.path.insert(0, "/home/peter/rh/scripts")
from arch_eigen_1700 import build_M, star_square, arch_direct, A_COEF, N_PAD

w = 0.29
xgrid = -4.0 * w + (8.0 * w) / N_PAD * np.arange(N_PAD)
dx = xgrid[1] - xgrid[0]
plain = np.exp(-1.0 / np.maximum(1e-300, 1.0 - (xgrid / w) ** 2))
plain *= (np.abs(xgrid) < w)
plain /= np.linalg.norm(plain) * np.sqrt(dx)

print("dx =", dx, " mass =", dx * plain @ plain)
M = build_M(xgrid, w)
print("M diag[:3] =", M.diagonal()[:3], "  M[0,1] =", M[0, 1])
print("trace/Mass-form on plain:", float(plain @ M @ plain))

# manual form reconstruction, piece by piece
ksup = int(round(2.0 * w / dx))
k40 = int(round(40.0 / dx))
ks = np.arange(1, k40 + 1)
wall = dx / (np.exp(ks * dx) - np.exp(-ks * dx))
print("wall.sum() =", wall.sum(), " -> -2*that =", -2 * wall.sum())
print("A*dx =", A_COEF * dx)

F = star_square(plain, dx)
print("F.real max =", np.abs(F.real).max(), " F0 =", F[0].real)
print("F symmetry |F(y)-F(-y)| max:",
      np.abs(F.real - np.roll(F.real[::-1], 0)).max() if False else
      np.abs(F.real[1:50] - F.real[-1:-50:-1]).max())

# circulant sanity: does circulant(c) act as shift+weight?
c = np.zeros(N_PAD)
kp = np.arange(1, ksup + 1)
c[kp] = dx / (np.exp(kp * dx) - np.exp(-kp * dx)) * np.exp(kp * dx / 2.0)
Cc = circulant(c)
chk = float(plain @ (Cc + Cc.T) @ plain)
print("circulant part (plain):", chk)
print("-2I part (plain):", -2.0 * wall.sum() * float(plain @ plain))
print("A part (plain):", A_COEF * dx * float(plain @ plain))
