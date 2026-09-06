"""1212 aliasing diagnostic: is the operator-side grid resolving the
pinned detector?

The detector correction carries the 1116 node oscillations e^{-i gamma t}
with gamma up to gamma_9 ~ 1687 (period 2 pi / gamma ~ 3.7e-3).  Nyquist
on the operator grid needs dt <= pi/gamma ~ 1.86e-3.  The registered
ladder grids have dt ~ 1.05e-2 / 5.3e-3 -- both alias.  This diagnostic
quantifies the alias by comparing the discrete detector mass f0d*dt
against the qw-side (resolved, DQ = 1.7e-3) reference f0, at both ladder
grades and at a resolving grade.
"""
import importlib.util as ilu

import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = ilu.spec_from_file_location(
    "probe", os.path.join(HERE, "1212_projection_trace_probe.py"))
P = ilu.module_from_spec(spec)
spec.loader.exec_module(P)

g0, meta = P.build_g_delta0()
sample = P.sample_fn(g0)
f0_ref = P.qw_terms(g0)["f0"]

print(f"resolved qw-side f0 = {f0_ref:.6e}  (QS grid DQ = {P.DQ:.6f})")
gammas = P.load_gammas()
print(f"highest node frequency gamma_9 = {gammas[-1]:.2f}, "
      f"Nyquist dt <= pi/gamma = {np.pi / gammas[-1]:.6f}")
print()
print(f"{'grid':>22} {'dt':>10} {'f0d*dt (alias est.)':>20} "
      f"{'ratio vs f0':>12}")
for N in (8192, 16384, 65536, 131072):
    Rn = P.R0 + 8 + 1
    grid = P.Grid(Rn + P.PAD, N)
    gt = sample(grid.t)
    f0d = float((np.abs(gt) ** 2).sum())
    est = f0d * grid.dt
    print(f"N={N:6d} box={2*grid.t[-1]:6.1f}      {grid.dt:10.6f} "
          f"{est:20.6e} {est / f0_ref:12.2f}")

# spectral content of the sampled detector on a ladder grid vs the QS grid
grid = P.Grid(P.R0 + 8 + 1 + P.PAD, 16384)
gt = sample(grid.t)
Gf = np.fft.fftshift(np.abs(np.fft.fft(gt)) ** 2)
fx = np.fft.fftshift(np.fft.fftfreq(len(gt), d=grid.dt))
resolvable = np.abs(fx) <= 1 / (2 * P.DQ)
tot = Gf.sum()
print()
print(f"sampled-detector spectral mass within the QS-resolvable band "
      f"|f| <= {1/(2*P.DQ):.1f}: {Gf[resolvable].sum() / tot:.4f}")
print(f"beyond (aliased content):        {Gf[~resolvable].sum() / tot:.4f}")
