"""1225 Stage-A rank diagnostic (MODEL, not an official readout).

Question: smoke-3 S0.5 fails at the committed DENSE_N=2048 / RANK=320 with
`Tn dense-vs-spectral 4.7e-01`.  Is that (a) eigsh mis-convergence on the
clustered PSD spectrum, or (b) genuine spectral-tail mass beyond rank 320
for the narrow-band control bump?  Method: form the dense W at the SAME
n=8 grid, take the FULL exact spectrum with eigvalsh, print the true
capture fraction as a function of rank, and compare eigsh's top-320 to the
true top-320.  Prints only; asserts nothing; certifies nothing.
"""
import importlib.util
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "probe", os.path.join(HERE, "1225_positive_control_probe.py"))
assert spec is not None and spec.loader is not None
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

g, meta = m.build_g_control(m.CONTROL_EPS)
print(f"control: residual {meta['residual']:.2e} |a|max {meta['max_abs_a']:.2e} "
      f"support(1e-8) {meta['support_radius']:.6f}")

n = 8
Rn = m.R0 + n + 1
grid = m.Grid(Rn + m.PAD, m.DENSE_N)
sample = m.sample_fn(g)
gt = sample(grid.t)
win = np.abs(grid.t) <= Rn
cn = m.Cn(grid, gt, win)
N = grid.N
eye = np.eye(N, dtype=complex)
Wd = np.empty_like(eye)
for j in range(N):
    Wd[:, j] = cn.Wmv(eye[:, j:j + 1])[:, 0]
Ws = (Wd + Wd.conj().T) / 2
del Wd
vals = np.sort(np.linalg.eigvalsh(Ws))[::-1]
tot = float(vals.sum())
print(f"N={N}  tr(W) {tot:.6e}  #vals>1e-16*tot: {int((vals > 1e-16*tot).sum())}")
for r in (10, 50, 100, 200, 320, 400, 512, 640, 800, 1024, 1280, 1600, 2048):
    rr = min(r, N) - 1
    print(f"  true capture at rank {r:5d}: {float(vals[:rr + 1].sum()) / tot:.10f}"
          f"   lambda_r {vals[rr]:.3e}")
v_spec, u_spec = m.bulk_eig(cn, 320)
dv = np.abs(v_spec[:320] - vals[:320]).max()
print(f"eigsh top-320 vs true top-320: max |diff| {dv:.3e}  "
      f"(eigsh sum {float(v_spec.sum()):.6e} vs true sum {float(vals[:320].sum()):.6e})")

# contrast: the committed detector twin on the same grid/rank
g_det, _ = m.build_g_delta0()
sdet = m.sample_fn(g_det)
gtd = sdet(grid.t)
cnd = m.Cn(grid, gtd, win)
Wd2 = np.empty((N, N), dtype=complex)
for j in range(N):
    Wd2[:, j] = cnd.Wmv(eye[:, j:j + 1])[:, 0]
vals_d = np.sort(np.linalg.eigvalsh((Wd2 + Wd2.conj().T) / 2))[::-1]
tot_d = float(vals_d.sum())
for r in (10, 100, 320):
    rr = min(r, N) - 1
    print(f"  DETECTOR true capture at rank {r:5d}: "
          f"{float(vals_d[:rr + 1].sum()) / tot_d:.10f}"
          f"   lambda_r {vals_d[rr]:.3e}")
print("diag done (MODEL; certifies nothing; RH NOT claimed)")
