import importlib.util as ilu

import numpy as np

import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = ilu.spec_from_file_location(
    "probe", os.path.join(HERE, "1212_projection_trace_probe.py"))
P = ilu.module_from_spec(spec)
spec.loader.exec_module(P)

g0, meta = P.build_g_delta0()
sample = P.sample_fn(g0)

N = 512
Rn = P.R0 + 8 + 1
grid = P.Grid(Rn + P.PAD, N)
gt = sample(grid.t)
cn = P.Cn(grid, gt)

eye = np.eye(N, dtype=complex)
A = np.empty_like(eye)
for j in range(N):
    A[:, j] = cn._conv(eye[:, j:j + 1], cn.Kf)[:, 0]

# ideal zero-extension Toeplitz entries
ideal = np.empty_like(A)
for i in range(N):
    ideal[:, i] = np.roll(gt, i)   # A[j, i] = gt[(j - i) mod N]

err = np.abs(A - ideal)
amax = float(np.abs(A).max())
print(f"max|A| {amax:.3e}; max|A-ideal| {err.max():.3e} "
      f"(rel {err.max()/amax:.2e})")
# where do they differ?  restrict to entries with |ideal| above noise
big = np.abs(ideal) > 1e-6 * amax
print(f"entries with |ideal|>1e-6max: {int(big.sum())}; "
      f"max err there {err[big].max() if big.any() else 0:.3e}")
# row/column profile of the difference
rowerr = err.max(axis=1)
colerr = err.max(axis=0)
bad_rows = np.nonzero(rowerr > 1e-6 * amax)[0]
print(f"bad rows: {len(bad_rows)}; t-range "
      f"{grid.t[bad_rows.min()] if len(bad_rows) else 0:+.2f} .. "
      f"{grid.t[bad_rows.max()] if len(bad_rows) else 0:+.2f}")
# check a single interior entry explicitly
i0 = N // 2 + 10
j0 = N // 2 - 7
print(f"A[{j0},{i0}] {A[j0, i0]:.6e}  gt(t_j0-t_i0) "
      f"{np.interp(grid.t[j0]-grid.t[i0], grid.t, gt.real):.6e} "
      f"+1j*{np.interp(grid.t[j0]-grid.t[i0], grid.t, gt.imag):.6e}")
