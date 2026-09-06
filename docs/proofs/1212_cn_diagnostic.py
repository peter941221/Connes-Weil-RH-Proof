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

# dense A via _conv on unit vectors (forward), and A^dagger via adj conv
eye = np.eye(N, dtype=complex)
A = np.empty_like(eye)
Ad = np.empty_like(eye)
for j in range(N):
    e = eye[:, j:j + 1]
    A[:, j] = cn._conv(e, cn.Kf)[:, 0]
    Ad[:, j] = cn._conv(e, cn.Kaf)[:, 0]
adj_err = float(np.abs(Ad - A.conj().T).max()
                / max(float(np.abs(A).max()), 1e-300))
print(f"adjoint rel err {adj_err:.2e}")

w = grid.pos
Nw = int(w.sum())
f0d = float((np.abs(gt) ** 2).sum())
colnorm = np.sqrt((np.abs(A) ** 2).sum(axis=0))          # ||A e_i||
colnorm_w = np.sqrt((np.abs(A[w, :]) ** 2).sum(axis=0))  # ||1_w A e_i||
print(f"||Ae_i|| all-i: min {colnorm.min():.6f} max {colnorm.max():.6f} "
      f"sqrt(f0d) {np.sqrt(f0d):.6f}")
print(f"||1_w A e_i|| for i in w: min {colnorm_w[w].min():.6f} "
      f"max {colnorm_w[w].max():.6f}  (expect sqrt(f0d) if closed form)")
tr_dense = float((colnorm_w[w] ** 2).sum())
print(f"tr dense {tr_dense:.6e}  Nw*f0d {Nw*f0d:.6e}  "
      f"rel {abs(tr_dense-Nw*f0d)/(Nw*f0d):.2e}")
# deficit profile vs position in window
idx = np.nonzero(w)[0]
prof = (colnorm_w[w] ** 2) - f0d
print(f"deficit at window center {prof[len(prof)//2]:.3e}; "
      f"at edges {prof[0]:.3e}/{prof[-1]:.3e}")
print(f"gt support: last |gt|>1e-12*max at |t| = "
      f"{float(np.abs(grid.t)[np.abs(gt) > 1e-12*np.abs(gt).max()].max()):.2f}"
      f" (Rn = {Rn}, dt = {grid.dt:.3f})")
