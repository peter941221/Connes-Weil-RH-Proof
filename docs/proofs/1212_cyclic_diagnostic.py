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
w = grid.pos
Nw = int(w.sum())
f0d = float((np.abs(gt) ** 2).sum())

eye = np.eye(N, dtype=complex)
A = np.empty_like(eye)
for j in range(N):
    A[:, j] = cn._conv(eye[:, j:j + 1], cn.Kf)[:, 0]
Ah = A.conj().T

W1 = Ah @ (np.diag(w.astype(float)) @ A)     # A^H M_w A
T_direct = float(np.trace(W1).real)          # implemented tr(W)
T_cyc = float((w * (A @ Ah).diagonal()).sum().real)  # tr(M_w A A^H)
T3 = Nw * f0d
print(f"T_direct  {T_direct:.6e}")
print(f"T_cyclic  {T_cyc:.6e}  (diff {T_direct - T_cyc:+.3e})")
print(f"T3 Nw*f0d {T3:.6e}  (T_direct-T3 {T_direct-T3:+.3e}, "
      f"rel {(T_direct-T3)/T3:+.3e})")

rownorm2 = (np.abs(A) ** 2).sum(axis=1)      # (A A^H)_ii
dev = 1.0 - rownorm2 / f0d
print(f"row-norm deviation from f0d: max {np.abs(dev).max():.2e} "
      f"at t = {grid.t[np.argmax(np.abs(dev))]:+.2f}; "
      f"dev(|t|<=15) max {np.abs(dev[np.abs(grid.t) <= 15]).max():.2e}")
# shift invariance of entries on the interior block
inner = slice(N // 4, 3 * N // 4)
si = float(np.abs(A[inner, inner] - A[inner.start + 1:inner.stop + 1,
                                      inner.start + 1:inner.stop + 1]).max())
print(f"shift-invariance max err (interior block) {si:.2e} "
      f"(vs max|A| {np.abs(A).max():.2e})")
