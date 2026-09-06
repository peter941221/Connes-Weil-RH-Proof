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
win = np.abs(grid.t) <= Rn
cn = P.Cn(grid, gt, win)
pf = P.PfEngine(grid)

# 1) ran(P_f) subset ker((I-P_r) T_S)?
rng = np.random.default_rng(7)
V = rng.standard_normal((N, 6)) + 1j * rng.standard_normal((N, 6))
PV = pf.apply(V)
res = grid.apply_ts(PV) * grid.neg[:, None]
print(f"||(I-P_r)T_S P_f v|| / ||v|| = "
      f"{float(np.linalg.norm(res)/np.linalg.norm(PV)):.2e}")

# 2) dense von Neumann trace sequence (relative steps)
f0d = float((np.abs(gt) ** 2).sum())
Nw = int(win.sum())
bulk = Nw * f0d
eye = np.eye(N, dtype=complex)
Wd = np.empty_like(eye)
for j in range(N):
    Wd[:, j] = cn.Wmv(eye[:, j:j + 1])[:, 0]
U = Wd * grid.pos[:, None]
tr0 = float(np.einsum('ij,ji->', U, Wd).real)
print(f"bulk {bulk:.6e}; tr(P_r W) = {tr0:.6e} (ratio {tr0/bulk:.4f})")
hist = [tr0]
for k in range(1, 241):
    U = pf.apply(U)
    U *= grid.pos[:, None]
    tr = float(np.einsum('ij,ji->', U, Wd).real)
    hist.append(tr)
    if k in (1, 2, 5, 10, 20, 40, 60, 80, 120, 160, 240):
        d = abs(tr - hist[-2]) / max(abs(tr), 1e-300)
        print(f"iter {k:3d}: tr {tr:+.6e}  step {d:.2e}  "
              f"tr/bulk {tr/bulk:+.6f}")

# 3) estimate rate from the last 80 iterates (geometric fit)
arr = np.array(hist[160:])
if np.all(arr > 0):
    steps = np.diff(np.log(arr))
    print(f"log-step mean {steps.mean():+.3e} (last 80) -> "
          f"iters for 1e-11 from iter 240: "
          f"{int(np.log(1e-11)/steps.mean()) if steps.mean() < 0 else 'inf'}")
