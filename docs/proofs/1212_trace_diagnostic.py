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

# detector mass profile
supp = 10.05
m_supp = np.abs(grid.t) <= supp
mass_out = float((np.abs(gt[~m_supp]) ** 2).sum())
print(f"f0d {f0d:.6e}; mass |t|>10.05 {mass_out:.6e} "
      f"(fraction {mass_out/f0d:.2e}); "
      f"max|gt| {np.abs(gt).max():.3e}; "
      f"|gt(24)| {np.interp(24.0, grid.t, np.abs(gt)):.3e}; "
      f"|gt(15)| {np.interp(15.0, grid.t, np.abs(gt)):.3e}")

eye = np.eye(N, dtype=complex)
A = np.empty_like(eye)
for j in range(N):
    A[:, j] = cn._conv(eye[:, j:j + 1], cn.Kf)[:, 0]

full = (np.abs(A) ** 2).sum(axis=0)              # ||A e_i||^2, all i
win = (np.abs(A[w, :]) ** 2).sum(axis=0)         # ||1_w A e_i||^2
T1 = float(full[w].sum())                        # cyclic bulk
T2 = float(win.sum())                            # true trace
T3 = Nw * f0d
# overlap formula: N_pair(d) = (1_w * 1_box)[d]
ind = np.ones(N)
pairs = np.convolve(w.astype(float), ind)        # length 2N-1, d = k-(N-1)
d = np.arange(-(N - 1), N)
# |gt[d]| on index space: gt index offset d = j - i in samples
gtd = np.zeros_like(pairs)
gt_idx = np.arange(N)
# gt[d] with d = j - i samples: interpolate gt array at (center+d)
gt_shift = np.roll(gt, 0)
for k, dd in enumerate(d):
    src = gt_idx - dd
    ok = (src >= 0) & (src < N)
    gtd[k] = float((np.abs(gt[src[ok]]) ** 2).sum()) if ok.any() else 0.0
# That's sum_j |gt[j-d... instead compute directly:
T4 = 0.0
for k, dd in enumerate(d):
    ii = np.nonzero(w)[0]
    jj = ii + dd
    ok = (jj >= 0) & (jj < N)
    T4 += float((np.abs(gt[jj[ok]]) ** 2).sum())
print(f"T1 cyclic {T1:.6e}")
print(f"T2 true   {T2:.6e}  (T1-T2 {T1-T2:+.3e})")
print(f"T3 Nw*f0d {T3:.6e}  (T1-T3 {T1-T3:+.3e})")
print(f"T4 overlap {T4:.6e}  (T2-T4 {T2-T4:+.3e})")
rel = abs(T2 - T3) / T3
print(f"|T2-T3|/T3 {rel:.2e}")
