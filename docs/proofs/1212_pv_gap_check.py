import importlib.util as ilu

import numpy as np

import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = ilu.spec_from_file_location(
    "probe", os.path.join(HERE, "1212_projection_trace_probe.py"))
P = ilu.module_from_spec(spec)
spec.loader.exec_module(P)

grid = P.Grid(P.R0 + P.PAD, 2048)
neg = grid.neg
idx = np.nonzero(neg)[0]
m = len(idx)
Gm = np.empty((m, m), dtype=complex)
for j0 in range(0, m, 128):
    cols = idx[j0:j0 + 128]
    E = np.zeros((grid.N, len(cols)), dtype=complex)
    E[cols, np.arange(len(cols))] = 1.0
    V = grid.pos[:, None] * grid.apply_ts(E, adjoint=True)
    Gm[:, j0:j0 + 128] = (grid.apply_ts(V) * neg[:, None])[neg, :]
Gm = (Gm + Gm.conj().T) / 2
ev = np.sort(np.linalg.eigvalsh(Gm).real)[::-1]
scale = ev.max()
print(f"m={m} scale={scale:.3e}")
km = int((ev > 1e-8 * scale).sum())
print(f"count > 1e-8*scale: {km}")
for r in list(range(800, 826, 5)) + [km - 1, km]:
    print(f"  ev[{r}] = {ev[r]:+.6e}  (log10 rel {np.log10(abs(ev[r])/scale):+.2f})")
print(f"smallest 5 kept: {ev[km-5:km]/scale}")
print(f"largest 5 dropped: {ev[km:km+5]/scale}")
print(f"gap ratio = {ev[km-1]/max(abs(ev[km]), 1e-300):.3e}")
