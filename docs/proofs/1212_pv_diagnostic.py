import importlib.util as ilu

import numpy as np

import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = ilu.spec_from_file_location(
    "probe", os.path.join(HERE, "1212_projection_trace_probe.py"))
P = ilu.module_from_spec(spec)
spec.loader.exec_module(P)

grid = P.Grid(P.R0 + P.PAD, 512)
neg = grid.neg
idx = np.nonzero(neg)[0]
m = len(idx)
Gm = np.empty((m, m), dtype=complex)
for j0 in range(0, m, 64):
    cols = idx[j0:j0 + 64]
    E = np.zeros((grid.N, len(cols)), dtype=complex)
    E[cols, np.arange(len(cols))] = 1.0
    V = grid.pos[:, None] * grid.apply_ts(E, adjoint=True)
    Gm[:, j0:j0 + 64] = (grid.apply_ts(V) * neg[:, None])[neg, :]
Gm = (Gm + Gm.conj().T) / 2
dg = np.abs(np.diag(Gm))
scale = float(dg.max())
ev = np.linalg.eigvalsh(Gm).real
ev = np.sort(ev)[::-1]
print(f"scale (max diag) {scale:.3e}")
print("eigenvalues of G_C (CC^*), log10, descending:")
lg = np.log10(np.abs(ev) / scale + 1e-300)
for lo in range(0, m, 16):
    blk = lg[lo:lo + 16]
    print(f"  [{lo:3d}] " + " ".join(f"{v:+.2f}" for v in blk[:8]))
    if lo >= 96:
        break
print(f"count(ev) > 1e-10*scale: {int((ev > 1e-10*scale).sum())} / {m}")
print(f"count(ev) > 1e-8 *scale: {int((ev > 1e-8*scale).sum())} / {m}")
print(f"count(ev) > 1e-6 *scale: {int((ev > 1e-6*scale).sum())} / {m}")
print(f"count(ev) > 1e-4 *scale: {int((ev > 1e-4*scale).sum())} / {m}")
print(f"smallest 8 / largest: {ev[-8:]/scale} / {ev[0]/scale:.3f}")
