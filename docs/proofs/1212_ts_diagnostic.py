import importlib.util as ilu

import numpy as np

import os

HERE = os.path.dirname(os.path.abspath(__file__))
spec = ilu.spec_from_file_location(
    "probe", os.path.join(HERE, "1212_projection_trace_probe.py"))
P = ilu.module_from_spec(spec)
spec.loader.exec_module(P)

for label, B, N, mk in [
        ("gauss B=34", 34.05, 2048, None),
        ("bump  B=34", 34.05, 2048, "bump"),
        ("bump  B=100", 100.05, 6144, "bump"),
        ("gauss B=100", 100.05, 6144, None),
]:
    g = P.Grid(B, N)
    if mk == "bump":
        u = P.chi(g.t / 20.0).astype(complex)[:, None]
    else:
        u = np.exp(-g.t ** 2 / 4).astype(complex)[:, None]
    nrm = float(np.linalg.norm(u))
    v0 = g.apply_e(u, True)
    edge_r = float(abs(v0[g.t > B - 3.0, 0]).max())
    edge_l = float(abs(v0[g.t < -B + 3.0, 0]).max())
    e_err = float(np.linalg.norm(g.apply_e(v0) - u) / nrm)
    ts2 = g.apply_ts(g.apply_ts(u))
    ts_err = float(np.linalg.norm(ts2 - u) / nrm)
    ht1 = g.ht(u)
    ht_err = float(np.linalg.norm(g.ht(ht1) - u) / nrm)
    # isolate: HT of E^-1 u vs re-application path T_S^2 = E HT E^-1 E HT E^-1
    w = g.ht(v0)
    mid = g.apply_e(w)
    back = g.ht(mid)
    print(f"{label:12s} ht2 {ht_err:.2e}  E.E-1 {e_err:.2e}  "
          f"v0 edge L/R {edge_l:.1e}/{edge_r:.1e}  "
          f"ts2 {ts_err:.2e}  "
          f"[HT.E-1 {float(np.linalg.norm(w)/nrm):.2e} "
          f"E.HT.E-1 {float(np.linalg.norm(mid)/nrm):.2e} "
          f"HT.E.HT.E-1 {float(np.linalg.norm(back)/nrm):.2e}]")
