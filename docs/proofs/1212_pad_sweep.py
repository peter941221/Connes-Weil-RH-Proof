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
qwv = P.qw_terms(g0)
f0c = qwv["f0"]

print("pad sweep at n=8, N=2048 (Rn = 19.05):")
print(f"{'pad':>5} {'T':>8} {'bulk':>12} {'term1':>12} "
      f"{'term_pv':>12} {'Tn':>12} {'sn':>12} {'sn/bulk':>10} {'pv_rank':>8}")
for pad in (8, 12, 16, 24, 32, 40, 56, 72, 96):
    r = P.rung(8, 2048, sample, f0c, pad=pad)
    print(f"{pad:5.0f} {2*r['Rn']+2*pad:8.1f} {r['bulk']:12.4e} "
          f"{r['term1']:12.4e} {r['term_pv']:12.4e} {r['Tn']:12.4e} "
          f"{r['sn']:12.4e} {r['sn']/r['bulk']:10.3e} "
          f"{r['pv_rank']:5d}/{r['pv_neg_dim']}")
