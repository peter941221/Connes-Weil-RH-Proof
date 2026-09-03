"""1105 addendum B - P-7 K-fracture re-run (their pre-registered experiment 3,
criterion eps(K=24) > 1 at a=2). Committed 1100b rig, grid 4001, legendre.
Diagnostic float64; RH not claimed."""
import importlib.util
import math
import os
import sys

import numpy as np
from scipy.linalg import eigh

PROOFS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load_rig():
    path = os.path.join(PROOFS, "1100b_first_cell_gate_scan_probe.py")
    spec = importlib.util.spec_from_file_location("probe1100b", path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules["probe1100b"] = mod
    spec.loader.exec_module(mod)
    return mod


def cell(mod, a, K, grid=4001):
    probe = mod.OrbitGateProbe(radius=a, basis_size=K, grid_size=grid,
                               envelope_power=1, basis_family="legendre",
                               include_primes=True, include_first_cell=True)
    funcs, _sv, probe.coefficients, _cg, _o = probe._orthonormal_null_functions()
    arch_m = probe.arch_matrix(funcs)
    prime_m = probe.prime_matrix(funcs)
    ev = lambda m: eigh((m + m.T) / 2.0, np.eye(m.shape[0]), eigvals_only=True)
    ea, ep = ev(arch_m), ev(prime_m)
    top_a, min_p = float(ea[-1]), float(ep[0])
    band = (K - 1) * math.pi / (4.0 * a)
    return dict(K=K, d=len(ea), top_a=top_a, min_p=min_p,
                eps=(-min_p) / top_a - 1.0, band=band)


def main():
    print("1105 addendum B - P-7 K-fracture re-run (a=2, grid 4001)")
    print("their pre-registered criterion: eps(K=24) > 1")
    print("their reported: K=8 +4.99e-3 | K=16 +1.44e-2 | K=24 +2.05 | "
          "K=32 +2.37 | K=48 +2.62")
    mod = load_rig()
    verdicts = []
    for K in (8, 16, 24, 32, 48):
        r = cell(mod, 2.0, K)
        print(f"K={K:<3d} d={r['d']:<3d} topA={r['top_a']:+.6f} "
              f"minP={r['min_p']:+.6f} eps={r['eps']:+.4e} band={r['band']:.2f}")
        if K == 24:
            verdicts.append(r["eps"] > 1.0)
    ok = all(verdicts)
    print(f"\nVERDICT: {'PASS' if ok else 'FAIL'}  "
          f"(eps(K=24) > 1: {verdicts[0] if verdicts else 'missing'})")
    print("DONE")


if __name__ == "__main__":
    main()
