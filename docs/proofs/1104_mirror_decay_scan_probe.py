"""1104 - mirror-decay decision scan (internal decision-grade P-1 + A1).

Reuses the committed 1100b OrbitGateProbe in-process (law 26).  Emits
the REPRO abort gate, the G1..G4 pre-registered gates and a literal
VERDICT line per docs/proofs/1104_mirror_decay_scan_preregistration.md.
Diagnostic float64; no certified bound; RH not claimed.
"""
import importlib.util
import math
import os
import sys
import time

import numpy as np
from scipy.linalg import eigh

PROOFS = os.path.dirname(os.path.abspath(__file__))

# Audit-log anchors (006-mult-audit-raw.log, 2026-09-03), absolute tol 1e-9.
# cell -> {observable: value}
ANCHORS = {
    (2.0, 8, 4001): dict(top_arch=0.854466, min_prime=-0.858729,
                          top_counter=1.712992),
    (4.0, 8, 4001): dict(top_arch=1.781109, min_prime=-1.781212,
                          top_counter=3.562321),
    (2.0, 16, 32001): dict(top_arch=0.891587, min_prime=-0.904387,
                            top_counter=1.788509),
    (4.0, 24, 32001): dict(top_arch=1.869473, min_prime=-1.886632,
                            top_counter=3.750691),
}

RAY = [(a, 8, 4001) for a in (0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0, 5.0, 6.0)]
KSTAB = [(2.0, 16, 32001), (4.0, 24, 32001)]


def load_rig():
    path = os.path.join(PROOFS, "1100b_first_cell_gate_scan_probe.py")
    spec = importlib.util.spec_from_file_location("probe1100b", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["probe1100b"] = mod
    spec.loader.exec_module(mod)
    return mod


def cell(mod, a, K, grid):
    t0 = time.time()
    probe = mod.OrbitGateProbe(radius=a, basis_size=K, grid_size=grid,
                               envelope_power=1, basis_family="legendre",
                               include_primes=True, include_first_cell=True)
    funcs, _sv, probe.coefficients, _cg, _o = probe._orthonormal_null_functions()
    arch_m = probe.arch_matrix(funcs)
    prime_m = probe.prime_matrix(funcs)
    ev = lambda m: eigh((m + m.T) / 2.0, np.eye(m.shape[0]), eigvals_only=True)
    ea, ep = ev(arch_m), ev(prime_m)
    out = dict(a=a, K=K, grid=grid, nullity=len(ea),
               n_visible=len(probe.prime_terms),
               top_total=float(ev(arch_m + prime_m)[-1]),
               top_arch=float(ea[-1]),
               min_prime=float(ep[0]),
               top_prime=float(ep[-1]),
               top_counter=float(ev(arch_m - prime_m)[-1]),
               secs=time.time() - t0)
    out["B"] = -out["min_prime"]
    out["eps"] = out["B"] / out["top_arch"] - 1.0 if out["top_arch"] > 0 else float("nan")
    return out


def main():
    print("1104 mirror-decay decision scan (pre-reg: 1104_mirror_decay_scan_preregistration.md)")
    print(f"python={sys.version.split()[0]} numpy={np.__version__}")
    mod = load_rig()

    results = []
    for a, K, grid in RAY + KSTAB:
        r = cell(mod, a, K, grid)
        results.append(r)
        print(f"cell a={a:<4g} K={K:<2d} grid={grid:<5d} null={r['nullity']:<2d} "
              f"n_vis={r['n_visible']:<5d} total={r['top_total']:+.2e} "
              f"arch={r['top_arch']:+.6f} B={r['B']:+.6f} eps={r['eps']:+.3e} "
              f"prime_top={r['top_prime']:+.6f} counter={r['top_counter']:+.6f} "
              f"({r['secs']:.1f}s)", flush=True)

    # ---- REPRO abort gate (law 26/30/37) ----------------------------------
    worst = 0.0
    for r in results:
        key = (r["a"], r["K"], r["grid"])
        if key not in ANCHORS:
            continue
        for obs, ref in ANCHORS[key].items():
            got = r["top_arch" if obs == "top_arch" else
                      "min_prime" if obs == "min_prime" else "top_counter"]
            worst = max(worst, abs(got - ref))
    print(f"\nREPRO gate: worst |now - audit| = {worst:.3e} (tol 1e-9; abort >= 1e-6)")
    if worst >= 1e-6:
        print("VERDICT: ABORT-REPRO (no verdict issued; diagnose drift)")
        return

    by_a = {r["a"]: r for r in results if r["grid"] == 4001}
    ray_eps = [(a, by_a[a]["eps"]) for a in (2.0, 3.0, 4.0, 5.0, 6.0)]

    # ---- G1 zero-pinning persistence (a >= 1.5) ---------------------------
    g1_cells = [(r["a"], r["top_total"]) for r in results if r["a"] >= 1.5]
    g1 = all(abs(v) <= 1e-3 for _, v in g1_cells)
    print(f"G1 zero-pinning (a>=1.5, tol 1e-3): {'PASS' if g1 else 'FAIL'}  "
          f"max |top_total| = {max(abs(v) for _, v in g1_cells):.2e}")

    # ---- G2 mirror decay ---------------------------------------------------
    mono = all(e2 < e1 for (_, e1), (_, e2) in zip(ray_eps, ray_eps[1:]))
    eps6 = by_a[6.0]["eps"]
    band = 1e-7 <= eps6 <= 1e-4
    g2 = mono and band
    print(f"G2 mirror decay: eps ray = " +
          ", ".join(f"eps({a:g})={e:+.2e}" for a, e in ray_eps))
    print(f"   monotone={mono}  eps(6)={eps6:+.3e} in [1e-7,1e-4]={band}  "
          f"=> {'PASS' if g2 else 'FAIL'}")

    # ---- G3 saturation ------------------------------------------------------
    arch6 = by_a[6.0]["top_arch"]
    mono_arch = all(by_a[b]["top_arch"] > by_a[a]["top_arch"]
                    for a, b in zip(sorted(by_a), sorted(by_a)[1:]))
    if arch6 >= 5.0:
        g3 = "FAST-SATURATION (A1 falsified)"
    elif mono_arch:
        g3 = "SLOW-CONVERGENCE-SURVIVES (A1 standing)"
    else:
        g3 = "NON-MONOTONE (investigate)"
    plateau = mono_arch and arch6 < 5.372183 * 0.95
    print(f"G3 saturation: top_arch ray = " +
          ", ".join(f"a={a:g}:{by_a[a]['top_arch']:+.4f}" for a in sorted(by_a)))
    print(f"   top_arch(6)={arch6:+.6f} monotone={mono_arch} => {g3}"
          + ("  [plateau-below-peak candidate finding]" if plateau else ""))

    # ---- G4 counterfactual sign ---------------------------------------------
    g4_cells = [(r["a"], r["top_counter"]) for r in results if r["grid"] == 4001]
    g4 = all(v > 0.3 for _, v in g4_cells)
    print(f"G4 counterfactual sign (> +0.3 everywhere): {'PASS' if g4 else 'FAIL'}  "
          f"min = {min(v for _, v in g4_cells):+.6f} at a="
          f"{min(g4_cells, key=lambda p: p[1])[0]:g}")

    verdict = ("PASS" if (g1 and g2 and g4) else "FAIL") + f"  G1={g1} G2={g2} G4={g4}  G3={g3}"
    print(f"\nVERDICT: {verdict}")
    print("DONE")


if __name__ == "__main__":
    main()
