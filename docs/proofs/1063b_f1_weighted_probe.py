# 1063b - does the detector weighting D rescue F1?
#
# 1063 evidence so far: the RAW angle sum Sum cos^2(theta_n) of the pair
# (E, Q_S) grows with the frequency window xi_max (dt-converged!) for every
# nonempty family, while the source case S={} plateaus (proven-trace-class
# anchor). If that persists at xi_max -> infinity, K_S is NOT trace class and
# the raw F1 statement (C1ProlateResponseTraceLegalityUnitScale.lean:117-121)
# is FALSE as written.
#
# But the Dev leaf never consumes K_S raw: every consumer routes through
# `detectorOperator owner oL ...` (leaf lines 262-300 and capstone 404-420),
# and detectorOperator = (conv h)^d (conv h) for a Schwartz h
# (GlobalConvolutionCrossing.lean:22-25), i.e. MULTIPLICATION BY |hat h|^2
# in the Fourier variable. This probe measures the weighted trace
#
#   Tr(D K_S) = Sum_{nonmeet n} <v_n, D v_n> cos^2(theta_n),
#
# for Gaussian weights w(xi) = exp(-(k xi)^2 / 2), k in {0.3, 1, 3} (the
# three decay scales standing for "gentle / medium / fast" Schwartz falloff).
#
# Decision rule (H-numbers shared with 1063):
#   W1: weighted sums SATURATE in xi_max  -> the repair F1' (D-weighted
#       remainder trace-class) is numerically true; raw F1 was the wrong
#       statement to chase and the leaf's consumer already fits F1'.
#   W2: weighted sums grow like the raw sums -> no Schwartz weighting can
#       absorb the pathology (it is not high-frequency-localized); the
#       semilocal Station-5 brick is DEAD, not repairable.
#
# Gates: positivity (lambda_min > -1e-6), weights in [0,1], and the raw
# nonmeet sum must REPRODUCE the 1063 table (same code path -> same numbers).
#
# Deterministic. Run after 1063_f1_target_angle_probe.py has been copied to
# the same directory; P1063 env overrides its path.

import importlib.util
import os

import numpy as np

_spec = importlib.util.spec_from_file_location(
    "p1063", os.environ.get("P1063", "1063_f1_target_angle_probe.py"))
assert _spec is not None and _spec.loader is not None, "run next to the 1063 probe file"
p = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p)


def weighted_traces(N, S, E_diag, F, xi):
    phase = p.transport_phase(xi, S)
    HT = p.build_HT(phase, F, N)
    ED = np.diag(E_diag)
    M = ED @ HT @ ED @ HT @ ED
    Hm = p.hermitian_part(M)
    lam, vec = np.linalg.eigh(Hm)          # ascending
    idx = np.argsort(lam)[::-1]
    vals, vecs = lam[idx], vec[:, idx]
    assert float(vals.min()) > -1e-6, f"positivity fail N={N} S={S}"
    jb, raw = p.nonmeet_sum(vals)          # reproduce 1063 split
    out = [("raw", raw)]
    for k in (0.3, 1.0, 3.0):
        w = np.exp(-0.5 * (k * xi) ** 2)   # multiplier in xi
        assert float(w.max()) <= 1.0 + 1e-15 and float(w.min()) >= 0.0
        Dm = F.conj().T @ (w[:, None] * F)
        d = np.einsum("ij,ij->j", vecs.conj(), Dm @ vecs).real
        assert d.min() > -1e-8 and d.max() < 1 + 1e-8, "weighting not contractive"
        tr = float(np.sum(d[jb:] * vals[jb:]))
        out.append((f"k={k}", tr))
    return jb, out


def run():
    print("=== 1063b F1 detector-weighted probe ===")
    import json
    grid_list = json.loads(os.environ.get(
        "GRIDS_1063B", "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))
    for (N, T) in grid_list:
        t, dt, xi, _ = p.grids(N, T)
        F = p.dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- grid N={N} T={T} (dt={dt:.4f}, xi_max={abs(xi).max():.1f}) ---")
        for S in [[], [2], [2, 3], [2, 3, 5]]:
            jb, rows = weighted_traces(N, S, E_diag, F, xi)
            name = "S=" + ",".join(str(x) for x in S)
            line = "  ".join(f"{lab}:{v:.4f}" for lab, v in rows)
            print(f"WEIGHT|N{N}|{name}|meet={jb}|{line}")


if __name__ == "__main__":
    run()
