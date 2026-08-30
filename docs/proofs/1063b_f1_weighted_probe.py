# 1063b - finite-grid detector-weighting diagnostic for F1'
#
# The raw finite-grid nonmeet statistic grows with the frequency window for
# every tested nonempty family, while the source anchor stays bounded.  That
# rejects the historical raw-F1 theorem as the next proof target, but does NOT
# prove a continuum negation or identify the statistic with Lean's named-basis
# `IsTraceClassAlong` predicate.
#
# This script computes a finite-dimensional weighted spectral statistic for
# the detector-shaped multiplier.  It is not a trace-class proof.  In Lean,
# D = C† C and K_S = A† A, so D K_S is generally non-self-adjoint and a legal
# readback from any symmetric positive sandwich requires a separate theorem.
#
# The finite statistic is
#
#   Sum_{nonmeet n} <v_n, D v_n> lambda_n,
#
# for Gaussian multipliers w(xi) = exp(-(k xi)^2 / 2), k in {0.3, 1, 3}.
#
# Decision rule (H-numbers shared with 1063):
#   W1: apparent saturation -> investigate the honest symmetric factor
#       B = A C† and seek a continuum Hilbert--Schmidt proof.
#   W2: growth like the raw statistic -> smoothing is not supported by this
#       model, so do not schedule a proof brick without another mechanism.
# Neither outcome proves or disproves F1' or the semilocal route.
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


def weighted_statistics(N, S, E_diag, F, xi):
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
            jb, rows = weighted_statistics(N, S, E_diag, F, xi)
            name = "S=" + ",".join(str(x) for x in S)
            line = "  ".join(f"{lab}:{v:.4f}" for lab, v in rows)
            print(f"WEIGHTED_STAT|N{N}|{name}|meet={jb}|{line}")


if __name__ == "__main__":
    run()
