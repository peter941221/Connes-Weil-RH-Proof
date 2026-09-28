#!/usr/bin/env python3
"""Record 2143: high-precision pin correction and full gate replay."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_density_1959 as density  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_cert_d_1985 as cert  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402

OUTPUT = ROOT / "results" / "2143_routea_mp_pinned_gate.json"
RHO = complex(0.945, 39.25244858548658)
K = 30.0
N = 0
FACTORS = [0.50, 0.70, 0.90, 1.10, 1.30]
SEED = 2141
TRIAL = 162
SCALE_BASE = -2.7660862136111555
SCALE_CORR = -7.593725512173001
MP_M = 320


def constrained_h1(matrix, gram, values):
    eigenvalues, eigenvectors = np.linalg.eigh((gram + gram.conj().T) / 2.0)
    floor = max(float(eigenvalues.max()) * 1e-12, 1e-24)
    inverse = (eigenvectors / np.maximum(eigenvalues, floor)) @ eigenvectors.conj().T
    return inverse @ matrix.conj().T @ np.linalg.solve(matrix @ inverse @ matrix.conj().T, values)


def candidate():
    targets = density.target_nodes(RHO)
    target_values = np.asarray([density.target_value(RHO, z) for z in targets], dtype=complex)
    base_family = density.design_family(RHO, 1.0)
    fam = [(factor * a, theta) for factor in FACTORS for a, theta in base_family]
    xw = [density.phi_weights(a, panels=6, m=400) for a, _ in fam]
    matrix = density.family_values(fam, K, np.asarray(targets, dtype=complex), xw).T
    gram = health.h1_gram(fam)
    base0 = constrained_h1(matrix, gram, np.ones(len(targets), dtype=complex))
    corr0 = constrained_h1(matrix, gram, target_values)
    _u, singular, vh = np.linalg.svd(matrix)
    rank = int(np.sum(singular > 1e-10 * singular[0]))
    null = vh[rank:].conj().T
    rng = np.random.default_rng(SEED)
    directions = []
    for _ in range(24):
        raw = null @ (rng.normal(size=null.shape[1]) + 1j * rng.normal(size=null.shape[1]))
        norm = math.sqrt(max(float(np.real(raw.conj() @ gram @ raw)), 1e-300))
        directions.append(raw / norm)
    return targets, target_values, fam, xw, base0 + SCALE_BASE * directions[TRIAL % 24], corr0 + SCALE_CORR * directions[(7 * TRIAL + 3) % 24]


def mp_values(fam, s):
    values = []
    for a, theta in fam:
        aa = mp.mpf(str(a)); tt = mp.mpf(str(theta)); ss = mp.mpc(s)
        X, W = cert.phi_weights_mp(aa, 6, MP_M)
        total = mp.mpc(0)
        for x, w in zip(X, W):
            u = x / aa
            if abs(u) < 1:
                total += aa * w * mp.exp(-K / (1 - u * u) + aa * (ss + 1j * tt) * x)
        values.append(total)
    return values


def gate(fam, xw, base, corr, points):
    xi = np.linspace(-40.0, 40.0, points)
    targets = density.target_nodes(RHO)
    weight, _lb, _lc, ratio = completion.owner_density(targets, fam, K, N, xi, xw, (base, corr))
    polynomial = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(RHO)))
    ge = density.gate_entries(xi, weight, polynomial, max(a for a, _ in fam) * 2.0)
    spread = density.route_spread(ge)
    det = ge["C"] * ge["D"] - ge["B01"] ** 2
    return {"xi_points": points, "C": float(ge["C"]), "B01": float(ge["B01"]), "D": float(ge["D"]), "det": float(det), "healthy": bool(ge["C"] > 0 and ge["D"] < 0 and det < 0), "route_key": ge["route_key"], "routes": sorted(ge["prime"].keys()), "route_spread": [float(v) for v in spread], "max_cancellation_ratio": float(np.nanmax(ratio)), "n_primes": int(ge["n_primes"])}


def main():
    mp.mp.dps = 80
    targets, target_values, fam, xw, base, corr = candidate()
    high_matrix = np.asarray([[complex(v.real, v.imag) for v in mp_values(fam, mp.mpc(float(z.real), float(z.imag)))] for z in targets], dtype=complex)
    singular = np.linalg.svd(high_matrix, compute_uv=False)
    rows = []
    for label, coeff, expected in (("base", base, np.ones(len(targets), dtype=complex)), ("corr", corr, target_values)):
        before = high_matrix @ coeff
        residual = expected - before
        correction = np.linalg.lstsq(high_matrix, residual, rcond=None)[0]
        repaired = coeff + correction
        after = high_matrix @ repaired
        rows.append({"label": label, "before_max_residual": float(np.max(np.abs(before - expected))), "correction_l2": float(np.linalg.norm(correction)), "correction_max": float(np.max(np.abs(correction))), "after_max_residual": float(np.max(np.abs(after - expected)))})
        if label == "base":
            repaired_base = repaired
        else:
            repaired_corr = repaired
    result = {"record": 2143, "status": "MP-PIN-CORRECTED-GATE-REPLAY", "candidate": {"trial": TRIAL, "scale_base": SCALE_BASE, "scale_corr": SCALE_CORR}, "mp_quadrature_points_per_panel": MP_M, "high_matrix_singular_values": [float(v) for v in singular], "pin_correction": rows, "gate_before": [gate(fam, xw, base, corr, p) for p in (4001, 10001, 20001)], "gate_after": [gate(fam, xw, repaired_base, repaired_corr, p) for p in (4001, 10001, 20001)], "nonclaims": ["high matrix is quadrature-based, not interval enclosed", "the owner is still a finite known-zero screen", "no producer theorem or RH claim"], "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)), "source": "results/2141_routea_overcomplete_h1_fibre_verify.json"}}
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
