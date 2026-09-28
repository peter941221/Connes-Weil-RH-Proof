#!/usr/bin/env python3
"""Record 2142: high-precision pin audit of the 2141 candidate coefficients."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_density_1959 as density  # noqa: E402
import fourpoint_cert_d_1985 as cert  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402

OUTPUT = ROOT / "results" / "2142_routea_h1_fibre_mp_pin_audit.json"
RHO = complex(0.945, 39.25244858548658)
K = 30.0
FACTORS = [0.50, 0.70, 0.90, 1.10, 1.30]
TRIAL = 162
SCALE_BASE = -2.7660862136111555
SCALE_CORR = -7.593725512173001
SEED = 2141


def constrained_h1(matrix, gram, values):
    eigenvalues, eigenvectors = np.linalg.eigh((gram + gram.conj().T) / 2.0)
    floor = max(float(eigenvalues.max()) * 1e-12, 1e-24)
    inverse = (eigenvectors / np.maximum(eigenvalues, floor)) @ eigenvectors.conj().T
    return inverse @ matrix.conj().T @ np.linalg.solve(matrix @ inverse @ matrix.conj().T, values)


def build_candidate():
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
    base = base0 + SCALE_BASE * directions[TRIAL % 24]
    corr = corr0 + SCALE_CORR * directions[(7 * TRIAL + 3) % 24]
    return targets, target_values, fam, base, corr


def mp_family_values(fam, s, m):
    out = []
    for a, theta in fam:
        aa = mp.mpf(str(a)); tt = mp.mpf(str(theta)); ss = mp.mpc(s)
        X, W = cert.phi_weights_mp(aa, 6, m)
        total = mp.mpc(0)
        for x, w in zip(X, W):
            u = x / aa
            if abs(u) < 1:
                total += aa * w * mp.exp(-K / (1 - u * u) + aa * (ss + 1j * tt) * x)
        out.append(total)
    return out


def main():
    targets, target_values, fam, base, corr = build_candidate()
    mp.mp.dps = 80
    readings = []
    for m in (160, 320):
        base_errors = []
        corr_errors = []
        for z, expected in zip(targets, target_values):
            values = mp_family_values(fam, mp.mpc(float(z.real), float(z.imag)), m)
            base_mp = sum(mp.mpc(complex(base[j])) * values[j] for j in range(len(fam)))
            corr_mp = sum(mp.mpc(complex(corr[j])) * values[j] for j in range(len(fam)))
            base_errors.append(float(abs(base_mp - 1)))
            corr_errors.append(float(abs(corr_mp - mp.mpc(complex(expected)))))
        readings.append({"quadrature_points_per_panel": m, "max_base_pin_error": max(base_errors), "max_corr_pin_error": max(corr_errors), "base_pin_errors": base_errors, "corr_pin_errors": corr_errors})
    result = {"record": 2142, "status": "HIGH-PRECISION-PIN-AUDIT", "candidate": {"trial": TRIAL, "scale_base": SCALE_BASE, "scale_corr": SCALE_CORR}, "family_count": len(fam), "readings": readings, "nonclaims": ["coefficients are still double-precision null-fibre coefficients", "this does not certify the Gram solve or the signed integral", "no producer theorem or RH claim"], "provenance": {"script": os.fspath(Path(__file__).relative_to(ROOT)), "source": "results/2141_routea_overcomplete_h1_fibre_verify.json"}}
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()

