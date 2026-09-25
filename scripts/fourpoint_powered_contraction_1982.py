#!/usr/bin/env python3
"""Record 1982: powered-seed high-shell contraction candidate.

This is a conditioning probe, not a GO certificate. It keeps the owner,
base, correction, convolution index, and gate witness from record 1981, then
tests an explicit contraction constant q on a denser strip grid. The tail
ratios are obtained by replacing the formal 1/2 contraction proxy by q in the
same-index formula; the replacement still needs an interval proof before it
can be used by Lean.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as owner_probe  # noqa: E402
import fourpoint_powered_seed_1981 as powered  # noqa: E402


RHO = powered.RHO
N = powered.N
T_MAX = 64.0
DT = 0.01
SIGMA_STEP = 0.025
QUADRATURE_ORDER = 500
Q_CANDIDATES = [2.0 ** -16, 2.0 ** -17, 2.0 ** -18, 2.0 ** -19]
T_CANDIDATES = [18.0, 20.0, 22.0, 24.0, 28.0, 32.0]
RECOMMENDED_T = 28.0
RECOMMENDED_Q = 2.0 ** -14


def main() -> None:
    owner, targets, radius, known = owner_probe.build_owner(RHO, N)
    seed_transform = powered.make_powered_seed(order=QUADRATURE_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])
    base_values = [1.0 + 0j] * len(targets)

    ts = np.arange(-T_MAX, T_MAX + 0.5 * DT, DT)
    sigmas = np.arange(0.0, 1.0 + 0.5 * SIGMA_STEP, SIGMA_STEP)
    profile = np.zeros_like(ts)
    arg_sigma = np.zeros_like(ts)
    for sigma in sigmas:
        values = owner_probe.cardinal_transform(
            targets, base_values, seed0, sigma + 1j * ts, seed_transform)
        abs_values = np.abs(values)
        update = abs_values > profile
        arg_sigma[update] = sigma
        profile = np.maximum(profile, abs_values)

    maxima = {}
    for threshold in T_CANDIDATES:
        mask = np.abs(ts) >= threshold
        index = np.flatnonzero(mask)[np.argmax(profile[mask])]
        maxima[str(threshold)] = {
            "max_abs_base": float(profile[index]),
            "arg_t": float(ts[index]),
            "arg_sigma": float(arg_sigma[index]),
        }

    old = json.loads(
        (ROOT / "results" / "1981_powered_seed_underapprox.json").read_text())
    row = next(item for item in old["rows"] if item["n"] == 4)
    tail_rows = []
    for threshold in T_CANDIDATES:
        qmax = maxima[str(threshold)]["max_abs_base"]
        for q in Q_CANDIDATES:
            ratio = row["tail_proxy_L_over_lambda_sq"] * (q / 0.5) ** (2 * row["n"])
            tail_rows.append({
                "T": threshold,
                "q": q,
                "grid_margin": q - qmax,
                "tail_proxy_L_over_lambda_sq": ratio,
                "tail_proxy_below_one": ratio < 1.0,
            })

    recommended_max = maxima[str(RECOMMENDED_T)]["max_abs_base"]
    recommended_ratio = row["tail_proxy_L_over_lambda_sq"] * (
        RECOMMENDED_Q / 0.5) ** (2 * row["n"])

    report = {
        "record": 1982,
        "status": "CONTRACTION_CANDIDATE_ONLY",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "owner_model": old["owner_model"],
        "radius": radius,
        "known_zero_count": len(known),
        "owner_cardinality": len(owner),
        "target_cardinality": len(targets),
        "min_separation": owner_probe.min_separation(owner),
        "seed": {
            "scale": powered.SEED_SCALE,
            "power": powered.SEED_POWER,
            "quadrature_order": QUADRATURE_ORDER,
        },
        "gate_row_n4": {
            "C": row["C"],
            "b": row["b"],
            "D": row["D"],
            "det": row["det"],
            "lambda": row["lambda"],
            "gate_signs": row["gate_signs"],
        },
        "profile_grid": {
            "T_max": T_MAX,
            "dt": DT,
            "sigma_step": SIGMA_STEP,
            "max_abs_base_global": float(profile.max()),
            "global_arg_t": float(ts[profile.argmax()]),
            "global_arg_sigma": float(arg_sigma[profile.argmax()]),
            "threshold_maxima": maxima,
        },
        "tail_rows": tail_rows,
        "recommended_candidate": {
            "T": RECOMMENDED_T,
            "q": RECOMMENDED_Q,
            "grid_max_abs_base": recommended_max,
            "grid_margin": RECOMMENDED_Q - recommended_max,
            "tail_proxy_L_over_lambda_sq": recommended_ratio,
            "tail_proxy_below_one": recommended_ratio < 1.0,
        },
        "provenance": [
            "scripts/fourpoint_powered_seed_1981.py",
            "scripts/fourpoint_actual_owner_1980.py",
            "results/1981_powered_seed_underapprox.json",
            "known zeros supplied by mpmath.zetazero; under-approximation only",
            "q and tail values are grid/proxy diagnostics, not interval proofs",
        ],
    }
    output = ROOT / "results" / "1982_powered_contraction_candidate.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
