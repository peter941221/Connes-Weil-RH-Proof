#!/usr/bin/env python3
"""Record 2136: reprice the fixed-r48 tail with record-2135 N48."""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402

OUTPUT = ROOT / "results" / "2136_routea_fixed_r48_tail_price.json"
K = 30.0
R = 48
N48_UPPER = float(json.loads(
    (ROOT / "results" / "2135_routea_root_partition_lipschitz.json").read_text(
        encoding="utf-8"
    )
)["variation_upper"])
X0 = 160.0
XMAX = 1.0e6


def main() -> None:
    rho, nodes, values, fam, _xw, gram, _a, _, _ = r37.setup(False)
    xw = [r59.phi_weights(a, panels=6, m=6400) for a, _theta in fam]
    a_mat = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    corr, solve_info = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    base, _ = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
    prime_powers = r59.rig.prime_powers_up_to(math.exp(9.504))
    env = sum(2.0 * weight / math.sqrt(number) for number, weight in prime_powers)
    env += max(
        abs(float(r59.rig.sigma_vec(np.array([2 * math.pi * x]))[0]))
        for x in np.linspace(X0, 400, 2000)
    )
    env += 2.0
    family_data = [
        (float(a), float(theta), abs(b), abs(c))
        for (a, theta), b, c in zip(fam, base, corr)
    ]

    def value_bound(a: float, t: float) -> float:
        log_value = (
            0.5 * a * a
            + math.log(N48_UPPER)
            - (2 * R - 2) * math.log(a)
            - R * math.log(math.hypot(0.5, t))
        )
        if log_value < -745.0:
            return 0.0
        return math.exp(min(log_value, 700.0))

    def envelope(x: float) -> float:
        base_bound = 0.0
        correction_bound = 0.0
        for a, theta, base_coefficient, correction_coefficient in family_data:
            bound = value_bound(a, theta - 2 * math.pi * x)
            base_bound += base_coefficient * bound
            correction_bound += correction_coefficient * bound
        p = abs(float(np.real(
            r59.P_from_nodes(np.array([x]), r80.counterpart_nodes(rho))[0]
        )))
        return env * p * p * base_bound * base_bound * correction_bound * correction_bound

    grid = np.geomspace(X0, XMAX, 5000)
    values_env = np.array([envelope(float(x)) for x in grid])
    tail_numeric = float(np.trapezoid(values_env, grid))
    remainder = float(values_env[-1] * grid[-1] / (4 * R - 9))
    total = tail_numeric + remainder
    result = {
        "record": 2136,
        "status": "FIXED-R48-TAIL-REPRICED-CANDIDATE",
        "owner": "one-copy G8-H",
        "rule_m_for_coefficients": 6400,
        "rung": R,
        "N48_interval_upper": N48_UPPER,
        "x0": X0,
        "xmax_numeric": XMAX,
        "tail_160_to_1e6": tail_numeric,
        "remainder_model": remainder,
        "tail_total": total,
        "q1600_abs": 3.406049871881275e12,
        "l2_charge": 4.412215566637855e10,
        "tail_over_q1600": total / 3.406049871881275e12,
        "tail_over_l2": total / 4.412215566637855e10,
        "solve": solve_info,
        "nonclaims": [
            "the N48 candidate still needs an independent interval audit",
            "the infinity remainder is still an asymptotic model",
            "the owner is the one-copy numerical G8-H candidate",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "variation_source": "results/2135_routea_root_partition_lipschitz.json",
            "owner_source": "results/2058_l5_solve.json",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
