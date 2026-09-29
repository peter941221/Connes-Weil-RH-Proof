#!/usr/bin/env python3
"""Pre-registered direct selected-g gate screen for wider paired filters.

Numerical known-zero under-approximation only.  The decision concerns the
direct C channel, not the auxiliary four-point vertex determinant.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_polynomial_zero_filter_2151 as filt  # noqa: E402
import routea_mp_pinned_gate_replay_2143 as prior  # noqa: E402
import routea_overcomplete_h1_fibre_verify_2141 as verify  # noqa: E402
import fourpoint_actual_owner_1980 as actual  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402

OUTPUT = ROOT / "results" / "2159_routea_paired_filter_direct_gate.json"
WIDTHS = (1.5, 2.0, 2.5)
DXI = 0.01
M = 1600


def main() -> None:
    rho = prior.RHO
    known = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    zeros = known + [np.conj(z) for z in known]
    _, _, fam, _, base, corr = prior.candidate()
    xi = np.linspace(-20.0, 20.0, 4001)
    s = 0.5 - 2j * np.pi * xi
    rules = [density.phi_weights(a, panels=6, m=M) for a, _ in fam]
    v = density.family_values(fam, prior.K, s, rules)
    w_base = np.abs(base @ v) ** 2 * np.abs(corr @ v) ** 2
    base_support = max(a for a, _ in fam) * 2.0
    rows = []
    for width in WIDTHS:
        ff = filt.damped_filter_values(s, zeros, rho, width, M)
        w = w_base * np.abs(ff) ** 2
        gate = density.gate_entries(xi, w, np.ones_like(xi), base_support + width)
        c = float(gate["C"])
        a = float(gate["arch"][0] + gate["prime"].get("A", [math.nan])[0])
        b = float(gate["arch"][0] + gate["prime"].get("B", [math.nan])[0])
        mass = float(np.trapezoid(w, xi))
        edge = float(np.trapezoid(np.where(np.abs(xi) >= 15.0, w, 0.0), xi) / mass)
        spread = abs(a - b) / max(abs(b), 1e-300)
        row = {
            "width": width,
            "support_radius": base_support + width,
            "n_primes": int(gate["n_primes"]),
            "n_covered": int(gate["n_covered"]),
            "C_route_A": a,
            "C_route_B": b,
            "C_selected": c,
            "route_relative_spread": spread,
            "window_mass": mass,
            "edge_fraction_15_20": edge,
            "screen_go": bool(a < 0 and b < 0 and spread <= 1e-3 and edge <= 1e-8),
        }
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {
        "record": 2159,
        "decision_target": "direct ICgate(g.square) < 0 on the registered paired-filter model",
        "owner_model": "2143 trial 162; 21 known positive-height zeros plus conjugates",
        "widths": list(WIDTHS),
        "nodes_per_panel": M,
        "dxi": DXI,
        "go_count": sum(row["screen_go"] for row in rows),
        "rows": rows,
        "nonclaims": [
            "known zeros are not the complete formal source-zero owner",
            "sampled finite-window gate is not an integral certificate",
            "the 2143 float coefficients are not exact target pins",
            "no producer or RH claim",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"go_count": result["go_count"], "output": str(OUTPUT)}), flush=True)


if __name__ == "__main__":
    main()
