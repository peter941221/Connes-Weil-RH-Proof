#!/usr/bin/env python3
"""Independent window/rule adjudication of the 2159 direct-C sign crossing."""
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

OUTPUT = ROOT / "results" / "2160_routea_paired_filter_direct_gate_verify.json"
WIDTH = 2.5
DXI = 0.01
CONFIGS = ((20.0, 1600), (40.0, 1600), (40.0, 3200))


def main() -> None:
    rho = prior.RHO
    known = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    zeros = known + [np.conj(z) for z in known]
    _, _, fam, _, base, corr = prior.candidate()
    support = max(a for a, _ in fam) * 2.0 + WIDTH
    rows = []
    for xmax, m in CONFIGS:
        xi = np.linspace(-xmax, xmax, int(round(2*xmax / DXI)) + 1)
        s = 0.5 - 2j * np.pi * xi
        rules = [density.phi_weights(a, panels=6, m=m) for a, _ in fam]
        v = density.family_values(fam, prior.K, s, rules)
        ff = filt.damped_filter_values(s, zeros, rho, WIDTH, m)
        w = np.abs(base@v)**2 * np.abs(corr@v)**2 * np.abs(ff)**2
        gate = density.gate_entries(xi, w, np.ones_like(xi), support)
        a = float(gate["arch"][0] + gate["prime"]["A"][0])
        b = float(gate["arch"][0] + gate["prime"]["B"][0])
        mass = float(np.trapezoid(w, xi))
        row = {
            "xmax": xmax, "nodes_per_panel": m, "dxi": DXI,
            "C_route_A": a, "C_route_B": b,
            "route_relative_spread": abs(a-b)/max(abs(b), 1e-300),
            "n_primes": int(gate["n_primes"]),
            "n_covered": int(gate["n_covered"]),
            "window_mass": mass,
            "edge_fraction_last_5": float(np.trapezoid(
                np.where(np.abs(xi) >= xmax-5.0, w, 0.0), xi)/mass),
        }
        rows.append(row)
        print(json.dumps(row), flush=True)
    rule_rel = abs(rows[1]["C_route_B"]-rows[2]["C_route_B"])/max(
        abs(rows[2]["C_route_B"]), 1e-300)
    eligible = all(r["C_route_A"] < 0 and r["C_route_B"] < 0 and
                   r["route_relative_spread"] <= 1e-3 and
                   r["edge_fraction_last_5"] <= 1e-8
                   for r in rows[1:]) and rule_rel <= 1e-3
    result = {
        "record": 2160,
        "decision_target": "adjudicate 2159 width-2.5 direct-C crossing at unchanged 0.1% route threshold",
        "owner_model": "2143 trial 162; 21 known positive-height zeros plus conjugates",
        "width": WIDTH, "rows": rows,
        "rule_relative_on_large_window": rule_rel,
        "screen_go": eligible,
        "nonclaims": [
            "known zeros are not the complete formal owner",
            "sampled finite-window gate is not an integral certificate",
            "the 2143 float coefficients are not exact target pins",
            "no producer or RH claim",
        ],
    }
    OUTPUT.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"screen_go": eligible, "output": str(OUTPUT)}), flush=True)


if __name__ == "__main__":
    main()
