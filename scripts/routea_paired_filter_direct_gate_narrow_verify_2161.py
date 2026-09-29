#!/usr/bin/env python3
"""Narrow-window rule/grid control after 2160's wide-window alias failure.

New instrument: use the direct prime-kernel B value as the comparison object;
book the FFT-A versus direct-B difference as an absolute charge.  This does
not repair 2159's failed 0.1% route-spread gate or certify the full line.
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

OUTPUT = ROOT / "results" / "2161_routea_paired_filter_direct_gate_narrow_verify.json"
WIDTH = 2.5
XMAX = 20.0
CONFIGS = ((1600, 0.01), (1600, 0.005), (3200, 0.01))


def main() -> None:
    rho = prior.RHO
    known = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    zeros = known + [np.conj(z) for z in known]
    _, _, fam, _, base, corr = prior.candidate()
    support = max(a for a, _ in fam) * 2.0 + WIDTH
    rows = []
    for m, dxi in CONFIGS:
        xi = np.linspace(-XMAX, XMAX, int(round(2*XMAX/dxi))+1)
        s = 0.5 - 2j*np.pi*xi
        rules = [density.phi_weights(a, panels=6, m=m) for a, _ in fam]
        v = density.family_values(fam, prior.K, s, rules)
        ff = filt.damped_filter_values(s, zeros, rho, WIDTH, m)
        w = np.abs(base@v)**2*np.abs(corr@v)**2*np.abs(ff)**2
        g = density.gate_entries(xi, w, np.ones_like(xi), support)
        a = float(g["arch"][0]+g["prime"]["A"][0])
        b = float(g["arch"][0]+g["prime"]["B"][0])
        mass = float(np.trapezoid(w, xi))
        row = {"nodes_per_panel": m, "dxi": dxi,
               "C_route_A": a, "C_route_B": b,
               "A_minus_B_abs": abs(a-b),
               "window_mass": mass,
               "edge_fraction_15_20": float(np.trapezoid(
                   np.where(np.abs(xi)>=15,w,0.0),xi)/mass),
               "n_primes": int(g["n_primes"]),
               "n_covered": int(g["n_covered"])}
        rows.append(row)
        print(json.dumps(row), flush=True)
    base_b = rows[0]["C_route_B"]
    grid_rel = abs(rows[1]["C_route_B"]-base_b)/max(abs(base_b),1e-300)
    rule_rel = abs(rows[2]["C_route_B"]-base_b)/max(abs(base_b),1e-300)
    fft_charge = max(r["A_minus_B_abs"] for r in rows)
    candidate = (all(r["C_route_B"]<0 and r["edge_fraction_15_20"]<=1e-8
                     and r["n_covered"]==r["n_primes"] for r in rows)
                 and grid_rel<=1e-3 and rule_rel<=1e-3
                 and fft_charge<min(-r["C_route_B"] for r in rows))
    result = {"record":2161,"status":"NARROW-DIRECT-B-CONTROL",
              "decision_target":"is 2159's direct-C sign stable on the model's trusted narrow window?",
              "owner_model":"2143 trial 162; 21 known positive-height zeros plus conjugates",
              "width":WIDTH,"xmax":XMAX,"rows":rows,
              "grid_relative_B":grid_rel,"rule_relative_B":rule_rel,
              "booked_A_B_absolute_gap":fft_charge,
              "narrow_candidate":candidate,
              "nonclaims":["2159's registered A/B 0.1% gate remains failed",
                           "known zeros are not the complete formal owner",
                           "window samples are not an integral certificate",
                           "no full-line tail certificate",
                           "no producer or RH claim"]}
    OUTPUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"narrow_candidate":candidate,"output":str(OUTPUT)}),flush=True)


if __name__=="__main__":
    main()
