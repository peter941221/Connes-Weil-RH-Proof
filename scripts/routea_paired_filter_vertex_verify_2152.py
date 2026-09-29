#!/usr/bin/env python3
"""Independent-grid and independent-rule check of record 2151's vertex row."""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_polynomial_zero_filter_2151 as r51  # noqa: E402
import routea_mp_pinned_gate_replay_2143 as prior  # noqa: E402
import routea_overcomplete_h1_fibre_verify_2141 as verify  # noqa: E402
import fourpoint_actual_owner_1980 as actual  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402

OUTPUT = ROOT / "results" / "2152_routea_paired_filter_vertex_verify.json"
WIDTH = 1.0


def run_row(fam, base, corr, zeros, nodes: int, dxi: float) -> dict:
    xi = np.linspace(-20.0, 20.0, int(round(40.0 / dxi)) + 1)
    rules = [density.phi_weights(a, panels=6, m=nodes) for a, _ in fam]
    v = density.family_values(fam, prior.K, 0.5-2j*np.pi*xi, rules)
    w0 = np.abs(base@v)**2*np.abs(corr@v)**2
    ff = r51.damped_filter_values(0.5-2j*np.pi*xi, zeros, prior.RHO, WIDTH, nodes)
    w = w0*np.abs(ff)**2
    p = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(prior.RHO)))
    support = max(a for a, _ in fam)*2.0+WIDTH
    g = density.gate_entries(xi, w, p, support)
    c,b,d = (float(g[k]) for k in ("C","B01","D"))
    det = c*d-b*b
    ab = [float(abs(x-y)/max(abs(y),1e-300)) for x,y in zip(g["prime"]["A"],g["prime"]["B"])]
    mass = float(np.trapezoid(w,xi))
    return {"nodes_per_panel": nodes, "dxi": dxi, "C": c, "B01": b,
            "D": d, "det": det, "vertex_coefficient": b/c,
            "relative_determinant_margin": -det/(b*b),
            "vertex_gate": det/c, "vertex_signs": bool(c>0 and b>0 and det<0),
            "n_primes": int(g["n_primes"]), "n_covered": int(g["n_covered"]),
            "A_vs_B_prime_relative": ab, "window_mass": mass,
            "edge_fraction_15_20": float(np.trapezoid(np.where(np.abs(xi)>=15,w,0.),xi)/mass)}


def main() -> None:
    rho = prior.RHO
    zeros = verify.known_zeros_in_ball(actual.formal_radius(rho,0))
    paired = zeros + [np.conj(z) for z in zeros]
    _, _, fam, _, base, corr = prior.candidate()
    rows = [run_row(fam,base,corr,paired,1600,0.01),
            run_row(fam,base,corr,paired,1600,0.005),
            run_row(fam,base,corr,paired,3200,0.01)]
    ref = rows[-1]
    for row in rows[:-1]:
        row["relative_to_m3200_dxi001"] = {
            k: float(abs(row[k]-ref[k])/max(abs(ref[k]),1e-300))
            for k in ("C","B01","D","det","vertex_gate")}
    result = {"record":2152,"status":"PAIRED-FILTER-VERTEX-REPLICATION",
              "owner_model":"2143 trial 162, 21 known positive-height zeros and their conjugates",
              "filter_degree":len(paired)+2,"damping_width":WIDTH,
              "rows":rows,
              "nonclaims":["not the complete formal owner",
                           "finite-window sampled values are not integral certificates",
                           "same-index spectral tail and parameter uniformity are open",
                           "no producer or RH claim"],
              "provenance":{"script":"scripts/routea_paired_filter_vertex_verify_2152.py",
                            "predecessor":"results/2151_routea_polynomial_zero_filter.json"}}
    OUTPUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
