#!/usr/bin/env python3
"""Prepriced one-parameter null-shape screen for the paired zero filter.

Success requires a sampled vertex margin >= 1e-3 with the exact target and
known-zero constraints preserved.  This is a screen, never a certificate.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_polynomial_zero_filter_2151 as filt  # noqa: E402
import routea_mp_pinned_gate_replay_2143 as prior  # noqa: E402
import routea_overcomplete_h1_fibre_verify_2141 as verify  # noqa: E402
import fourpoint_actual_owner_1980 as actual  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402

OUTPUT = ROOT / "results" / "2153_routea_paired_filter_nullshape.json"
WIDTH = 1.0
COEFFICIENTS = [-2.0, -1.0, -0.5, -0.25, 0.0, 0.25, 0.5, 1.0, 2.0,
                -1.0j, -0.5j, 0.5j] + [1j*round(0.9+0.001*k,10) for k in range(201)] + [
                    round(-0.5+0.05*i,10)+1j*round(0.90+0.01*j,10)
                    for i in range(21) for j in range(13)]


def main() -> None:
    rho = prior.RHO
    known = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    zeros = known + [np.conj(z) for z in known]
    _, _, fam, _, base, corr = prior.candidate()
    xi = np.linspace(-20.0,20.0,4001)
    s = 0.5-2j*np.pi*xi
    rules = [density.phi_weights(a,panels=6,m=1600) for a,_ in fam]
    values = density.family_values(fam,prior.K,s,rules)
    weight = np.abs(base@values)**2*np.abs(corr@values)**2
    ff = filt.damped_filter_values(s,zeros,rho,WIDTH,1600)
    weight *= np.abs(ff)**2
    p = np.real(density.P_from_nodes(xi,completion.counterpart_nodes(rho)))
    gate = density.gate_entries(xi,weight,p,max(a for a,_ in fam)*2.0+WIDTH)
    mu = gate["mu"]
    anchor = [float(np.sum(mu*p**k)) for k in (0,1,2)]
    base_gate = [float(gate[k]) for k in ("C","B01","D")]
    target = np.asarray([rho,1-np.conj(rho),rho+0.5],complex)
    t = np.ones_like(s)
    for z in target:
        t *= s-z
    peak = int(np.argmax(weight))
    scale = float(abs(t[peak]))
    rows = []
    for coeff in COEFFICIENTS:
        mult = np.abs(1.0+coeff*t/scale)**2
        mk = [float(np.sum(mu*mult*p**k)) for k in (0,1,2)]
        c,b,d = mk
        det = c*d-b*b
        margin = -det/(b*b) if b else float("-inf")
        changed_weight = weight*mult
        total = float(np.trapezoid(changed_weight,xi))
        edge = float(np.trapezoid(np.where(np.abs(xi)>=15,changed_weight,0.),xi)/total)
        rows.append({"coefficient":[float(coeff.real),float(coeff.imag)],
                     "C":c,"B01":b,"D":d,"det":det,
                     "relative_determinant_margin":margin,
                     "vertex_signs":bool(c>0 and b>0 and det<0),
                     "screen_go":bool(c>0 and b>0 and det<0 and margin>=1e-3 and edge<1e-8),
                     "edge_fraction_15_20":edge})
    result = {"record":2153,"status":"PAIRED-FILTER-NULLSHAPE-SCREEN",
              "owner_model":"2143 trial 162 plus 21 known zeros and conjugates",
              "width":WIDTH,"xi_peak":float(xi[peak]),"T_scale":scale,
              "moment_anchor":anchor,"gate_entry_anchor":base_gate,
              "anchor_relative_error":[float(abs(x-y)/max(abs(y),1e-300)) for x,y in zip(anchor,base_gate)],
              "threshold":{"margin":1e-3,"edge_fraction":1e-8},
              "rows":rows,"go_count":sum(row["screen_go"] for row in rows),
              "best_vertex_row":max((row for row in rows if row["vertex_signs"]),
                                    key=lambda row:row["relative_determinant_margin"]),
              "nonclaims":["not the complete formal owner","sampled grid is not an integral certificate",
                           "spectral tail and uniformity remain open","no RH claim"],
              "provenance":{"script":"scripts/routea_paired_filter_nullshape_2153.py",
                            "parent":"results/2152_routea_paired_filter_vertex_verify.json"}}
    OUTPUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
