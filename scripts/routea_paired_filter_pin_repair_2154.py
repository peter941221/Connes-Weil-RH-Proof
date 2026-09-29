#!/usr/bin/env python3
"""Same-run pin-repair sensitivity of the paired-filter vertex candidate."""
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

OUTPUT = ROOT / "results" / "2154_routea_paired_filter_pin_repair.json"
WIDTH = 1.0
COEFF = 0.962j


def main() -> None:
    rho = prior.RHO
    known = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    zeros = known + [np.conj(z) for z in known]
    targets, desired, fam, _, base, corr = prior.candidate()
    rules = [density.phi_weights(a, panels=6, m=1600) for a, _ in fam]
    matrix = density.family_values(fam, prior.K, np.asarray(targets, complex), rules).T
    wanted_base = np.ones(len(targets), complex)
    wanted_corr = np.asarray(desired, complex)
    before = {"base": float(np.max(np.abs(matrix@base-wanted_base))),
              "corr": float(np.max(np.abs(matrix@corr-wanted_corr)))}
    delta_base = np.linalg.lstsq(matrix, wanted_base-matrix@base, rcond=None)[0]
    delta_corr = np.linalg.lstsq(matrix, wanted_corr-matrix@corr, rcond=None)[0]
    fixed_base, fixed_corr = base+delta_base, corr+delta_corr
    after = {"base": float(np.max(np.abs(matrix@fixed_base-wanted_base))),
             "corr": float(np.max(np.abs(matrix@fixed_corr-wanted_corr)))}

    xi = np.linspace(-20.0, 20.0, 4001)
    s = 0.5-2j*np.pi*xi
    v = density.family_values(fam, prior.K, s, rules)
    ff = filt.damped_filter_values(s, zeros, rho, WIDTH, 1600)
    raw_weight = np.abs(base@v)**2*np.abs(corr@v)**2*np.abs(ff)**2
    target_poly = np.ones_like(s)
    for z in (rho, 1-np.conj(rho), rho+0.5):
        target_poly *= s-z
    scale = float(abs(target_poly[int(np.argmax(raw_weight))]))
    shape = np.abs(1+COEFF*target_poly/scale)**2
    p = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(rho)))
    support = max(a for a, _ in fam)*2.0+WIDTH

    def gate(b: np.ndarray, c: np.ndarray) -> dict:
        weight = np.abs(b@v)**2*np.abs(c@v)**2*np.abs(ff)**2*shape
        g = density.gate_entries(xi, weight, p, support)
        C,B,D = (float(g[k]) for k in ("C","B01","D"))
        det = C*D-B*B
        return {"C":C,"B01":B,"D":D,"det":det,
                "relative_determinant_margin":-det/(B*B),
                "vertex_signs":bool(C>0 and B>0 and det<0),
                "n_primes":int(g["n_primes"]),"n_covered":int(g["n_covered"])}

    original = gate(base,corr)
    repaired = gate(fixed_base,fixed_corr)
    result = {"record":2154,"status":"PAIRED-FILTER-PIN-REPAIR-SENSITIVITY",
              "owner_model":"2143 trial 162 with 21 known zeros and conjugates",
              "coefficient":[COEFF.real,COEFF.imag],"T_scale":scale,
              "target_error_before":before,"target_error_after":after,
              "coefficient_correction_l2":{"base":float(np.linalg.norm(delta_base)),
                                           "corr":float(np.linalg.norm(delta_corr))},
              "original_gate":original,"repaired_gate":repaired,
              "relative_gate_movement":{k:float(abs(repaired[k]-original[k])/max(abs(original[k]),1e-300))
                                        for k in ("C","B01","D","det")},
              "nonclaims":["least-squares pin repair in float is not an exact interpolation certificate",
                           "known zeros are not the complete formal owner",
                           "sampled finite-window gate is not an integral certificate",
                           "no producer or RH claim"],
              "provenance":{"script":"scripts/routea_paired_filter_pin_repair_2154.py",
                            "parent":"results/2153_routea_paired_filter_nullshape.json"}}
    OUTPUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
