#!/usr/bin/env python3
"""Cheap screen of an exact finite-zero differential filter on the 2143 owner.

This is a numerical model only.  The known zero list is not the formal owner,
and sampled gate integrals are not certificates.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_mp_pinned_gate_replay_2143 as prior  # noqa: E402
import routea_overcomplete_h1_fibre_verify_2141 as verify  # noqa: E402
import fourpoint_actual_owner_1980 as actual  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402

OUTPUT = ROOT / "results" / "2151_routea_polynomial_zero_filter.json"


def filter_values(s: np.ndarray, zeros: list[complex], rho: complex) -> np.ndarray:
    """Q(s)H(s), with H preserving all three nonzero correction targets."""
    targets = [rho, 1.0 - np.conj(rho), rho + 0.5]
    q = np.ones_like(s, dtype=complex)
    q_at = np.ones(3, dtype=complex)
    for z in zeros:
        q *= (s - z) / (rho - z)
        q_at *= np.asarray([(t-z)/(rho-z) for t in targets])
    h = np.zeros_like(s, dtype=complex)
    for j,t in enumerate(targets):
        basis = np.ones_like(s, dtype=complex)
        for k,u in enumerate(targets):
            if k != j:
                basis *= (s-u)/(t-u)
        h += basis/q_at[j]
    return q * h


def damped_filter_values(s: np.ndarray, zeros: list[complex], rho: complex,
                         width: float, nodes: int) -> np.ndarray:
    """Zero filter with a smooth, carrier-centred compact support factor."""
    targets = [rho, 1.0 - np.conj(rho), rho + 0.5]
    rule = density.phi_weights(width, panels=6, m=nodes)
    ss = np.atleast_1d(np.asarray(s, complex))
    carrier = 1j * rho.imag
    d0 = density.phi_laplace(width, prior.K, np.asarray([rho-carrier]), rule)[0]
    d = density.phi_laplace(width, prior.K, ss-carrier, rule) / d0
    d_at = density.phi_laplace(width, prior.K, np.asarray(targets)-carrier, rule) / d0
    q = np.ones_like(ss)
    q_at = np.ones(3, dtype=complex)
    for z in zeros:
        q *= (ss-z)/(rho-z)
        q_at *= np.asarray([(t-z)/(rho-z) for t in targets])
    h = np.zeros_like(ss, dtype=complex)
    for j,t in enumerate(targets):
        basis = np.ones_like(ss, dtype=complex)
        for k,u in enumerate(targets):
            if k != j:
                basis *= (ss-u)/(t-u)
        h += basis/(q_at[j]*d_at[j])
    return q*d*h


def main() -> None:
    rho = prior.RHO
    zeros = verify.known_zeros_in_ball(actual.formal_radius(rho, 0))
    _, _, fam, xw, base, corr = prior.candidate()
    xi = np.linspace(-40.0, 40.0, 4001)
    weight, _, _, _ = completion.owner_density(density.target_nodes(rho), fam, prior.K, 0, xi, xw, (base, corr))
    s = 0.5 - 2j * np.pi * xi
    filt = filter_values(s, zeros, rho)
    new_weight = weight * np.abs(filt) ** 2
    p = np.real(density.P_from_nodes(xi, completion.counterpart_nodes(rho)))
    support = max(a for a, _ in fam) * 2.0
    old = density.gate_entries(xi, weight, p, support)
    new = density.gate_entries(xi, new_weight, p, support)

    def summary(g: dict) -> dict:
        c, b, d = (float(g[k]) for k in ("C", "B01", "D"))
        ab = None
        if "A" in g["prime"] and "B" in g["prime"]:
            ab = [float(abs(x-y)/max(abs(y),1e-300)) for x,y in zip(g["prime"]["A"],g["prime"]["B"])]
        return {"C": c, "B01": b, "D": d, "det": c*d-b*b,
                "healthy": bool(c > 0 and d < 0 and c*d-b*b < 0),
                "routes": sorted(g["prime"]), "route_key": g["route_key"],
                "n_primes": int(g["n_primes"]),
                "A_vs_B_prime_relative": ab,
                "route_spread": [float(v) for v in density.route_spread(g)]}

    mass = float(np.trapezoid(new_weight, xi))
    edge = np.abs(xi) >= 30.0
    checks = [rho, 1 - np.conj(rho), rho + 0.5] + zeros
    vals = filter_values(np.asarray(checks, complex), zeros, rho)
    evaluator_check = []
    for m in (400, 1600):
        rule = [density.phi_weights(a, panels=6, m=m) for a, _ in fam]
        probe_xi = np.asarray([0.0, 10.0, 20.0, 30.0, 40.0])
        vv = density.family_values(fam, prior.K, 0.5 - 2j * np.pi * probe_xi, rule)
        wb = np.abs(base @ vv) ** 2 * np.abs(corr @ vv) ** 2
        ff = filter_values(0.5 - 2j * np.pi * probe_xi, zeros, rho)
        evaluator_check.append({"m": m, "xi": probe_xi.tolist(),
                                "log10_filtered_weight": [float(math.log10(max(x, 1e-300))) for x in wb * np.abs(ff) ** 2]})
    damping_check = []
    fine_xi = np.asarray([0.0, 10.0, 20.0, 30.0, 40.0])
    fine_rule = [density.phi_weights(a, panels=6, m=1600) for a, _ in fam]
    fine_values = density.family_values(fam, prior.K, 0.5-2j*np.pi*fine_xi, fine_rule)
    fine_weight = np.abs(base @ fine_values)**2 * np.abs(corr @ fine_values)**2
    for width in (0.25, 0.5, 0.75):
        ff = damped_filter_values(0.5-2j*np.pi*fine_xi, zeros, rho, width, 1600)
        vv = fine_weight*np.abs(ff)**2
        damping_check.append({"width": width,
                              "support_radius": support + width,
                              "log10_filtered_weight": [float(math.log10(max(x, 1e-300))) for x in vv],
                              "target_error": float(np.max(np.abs(damped_filter_values(np.asarray(checks[:3], complex), zeros, rho, width, 1600)-1)))})
    # Gate screen uses the higher-node rule and dxi=0.01 on the mass window.
    # This is still a sampled, finite-window reading, not a certificate.
    gate_xi = np.linspace(-20.0, 20.0, 4001)
    gate_values = density.family_values(fam, prior.K, 0.5-2j*np.pi*gate_xi, fine_rule)
    gate_weight = np.abs(base @ gate_values)**2 * np.abs(corr @ gate_values)**2
    gate_p = np.real(density.P_from_nodes(gate_xi, completion.counterpart_nodes(rho)))
    gate_smoke = {"old_m1600": summary(density.gate_entries(gate_xi, gate_weight, gate_p, support))}
    for width in (0.05, 0.1, 0.15, 0.2, 0.25, 0.35, 0.5, 0.75):
        ff = damped_filter_values(0.5-2j*np.pi*gate_xi, zeros, rho, width, 1600)
        w = gate_weight*np.abs(ff)**2
        gate_smoke[str(width)] = {"gate": summary(density.gate_entries(gate_xi, w, gate_p, support+width)),
                                  "window_mass": float(np.trapezoid(w, gate_xi)),
                                  "edge_fraction_15_20": float(np.trapezoid(np.where(np.abs(gate_xi)>=15,w,0.),gate_xi)/np.trapezoid(w,gate_xi))}
    paired_zeros = zeros + [np.conj(z) for z in zeros]
    paired_gate_smoke = {}
    for width in (0.25, 0.5, 0.75, 1.0, 1.5):
        ff = damped_filter_values(0.5-2j*np.pi*gate_xi, paired_zeros, rho, width, 1600)
        w = gate_weight*np.abs(ff)**2
        paired_gate_smoke[str(width)] = {"gate": summary(density.gate_entries(gate_xi, w, gate_p, support+width)),
                                         "window_mass": float(np.trapezoid(w, gate_xi)),
                                         "edge_fraction_15_20": float(np.trapezoid(np.where(np.abs(gate_xi)>=15,w,0.),gate_xi)/np.trapezoid(w,gate_xi))}
    peak_at = [float(gate_xi[int(np.argmax(gate_weight))])]
    for width in (0.25, 0.5):
        ff = damped_filter_values(0.5-2j*np.pi*gate_xi, zeros, rho, width, 1600)
        peak_at.append(float(gate_xi[int(np.argmax(gate_weight*np.abs(ff)**2))]))
    peak_s = 0.5-2j*np.pi*np.asarray(peak_at)
    fine_at = density.family_values(fam, prior.K, peak_s, fine_rule)
    rule3200 = [density.phi_weights(a, panels=6, m=3200) for a, _ in fam]
    check_at = density.family_values(fam, prior.K, peak_s, rule3200)
    v1600 = np.abs(base@fine_at)**2*np.abs(corr@fine_at)**2
    v3200 = np.abs(base@check_at)**2*np.abs(corr@check_at)**2
    peak_rule_check = {"xi": peak_at, "m1600_weight": v1600.tolist(),
                       "m3200_weight": v3200.tolist(),
                       "relative_difference": (np.abs(v1600-v3200)/np.maximum(v3200,1e-300)).tolist()}
    result = {
        "record": 2151, "status": "POLYNOMIAL-ZERO-FILTER-SCREEN",
        "owner_model": "2143 trial 162; 21 known zeros only",
        "filter_degree": len(zeros) + 2,
        "support_radius": support,
        "target_filter_values": [[float(v.real), float(v.imag)] for v in vals[:3]],
        "max_known_zero_filter_value": float(np.max(np.abs(vals[3:]))),
        "old_gate": summary(old), "filtered_gate": summary(new),
        "filtered_mass_on_window": mass,
        "filtered_edge_fraction_30_40": float(np.trapezoid(np.where(edge, new_weight, 0.0), xi) / mass),
        "filter_abs_at_0_20_40": [float(np.abs(filt[np.argmin(np.abs(xi-x))])) for x in (0.,20.,40.)],
        "evaluator_check": evaluator_check,
        "damping_check": damping_check,
        "damped_gate_smoke": gate_smoke,
        "paired_zero_gate_smoke": paired_gate_smoke,
        "peak_rule_check": peak_rule_check,
        "nonclaims": ["known zeros are not the complete formal owner",
                      "sampled window gate and edge fraction are not integral or tail certificates",
                      "no RH or producer claim"],
        "provenance": {"script": "scripts/routea_polynomial_zero_filter_2151.py"},
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
