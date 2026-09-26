#!/usr/bin/env python3
"""Record 2000: pre-registered finite A-V variational selector probe."""

import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402

T0 = time.time()
CASES = [
    (0.10, r94.G5, 0.92, "G5-H"),
    (0.10, r94.G5, 0.90, "G5-W"),
    (0.10, r94.G7, 0.92, "G7-H"),
    (0.10, r94.G8, 0.88, "G8-H"),
]
K = 30.0
N = 0
DXI = 0.008 if "--smoke" in sys.argv else 0.004
EIG_CUTOFF = 1.0e-12


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def overcomplete_family(nodes, scale, gamma):
    base = r94.family_for_ext(nodes, scale, gamma)
    out = []
    for a, theta in base:
        out.extend([(0.86 * a, theta), (1.14 * a, theta)])
    return out


def h1_gram(fam, k):
    amax = max(a for a, _theta in fam)
    xg, wg = np.polynomial.legendre.leggauss(800)
    x = amax * xg
    w = amax * wg
    phi = np.zeros((len(fam), len(x)), dtype=complex)
    dphi = np.zeros_like(phi)
    for j, (a, theta) in enumerate(fam):
        u = x / a
        inside = np.abs(u) < 1.0
        core = np.zeros_like(x)
        core[inside] = np.exp(-k / (1.0 - u[inside] ** 2))
        phase = np.exp(1j * theta * x)
        phi[j] = core * phase
        deriv_core = np.zeros_like(x)
        denom = 1.0 - u[inside] ** 2
        deriv_core[inside] = core[inside] * (
            -2.0 * k * x[inside] / (a * a * denom * denom))
        dphi[j] = (deriv_core + 1j * theta * core) * phase
    gram = (phi.conj() * w) @ phi.T + (dphi.conj() * w) @ dphi.T
    return (gram + gram.conj().T) / 2.0


def minimum_h1_coefficients(fam, nodes, values, k, xw):
    matrix = r80.family_values(fam, k, np.asarray(nodes, dtype=complex), xw).T
    gram = h1_gram(fam, k)
    eigvals, eigvecs = np.linalg.eigh(gram)
    largest = float(np.max(eigvals))
    floor = EIG_CUTOFF * largest
    clipped = np.maximum(eigvals, floor)
    h_inv = (eigvecs / clipped) @ eigvecs.conj().T
    schur = matrix @ h_inv @ matrix.conj().T
    coeff = h_inv @ matrix.conj().T @ np.linalg.solve(
        schur, np.asarray(values, dtype=complex))
    residual = float(np.max(np.abs(matrix @ coeff - values)))
    energy = float(np.real(coeff.conj() @ gram @ coeff))
    cond = float(np.max(clipped) / np.min(clipped))
    rank = int(np.sum(eigvals > floor))
    return coeff, {
        "constraint_residual": residual,
        "h1_energy": energy,
        "coefficient_norm": float(np.linalg.norm(coeff)),
        "gram_condition_cutoff": cond,
        "effective_rank": rank,
        "basis_size": len(fam),
        "owner_nodes": len(nodes),
    }


def run_case(delta, gamma, scale, tag):
    log("case %s delta=%.2f gamma=%.6f scale=%.2f" %
        (tag, delta, gamma, scale))
    rho = 0.5 + delta + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam = overcomplete_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, K)
    base_values = np.ones(len(nodes), dtype=complex)
    corr_values = np.asarray(values, dtype=complex)
    base, base_info = minimum_h1_coefficients(
        fam, nodes, base_values, K, xw)
    corr, corr_info = minimum_h1_coefficients(
        fam, nodes, corr_values, K, xw)
    pins = r80.check_pins(nodes, values, fam, K, xw, (base, corr))
    pin_base = max(p["err_base"] for p in pins)
    pin_corr = max(p["err_corr"] for p in pins)
    xi_max = 40.0
    xi = np.linspace(-xi_max, xi_max, int(round(2 * xi_max / DXI)) + 1)
    with np.errstate(over="ignore", invalid="ignore"):
        w, lb, _lc, _ratio = r80.owner_density(
            nodes, fam, K, N, xi, xw, (base, corr))
        finite = bool(np.isfinite(w).all()) and bool(np.isfinite(lb).all())
        if finite:
            p = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            support = max(a for a, _theta in fam) * (N + 2)
            ge = r59.gate_entries(xi, w, p, support)
            spread = r59.route_spread(ge)
            c, b, d = ge["C"], ge["B01"], ge["D"]
            det = c * d - b * b
            routes = sorted(ge["prime"].keys())
        else:
            ge = None
            spread = (float("inf"),) * 3
            c = b = d = det = float("nan")
            routes = []
    certified = finite and pin_base <= 1e-6 and pin_corr <= 1e-6 \
        and len(set(routes) & {"A", "Ap", "B"}) >= 2 \
        and spread[2] < 1.0 / 3.0
    margin_proxy = -d / (1.0 + base_info["h1_energy"] + corr_info["h1_energy"])
    result = {
        "tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
        "n": N, "k": K, "owner_nodes": len(nodes),
        "pin_err_base": pin_base, "pin_err_corr": pin_corr,
        "finite": finite, "certified": certified,
        "base": base_info, "correction": corr_info,
        "C": c, "B01": b, "D": d, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1],
        "spread_D": spread[2], "routes": routes,
        "margin_proxy": margin_proxy,
    }
    log("  nodes=%d basis=%d pins %.1e/%.1e rank=%d/%d | C=%+.4e D=%+.4e "
        "det=%+.4e spreadD=%.2e proxy=%+.4e -> %s" % (
            len(nodes), len(fam), pin_base, pin_corr,
            base_info["effective_rank"], base_info["basis_size"],
            c, d, det, spread[2], margin_proxy,
            "CERTIFIED" if certified else "UNRESOLVED"))
    return result


def main():
    cases = CASES[:1] if "--smoke" in sys.argv else CASES
    rows = [run_case(*case[:3], case[3]) for case in cases]
    if "--smoke" in sys.argv:
        verdict = "SMOKE"
    elif all(r["certified"] and r["C"] > 0 and r["D"] < 0
             and r["det"] < 0 and r["margin_proxy"] > 0 for r in rows):
        verdict = "A-V-GO-CANDIDATE"
    elif any(not r["certified"] or r["D"] >= 0 or r["det"] >= 0
             or r["margin_proxy"] <= 0 for r in rows):
        verdict = "A-V-NO-GO"
    else:
        verdict = "A-V-UNRESOLVED"
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "2000_route_a_variational_probe.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2000", "verdict": verdict,
                   "dxi": DXI, "eig_cutoff": EIG_CUTOFF,
                   "cases": rows}, stream, indent=2)
        stream.write("\n")
    log("VERDICT: %s" % verdict)
    log("results -> %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()