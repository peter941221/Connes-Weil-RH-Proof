#!/usr/bin/env python3
"""Record 2002: pre-registered health-constrained Route-A probe."""

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
T_GRID = np.linspace(0.0, 1.0, 11)
K = 30.0
N = 0
DXI = 0.008 if "--smoke" in sys.argv else 0.004
EIG_CUTOFF = 1.0e-12


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def three_copy_family(nodes, scale, gamma):
    base = r94.family_for_ext(nodes, scale, gamma)
    out = []
    for a, theta in base:
        out.extend([(0.8 * a, theta), (a, theta), (1.2 * a, theta)])
    return out, base


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


def minimum_h1(fam, nodes, values, k, xw):
    matrix = r80.family_values(fam, k, np.asarray(nodes, dtype=complex), xw).T
    gram = h1_gram(fam, k)
    eigvals, eigvecs = np.linalg.eigh(gram)
    largest = float(np.max(eigvals))
    clipped = np.maximum(eigvals, EIG_CUTOFF * largest)
    h_inv = (eigvecs / clipped) @ eigvecs.conj().T
    schur = matrix @ h_inv @ matrix.conj().T
    coeff = h_inv @ matrix.conj().T @ np.linalg.solve(
        schur, np.asarray(values, dtype=complex))
    residual = float(np.max(np.abs(matrix @ coeff - values)))
    return coeff, gram, {
        "constraint_residual": residual,
        "h1_energy": float(np.real(coeff.conj() @ gram @ coeff)),
        "effective_rank": int(np.sum(eigvals > EIG_CUTOFF * largest)),
        "basis_size": len(fam),
    }


def embedded_reference(base_coeff):
    out = np.zeros(3 * len(base_coeff), dtype=complex)
    out[1::3] = base_coeff
    return out


def measure(nodes, rho, values, fam, xw, base, corr, base_info, corr_info, t):
    pins = r80.check_pins(nodes, values, fam, K, xw, (base, corr))
    # check_pins expects correction targets; recompute the actual owner target
    # at the call site and replace this placeholder field below.
    xi = np.linspace(-40.0, 40.0, int(round(80.0 / DXI)) + 1)
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
    certified = finite and spread[2] < 1.0 / 3.0
    return {
        "t": float(t), "finite": finite, "certified": certified,
        "pin_err_base": max(p["err_base"] for p in pins),
        "pin_err_corr": max(p["err_corr"] for p in pins),
        "C": c, "B01": b, "D": d, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1],
        "spread_D": spread[2], "routes": routes,
        "base_h1": base_info["h1_energy"],
        "correction_h1": corr_info["h1_energy"],
    }


def run_case(delta, gamma, scale, tag):
    log("case %s" % tag)
    rho = 0.5 + delta + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam, base_fam = three_copy_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, K)
    base_ref, corr_ref, _amp_info = r80.amplitudes(nodes, values, base_fam, K,
                                               r80.family_quad(base_fam, K))
    base = embedded_reference(base_ref)
    corr_min, gram, corr_info = minimum_h1(fam, nodes, values, K, xw)
    # The base is kept at the committed owner selector; only the correction
    # varies along the registered feasible segment.
    base_info = {"h1_energy": float(np.real(base.conj() @ gram @ base))}
    corr_results = []
    for t in T_GRID:
        corr = (1.0 - t) * corr_min + t * embedded_reference(corr_ref)
        row = measure(nodes, rho, values, fam, xw, base, corr,
                      base_info, corr_info, t)
        corr_results.append(row)
        log("  %s t=%.1f C=%+.3e D=%+.3e det=%+.3e spreadD=%.2e %s" %
            (tag, t, row["C"], row["D"], row["det"],
             row["spread_D"], "CERT" if row["certified"] else "UNRES"))
    healthy = [r for r in corr_results if r["certified"] and r["C"] > 0
               and r["D"] < 0 and r["det"] < 0]
    return {"tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
            "owner_nodes": len(nodes), "rows": corr_results,
            "healthy_rows": healthy}


def main():
    cases = CASES[:1] if "--smoke" in sys.argv else CASES
    rows = [run_case(*case[:3], case[3]) for case in cases]
    if "--smoke" in sys.argv:
        verdict = "SMOKE"
    else:
        good = sum(bool(r["healthy_rows"]) for r in rows)
        verdict = "A-H-GO-CANDIDATE" if good >= 3 else "A-H-NO-GO"
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                       "results", "2002_route_a_health_selector.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2002", "verdict": verdict,
                   "dxi": DXI, "t_grid": list(map(float, T_GRID)),
                   "cases": rows}, stream, indent=2)
        stream.write("\n")
    log("VERDICT: %s" % verdict)
    log("results -> %s" % os.path.abspath(out))


if __name__ == "__main__":
    main()