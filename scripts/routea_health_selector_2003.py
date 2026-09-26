#!/usr/bin/env python3
"""Record 2003: A-H feasible-fiber ray scan (support preserving).

Supersedes the record-2002 instrument. The registered object is a scan along
canonical unit-H1 directions in the nullspace of the interpolation operator,
which keeps the pins exact without inverting the numerically singular H1
Gram; see docs/proofs/2003_route_a_health_selector_reregistration.md.
"""

import json
import math
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
REF_FILES = ("results/1996_gamma78_full_sweep.json",
             "results/1994b_ext_convention_control.json")
SIGMA_GRID = (0.00, 0.02, 0.05, 0.10, 0.20, 0.40, 0.80)
N_DIRECTIONS = 2
K = 30.0
N = 0
DXI = 0.008 if "--smoke" in sys.argv else 0.004
NARROW = 0.75
GAUSS_POINTS = 2400
SVD_TOL = 1.0e-10
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERTIFIED_ROUTES = set(r59.CERTIFIED_ROUTES)
REF_TOL = 1.0e-6
CONE_SIGMA = 0.05


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def two_copy_family(nodes, scale, gamma):
    """Overcomplete family whose widest copy is the committed width."""
    base = r94.family_for_ext(nodes, scale, gamma)
    out = []
    for a, theta in base:
        out.extend([(NARROW * a, theta), (a, theta)])
    return out, base


def h1_gram(fam):
    amax = max(a for a, _theta in fam)
    xg, wg = np.polynomial.legendre.leggauss(GAUSS_POINTS)
    x = amax * xg
    w = amax * wg
    phi = np.zeros((len(fam), len(x)), dtype=complex)
    dphi = np.zeros_like(phi)
    for j, (a, theta) in enumerate(fam):
        u = x / a
        inside = np.abs(u) < 1.0
        core = np.zeros_like(x)
        core[inside] = np.exp(-K / (1.0 - u[inside] ** 2))
        phase = np.exp(1j * theta * x)
        phi[j] = core * phase
        deriv_core = np.zeros_like(x)
        denom = 1.0 - u[inside] ** 2
        deriv_core[inside] = core[inside] * (
            -2.0 * K * x[inside] / (a * a * denom * denom))
        dphi[j] = (deriv_core + 1j * theta * core) * phase
    gram = (phi.conj() * w) @ phi.T + (dphi.conj() * w) @ dphi.T
    return (gram + gram.conj().T) / 2.0


def h1_norm(vector, gram):
    return math.sqrt(max(float(np.real(vector.conj() @ gram @ vector)), 0.0))


def feasible_directions(fam, gram, matrix, count):
    """Unit-H1 nullspace directions of the interpolation operator."""
    _u, sv, vh = np.linalg.svd(matrix)
    rank = int(np.sum(sv > SVD_TOL * sv[0]))
    null = vh[rank:].conj().T
    if null.shape[1] == 0:
        raise RuntimeError("empty feasible fiber")
    restricted = null.conj().T @ gram @ null
    restricted = (restricted + restricted.conj().T) / 2.0
    evals, evecs = np.linalg.eigh(restricted)
    order = np.argsort(evals)[::-1]
    dirs, info = [], {"rank": rank, "nullity": int(null.shape[1]),
                      "sv_max": float(sv[0]), "sv_min": float(sv[-1])}
    for j in range(count):
        idx = order[j]
        raw = null @ evecs[:, idx]
        norm = h1_norm(raw, gram)
        dirs.append(raw / norm)
        info["dir%d_energy_gap" % (j + 1)] = float(evals[idx] / evals.max())
    info["restricted_rel_eigs"] = [float(v / evals.max())
                                   for v in evals[order[:5]]]
    return dirs, info


def embedded_reference(base_coeff):
    out = np.zeros(2 * len(base_coeff), dtype=complex)
    out[1::2] = base_coeff
    return out


def load_references():
    refs = {}
    for rel in REF_FILES:
        with open(os.path.join(REPO, rel), encoding="utf-8") as stream:
            rows = json.load(stream).get("cases", [])
        for row in rows:
            for delta, gamma, scale, tag in CASES:
                if abs(row["delta"] - delta) < 1e-9 \
                        and abs(row["gamma"] - gamma) < 1e-6 \
                        and abs(row["scale"] - scale) < 1e-9:
                    refs.setdefault(tag, {"file": rel, "row": row})
    return refs


def measure(nodes, values, rho, fam, xw, base, corr, cond, direction, sigma):
    pins = r80.check_pins(nodes, values, fam, K, xw, (base, corr))
    xi = np.linspace(-40.0, 40.0, int(round(80.0 / DXI)) + 1)
    with np.errstate(over="ignore", invalid="ignore"):
        w, lb, _lc, _ratio = r80.owner_density(nodes, fam, K, N, xi, xw,
                                               (base, corr))
        finite = bool(np.isfinite(w).all()) and bool(np.isfinite(lb).all())
        if finite:
            p = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
            support = max(a for a, _theta in fam) * (N + 2)
            ge = r59.gate_entries(xi, w, p, support)
            spread = r59.route_spread(ge)
            c, b, d = ge["C"], ge["B01"], ge["D"]
            det = c * d - b * b
            routes = sorted(ge["prime"].keys())
            n_primes = int(ge["n_primes"])
        else:
            spread = (float("inf"),) * 3
            c = b = d = det = float("nan")
            routes, n_primes = [], None
    pin_err_base = max(p["err_base"] for p in pins)
    pin_err_corr = max(p["err_corr"] for p in pins)
    two_route = len(CERTIFIED_ROUTES & set(routes)) >= 2
    certified = bool(finite and cond <= 1e8 and pin_err_base <= 1e-6
                     and pin_err_corr <= 1e-6 and two_route
                     and spread[2] < 1.0 / 3.0)
    return {
        "direction": int(direction), "sigma": float(sigma),
        "finite": finite, "certified": certified,
        "healthy": bool(certified and c > 0.0 and d < 0.0 and det < 0.0),
        "two_route": two_route, "n_primes": n_primes, "cond": cond,
        "pin_err_base": pin_err_base, "pin_err_corr": pin_err_corr,
        "C": c, "B01": b, "D": d, "det": det, "routes": routes,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
    }


def run_case(delta, gamma, scale, tag, refs):
    log("case %s" % tag)
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam, base_fam = two_copy_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, K)
    base_ref, corr_ref, amp_info = r80.amplitudes(
        nodes, values, base_fam, K, r80.family_quad(base_fam, K))
    cond = max(amp_info["base"]["cond"], amp_info["corr"]["cond"])
    gram = h1_gram(fam)
    matrix = r80.family_values(fam, K, np.asarray(nodes, dtype=complex),
                               xw).T
    base = embedded_reference(base_ref)
    corr_committed = embedded_reference(corr_ref)
    e_ref = h1_norm(corr_committed, gram)
    dirs, dir_info = feasible_directions(fam, gram, matrix, N_DIRECTIONS)
    residual = float(np.max(np.abs(matrix @ dirs[0])))
    log("  support=%.4f cond=%.1e E_ref=%.4e nullity=%d dir_resid=%.2e"
        % (max(a for a, _t in fam) * (N + 2), cond, e_ref,
           dir_info["nullity"], residual))
    rows = []
    for j, direction in enumerate(dirs, start=1):
        for sigma in SIGMA_GRID:
            corr = corr_committed + sigma * e_ref * direction
            row = measure(nodes, values, rho, fam, xw, base, corr, cond,
                          j, sigma)
            rows.append(row)
            log("  %s dir%d s=%.2f C=%+.4e D=%+.4e det=%+.4e sD=%.2e np=%s %s"
                % (tag, j, sigma, row["C"], row["D"], row["det"],
                   row["spread_D"], row["n_primes"],
                   "HEALTHY" if row["healthy"] else
                   ("CERT" if row["certified"] else "UNRES")))
    ref = refs.get(tag)
    dev = {}
    if ref is not None:
        anchor = rows[0]
        for key in ("C", "B01", "D"):
            magnitude = max(abs(float(ref["row"][key])), 1e-300)
            dev[key] = abs(anchor[key] - float(ref["row"][key])) / magnitude
    radii = {}
    for j in range(1, N_DIRECTIONS + 1):
        sigmas = [r["sigma"] for r in rows
                  if r["direction"] == j and r["healthy"]]
        radii["dir%d" % j] = max(sigmas) if sigmas else None
    return {
        "tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
        "owner_nodes": len(nodes), "basis_size": len(fam), "cond": cond,
        "support_radius": max(a for a, _t in fam) * (N + 2),
        "e_ref": e_ref, "direction_info": dir_info,
        "direction_residual": residual,
        "reference_file": (ref["file"] if ref else None),
        "reference_dev": dev, "health_radius": radii, "rows": rows,
    }


def main():
    cases = CASES[:1] if "--smoke" in sys.argv else CASES
    refs = load_references()
    rows = [run_case(*case[:3], case[3], refs) for case in cases]
    checks = []
    for rec in rows:
        ref = refs.get(rec["tag"])
        dev = rec["reference_dev"]
        endpoint_certified = rec["rows"][0]["certified"]
        ok = bool(ref) and endpoint_certified and all(
            value <= REF_TOL for value in dev.values())
        checks.append({"tag": rec["tag"], "reference_present": bool(ref),
                       "anchor_certified": endpoint_certified,
                       "max_rel_dev": max(dev.values()) if dev else None,
                       "ok": ok})
    if "--smoke" in sys.argv:
        verdict = "SMOKE"
    elif not all(c["ok"] for c in checks):
        verdict = "INSTRUMENT-FAIL"
    else:
        interior = sum(
            max([radii for radii in rec["health_radius"].values()
                 if radii is not None], default=0.0) >= CONE_SIGMA
            for rec in rows)
        if interior >= 3:
            verdict = "A-H-CONE-NONEMPTY"
        elif interior == 0:
            verdict = "A-H-CONE-EMPTY"
        else:
            verdict = "A-H-CONE-MIXED"
    out = os.path.join(REPO, "results", "2003_route_a_health_selector.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2003", "verdict": verdict, "dxi": DXI,
                   "sigma_grid": list(SIGMA_GRID), "cone_sigma": CONE_SIGMA,
                   "reference_tol": REF_TOL, "reference_check": checks,
                   "cases": rows}, stream, indent=2)
        stream.write("\n")
    log("VERDICT: %s" % verdict)
    for check, rec in zip(checks, rows):
        log("  %s ref=%s anchor_cert=%s maxdev=%s radius=%s"
            % (check["tag"], check["reference_present"],
               check["anchor_certified"], check["max_rel_dev"],
               rec["health_radius"]))
    log("results -> %s" % out)


if __name__ == "__main__":
    main()
