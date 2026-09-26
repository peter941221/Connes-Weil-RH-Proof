#!/usr/bin/env python3
"""Record 2006: health-cone shape scan across the feasible fibre.

Samples the restricted-Gram spectrum (ranks 1..17) at four amplitudes per
owner and records the record-1919 signed-measure readout on every row; see
docs/proofs/2006_route_a_health_cone_shape_preregistration.md.
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
RANKS = (1, 2, 4, 6, 9, 12, 14, 17)
SIGMA_GRID = (0.02, 0.05, 0.20, 0.80)
NARROW = 0.75
K = 30.0
N = 0
DXI = 0.008
GAUSS_POINTS = 2400
SVD_TOL = 1.0e-10
CONE_SIGMA = 0.05
MECH_TOL = 0.20
# Instrument bands, keyed on the registered resolution. See record 2007 for
# the calibration that fixes these numbers; nothing here is a physics claim.
ALG_TOL = 1.0e-9
BANDS = {
    0.008: {"anchor_C": 1.0e-2, "anchor_D": 1.0e-3, "det_quad": 5.0e-3,
            "trace": 1.0e-3},
    0.016: {"anchor_C": 6.0e-2, "anchor_D": 3.0e-3, "det_quad": 1.5e-2,
            "trace": 1.0e-3},
}
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERTIFIED_ROUTES = set(r59.CERTIFIED_ROUTES)
ANCHOR_FILE = os.path.join(REPO, "results",
                           "2003_route_a_health_selector.json")


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def two_copy_family(nodes, scale, gamma):
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


def feasible_directions(fam, gram, matrix, ranks):
    _u, sv, vh = np.linalg.svd(matrix)
    rank = int(np.sum(sv > SVD_TOL * sv[0]))
    null = vh[rank:].conj().T
    restricted = null.conj().T @ gram @ null
    restricted = (restricted + restricted.conj().T) / 2.0
    evals, evecs = np.linalg.eigh(restricted)
    order = np.argsort(evals)[::-1]
    spectrum = [float(evals[i] / evals[order[0]]) for i in order]
    out = {}
    for want in ranks:
        idx = order[want - 1]
        raw = null @ evecs[:, idx]
        out[want] = raw / h1_norm(raw, gram)
    return out, {"nullity": int(null.shape[1]), "spectrum": spectrum}


def embedded_reference(base_coeff):
    out = np.zeros(2 * len(base_coeff), dtype=complex)
    out[1::2] = base_coeff
    return out


def load_anchors():
    with open(ANCHOR_FILE, encoding="utf-8") as stream:
        cases = json.load(stream)["cases"]
    return {rec["tag"]: rec["rows"][0] for rec in cases}


def measure(nodes, values, rho, delta, fam, xw, base, corr, cond, rank,
            sigma):
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
            arch, pb = ge["arch"], ge["prime"]["B"]
            c_b = arch[0] + pb[0]
            b_b = arch[1] + pb[1]
            d_b = arch[2] + pb[2]
            det_b = c_b * d_b - b_b * b_b
            vcheck = r59.variance_check(ge["mu"], p, xi, delta, rho.imag)
            tail4, mass = r59.tail_fraction(xi, w, 4.0)
            w0 = float(w[np.argmin(np.abs(xi))])
            triples = {}
            for kk in routes:
                prk = ge["prime"][kk]
                triples[kk] = [float(ge["arch"][i] + prk[i])
                               for i in range(3)]
        else:
            spread = (float("inf"),) * 3
            c = b = d = det = det_b = float("nan")
            c_b = b_b = d_b = w0 = tail4 = mass = float("nan")
            routes, n_primes, vcheck, triples = [], None, None, {}
    pin_err_base = max(p["err_base"] for p in pins)
    pin_err_corr = max(p["err_corr"] for p in pins)
    certified = bool(finite and cond <= 1e8 and pin_err_base <= 1e-6
                     and pin_err_corr <= 1e-6
                     and len(CERTIFIED_ROUTES & set(routes)) >= 2
                     and spread[2] < 1.0 / 3.0)
    ident = {}
    if vcheck and finite:
        scale_det = max(abs(det_b), 1.0)
        ident = {
            "det_B": det_b, "det_var": vcheck["det_var"],
            "det_moment": vcheck["det_moment"],
            "dev_var": abs(det_b - vcheck["det_var"]) / scale_det,
            "dev_moment": abs(det_b - vcheck["det_moment"]) / scale_det,
            "C_B": c_b, "B01_B": b_b, "D_B": d_b,
            "dev_A_C": abs(vcheck["A"] - c_b) / max(abs(c_b), 1.0),
            "dev_alg": abs(vcheck["det_var"] - vcheck["det_moment"])
            / max(abs(vcheck["det_var"]), 1.0),
            "A": vcheck["A"], "f": vcheck["f"],
            "xp": vcheck["xp"] if "xp" in vcheck else None,
            "var_plus": vcheck["var_plus"],
            "var_minus": vcheck["var_minus"],
            "delta_mean": vcheck["delta_mean"],
        }
        try:
            mp, mm, xp, xm, vp, vm = r59.measure_stats(ge["mu"], p)
            ident.update({"mp": float(mp), "mm": float(mm), "xp": float(xp),
                          "xm": float(xm), "var_plus": float(vp),
                          "var_minus": float(vm)})
        except Exception:
            pass
    return {
        "rank": int(rank), "sigma": float(sigma), "finite": finite,
        "certified": certified,
        "healthy": bool(certified and c > 0.0 and d < 0.0 and det < 0.0
                        and c_b > 0.0 and d_b < 0.0 and det_b < 0.0),
        "healthy_ap": bool(certified and c > 0.0 and d < 0.0 and det < 0.0),
        "healthy_b": bool(certified and c_b > 0.0 and d_b < 0.0
                          and det_b < 0.0),
        "n_primes": n_primes, "cond": cond, "routes": routes,
        "route_triples": triples,
        "pin_err_base": pin_err_base, "pin_err_corr": pin_err_corr,
        "C": c, "B01": b, "D": d, "det": det,
        "spread_C": spread[0], "spread_B01": spread[1], "spread_D": spread[2],
        "W0": w0, "tail_gt4": tail4, "mass": mass, "identity": ident,
    }


def run_case(delta, gamma, scale, tag, anchors):
    log("case %s" % tag)
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam, base_fam = two_copy_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, K)
    base_ref, corr_ref, amp_info = r80.amplitudes(
        nodes, values, base_fam, K, r80.family_quad(base_fam, K))
    cond = max(amp_info["base"]["cond"], amp_info["corr"]["cond"])
    gram = h1_gram(fam)
    matrix = r80.family_values(fam, K, np.asarray(nodes, dtype=complex), xw).T
    base = embedded_reference(base_ref)
    corr_committed = embedded_reference(corr_ref)
    e_ref = h1_norm(corr_committed, gram)
    dirs, spec = feasible_directions(fam, gram, matrix, RANKS)
    anchor = measure(nodes, values, rho, delta, fam, xw, base, corr_committed,
                     cond, 0, 0.0)
    ref = anchors.get(tag)
    dev = {}
    if ref:
        for key in ("C", "D"):
            dev[key] = abs(anchor[key] - float(ref[key])) \
                / max(abs(float(ref[key])), 1e-300)
    log("  anchor C=%+.6e D=%+.6e det=%+.4e cert=%s dev_C=%.2e dev_D=%.2e"
        % (anchor["C"], anchor["D"], anchor["det"], anchor["certified"],
           dev.get("C", float("nan")), dev.get("D", float("nan"))))
    rows = []
    for want in RANKS:
        for sigma in SIGMA_GRID:
            corr = corr_committed + sigma * e_ref * dirs[want]
            row = measure(nodes, values, rho, delta, fam, xw, base, corr,
                          cond, want, sigma)
            rows.append(row)
            log("  %s rk=%2d s=%.2f C=%+.4e D=%+.4e det=%+.4e sD=%.1e %s"
                % (tag, want, sigma, row["C"], row["D"], row["det"],
                   row["spread_D"],
                   "HEALTHY" if row["healthy"] else
                   ("cert" if row["certified"] else "UNRES")))
    radius = {}
    ratio = {}
    for want in RANKS:
        sigmas = [r["sigma"] for r in rows
                  if r["rank"] == want and r["healthy"]]
        radius[want] = max(sigmas) if sigmas else None
        top = [r for r in rows if r["rank"] == want
               and abs(r["sigma"] - SIGMA_GRID[-1]) < 1e-12]
        if top and anchor["C"] > 0:
            ratio[want] = top[0]["C"] / anchor["C"]
    return {
        "tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
        "owner_nodes": len(nodes), "basis_size": len(fam), "cond": cond,
        "support_radius": max(a for a, _t in fam) * (N + 2), "e_ref": e_ref,
        "spectrum": spec["spectrum"], "nullity": spec["nullity"],
        "reference_dev": dev, "anchor": anchor,
        "health_radius": {str(k): v for k, v in radius.items()},
        "ratio_at_max_sigma": {str(k): v for k, v in ratio.items()},
        "rows": rows,
    }


def main():
    cases = CASES[:1] if "--smoke" in sys.argv else CASES
    anchors = load_anchors()
    records = [run_case(*case[:3], case[3], anchors) for case in cases]
    band = BANDS[round(DXI, 3)]
    checks = []
    for rec in records:
        dev = rec["reference_dev"]
        anchor_ok = bool(rec["anchor"]["certified"]
                         and dev.get("C", 0.0) <= band["anchor_C"]
                         and dev.get("D", 0.0) <= band["anchor_D"])
        rows_ok = all(r["certified"] for r in rec["rows"])
        ident_ok = all(
            (not r["identity"])
            or (r["identity"]["dev_var"] <= band["det_quad"]
                and r["identity"]["dev_moment"] <= band["det_quad"]
                and r["identity"]["dev_alg"] <= ALG_TOL
                and r["identity"]["dev_A_C"] <= band["trace"])
            for r in rec["rows"])
        checks.append({"tag": rec["tag"], "anchor_ok": anchor_ok,
                       "rows_ok": rows_ok, "identity_ok": ident_ok,
                       "band": band,
                       "max_anchor_dev": max(dev.values()) if dev else None})
    pairs = [(rec["tag"], int(k)) for rec in records
             for k, v in rec["health_radius"].items()
             if v is not None and v >= CONE_SIGMA]
    n_pairs = len(pairs)
    rank_winners = {}
    for rec in records:
        ratio = {int(k): v for k, v in rec["ratio_at_max_sigma"].items()}
        rank_winners[rec["tag"]] = max(ratio, key=ratio.get) if ratio else None
    energetic = sum(1 for j in rank_winners.values() if j in (1, 2, 4))
    placement = sum(1 for j in rank_winners.values() if j in (12, 14, 17))
    mech = []
    for rec in records:
        anchor_f = (rec["anchor"]["identity"] or {}).get("f")
        if anchor_f in (None, 0.0):
            continue
        for want in RANKS:
            top = [r for r in rec["rows"] if r["rank"] == want
                   and abs(r["sigma"] - SIGMA_GRID[-1]) < 1e-12]
            if not top or not top[0]["identity"]:
                continue
            if top[0]["C"] > rec["anchor"]["C"]:
                mech.append(abs(top[0]["identity"]["f"] / anchor_f - 1.0))
    if "--smoke" in sys.argv:
        verdict = "SMOKE"
    elif not all(c["anchor_ok"] and c["rows_ok"] and c["identity_ok"]
                 for c in checks):
        verdict = "INSTRUMENT-FAIL"
    elif n_pairs >= 16:
        verdict = "H-CONE-FAT"
    elif n_pairs <= 1:
        verdict = "H-CONE-THIN"
    else:
        verdict = "H-CONE-STRATIFIED"
    if verdict != "SMOKE" and verdict != "INSTRUMENT-FAIL":
        verdict += "/RANK-" + ("ENERGETIC" if energetic >= 3 else
                               "PLACEMENT" if placement >= 3 else "FLAT")
        if mech:
            verdict += "/MECH-" + ("SCALE" if max(mech) <= MECH_TOL
                                   else "MIX")
    suffix = "_smoke" if "--smoke" in sys.argv else ""
    out = os.path.join(REPO, "results",
                       "2006_route_a_health_cone%s.json" % suffix)
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2006", "verdict": verdict, "dxi": DXI,
                   "ranks": list(RANKS), "sigma_grid": list(SIGMA_GRID),
                   "cone_sigma": CONE_SIGMA, "checks": checks,
                   "healthy_pairs": pairs, "n_healthy_pairs": n_pairs,
                   "rank_winners": rank_winners,
                   "mech_f_relative_changes": mech, "cases": records},
                  stream, indent=2)
        stream.write("\n")
    log("VERDICT: %s" % verdict)
    for check, rec in zip(checks, records):
        log("  %s anchor=%s rows=%s ident=%s radius=%s winner=%s"
            % (check["tag"], check["anchor_ok"], check["rows_ok"],
               check["identity_ok"], rec["health_radius"],
               rank_winners[rec["tag"]]))
    log("healthy (owner, rank) pairs at sigma >= %.2f: %d" %
        (CONE_SIGMA, n_pairs))
    for rec in records:
        ap = sum(1 for r in rec["rows"] if r["healthy_ap"])
        bb = sum(1 for r in rec["rows"] if r["healthy_b"])
        both = sum(1 for r in rec["rows"] if r["healthy"])
        log("  route robustness %s: rows=%d healthy_ap=%d healthy_b=%d"
            " healthy_both=%d" % (rec["tag"], len(rec["rows"]), ap, bb, both))
    log("results -> %s" % out)


if __name__ == "__main__":
    main()
