#!/usr/bin/env python3
"""Record 2028: Route-B Cut-1 coupling scan.

Pre-registered in docs/proofs/2028_coupling_scan_preregistration.md.

Questions:
  Q1  does lambda_n keep a positive lower bound as n grows?
  Q2  does det_n keep its sign as n grows?
  Q3  is n admissible far enough for the (1/2)^n tail to close?

The owner is exactly the record-1980/1981 known-zero under-approximation, so
every reading here is an UNDERAPPROXIMATION reading.  Nothing here is an
interval certificate, a determinant theorem, or an RH claim.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as owner_probe   # noqa: E402
import fourpoint_diagonal_sign_1918 as rig          # noqa: E402
import fourpoint_owner_density_1959 as legacy       # noqa: E402
import fourpoint_powered_seed_1981 as powered       # noqa: E402

T0 = time.time()

RHO = powered.RHO
N = powered.N

# registered instrument (pre-registration section 5)
XI_MAX = 25.0
DXI_PRIMARY = 0.02
N_MAX = 7
REFINE_N = (0, 1, 2, 3, 4)          # the pre-registered reproduction anchor
REFINE_DXI = (0.05, 0.02, 0.01, 0.005, 0.002, 0.001)
ROUTE_CAPS = {"Ap": 4000, "B": 60000, "A": 3000000}
CERTIFIED_ROUTES = ("Ap", "B")
SEED_ORDER = 300
CHUNK = 256
N_PREDICT = (8, 10, 12, 20, 47)


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


# ------------------------------------------------------------------ primes

def fast_prime_powers_up_to(xmax):
    """Sieved prime powers as two numpy arrays (value, log of its prime).

    Semantically identical to ``rig.prime_powers_up_to`` but the final scan
    uses ``np.flatnonzero`` instead of a python loop over every integer, which
    is the difference between O(x) and O(pi(x)) python steps.
    """
    if xmax < 2:
        return np.zeros(0, dtype=np.int64), np.zeros(0, dtype=float)
    n = int(math.floor(xmax))
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.flatnonzero(sieve)
    values = []
    logs = []
    for p in primes.tolist():
        lp = math.log(p)
        pk = p
        while pk <= n:
            values.append(pk)
            logs.append(lp)
            pk *= p
    order = np.argsort(np.asarray(values, dtype=np.int64))
    return (np.asarray(values, dtype=np.int64)[order],
            np.asarray(logs, dtype=float)[order])


def validation_block():
    checks = []
    for xmax in (50.0, 1000.0, 5000.0):
        ref = rig.prime_powers_up_to(xmax)
        ref_v = [int(k) for k, _ in ref]
        ref_l = [float(l) for _, l in ref]
        got_v, got_l = fast_prime_powers_up_to(xmax)
        ok = (ref_v == got_v.tolist()) and (
            not ref_l or float(np.max(np.abs(np.asarray(ref_l) - got_l))) == 0.0)
        checks.append({"xmax": xmax, "reference_count": len(ref_v),
                       "candidate_count": int(got_v.size), "identical": bool(ok)})
    return {"prime_power_generator_validation": checks,
            "all_identical": bool(all(c["identical"] for c in checks))}


# ------------------------------------------------------------------ kernel

def direct_prime_channel(xi, pset_values, pset_logs):
    """Prime kernel on the uniform grid, vectorized in chunks.

    The oscillation frequency is log(p^k) while the von Mangoldt weight is
    log(p); conflating the two is a silent order-1e-1 relative error on the
    prime channel (caught by the record-1981 anchor check).
    """
    kernel = np.zeros_like(xi)
    values = pset_values.astype(float)
    weights = 2.0 * pset_logs / np.sqrt(values)
    freqs = np.log(values)
    two_pi = 2.0 * math.pi
    for start in range(0, freqs.size, CHUNK):
        block = freqs[start:start + CHUNK]
        wblock = weights[start:start + CHUNK]
        kernel += np.cos(two_pi * np.outer(xi, block)).dot(wblock)
    return kernel


def fft_prime_channel(xi, integrands, pset_values, pset_logs):
    """Route A: dual FFT plus spline interpolation at log k (record 1959)."""
    npts = xi.shape[0]
    dxi = float(xi[1] - xi[0])
    xs_dual = np.fft.fftfreq(npts, d=dxi)
    nyquist = float(np.max(np.abs(xs_dual)))
    values = pset_values.astype(float)
    freqs = np.log(values)
    covered = int(np.sum(freqs <= nyquist))
    if covered == 0:
        return None, {"nyquist": nyquist, "n_covered": 0,
                      "max_log_k": float(freqs.max()) if freqs.size else 0.0}
    good = freqs <= nyquist
    lg = freqs[good]
    lam = 2.0 * pset_logs[good] / np.sqrt(values[good])
    out = []
    for f in integrands:
        F = np.fft.fft(f) * dxi * np.exp(-2j * np.pi * float(xi[0]) * xs_dual)
        r = legacy.interpolate_dual(F, xs_dual, lg)
        out.append(float(np.sum(lam * r.real)))
    return out, {"nyquist": nyquist, "n_covered": covered,
                 "max_log_k": float(freqs.max()),
                 "capture_fraction": float(covered) / float(freqs.size)}


def route_availability(count):
    return [name for name in ("Ap", "B", "A") if count <= ROUTE_CAPS[name]]


# ------------------------------------------------------------------ owner

def build_density(xi, seed_transform, seed0, owner, targets, values, n):
    axis = 0.5 - 2j * math.pi * xi
    base_values = [1.0 + 0j] * len(targets)
    lb = owner_probe.cardinal_transform(
        targets, base_values, seed0, axis, seed_transform)
    lc = owner_probe.cardinal_transform(
        owner, values, seed0, axis, seed_transform)
    return np.abs(lb) ** (2 * (n + 1)) * np.abs(lc) ** 2


def main() -> None:
    report = {
        "record": 2028,
        "status": "PENDING",
        "preregistration": "docs/proofs/2028_coupling_scan_preregistration.md",
        "rho": [RHO.real, RHO.imag],
        "N": N,
        "owner_model": ("known zeta zeros in formal closed ball + hypothetical "
                        "orbit + healthy targets (UNDERAPPROXIMATION)"),
        "route_caps": ROUTE_CAPS,
        "certified_routes": list(CERTIFIED_ROUTES),
    }

    log("validation block")
    report.update(validation_block())
    if os.environ.get("RH_COUPLING_SMOKE"):
        print(json.dumps(report["prime_power_generator_validation"], indent=2))
        return

    owner, targets, radius, known = owner_probe.build_owner(RHO, N)
    values = [owner_probe.target_value(RHO, z) for z in owner]
    seed_transform = powered.make_powered_seed(order=SEED_ORDER)
    seed0 = complex(seed_transform(np.array([0j]))[0])
    centered_orbit = [z - 0.5 for z in targets[:4]]
    report["owner_cardinality"] = len(owner)
    report["known_zero_count"] = len(known)
    report["target_cardinality"] = len(targets)
    report["min_separation"] = owner_probe.min_separation(owner)
    report["radius"] = radius

    # ------------------------------------------------------ structural block
    log("structural block (exact: support / prime book / routes)")
    structural = []
    counts = {}
    for n in range(0, N_MAX + 1):
        s_n = 2.0 * (n + 2)
        vals, logs = fast_prime_powers_up_to(math.exp(s_n))
        counts[n] = int(vals.size)
        structural.append({
            "n": n,
            "support_radius": s_n,
            "prime_power_count": int(vals.size),
            "max_log_k": float(logs.max()) if logs.size else 0.0,
            "routes_available": route_availability(int(vals.size)),
            "certified_route_available": bool(
                any(r in route_availability(int(vals.size))
                    for r in CERTIFIED_ROUTES)),
            "measurement": "exact",
        })
    for n in N_PREDICT:
        if n in counts:
            continue
        s_n = 2.0 * (n + 2)
        structural.append({
            "n": n,
            "support_radius": s_n,
            "prime_power_count": None,
            "prime_power_count_predicted": float(math.exp(s_n) / s_n),
            "routes_available": [],
            "certified_route_available": False,
            "measurement": "PREDICTED (PNT envelope, not sieved)",
        })
    report["structural"] = structural

    # ----------------------------------------------------------- trend block
    log("trend block at dxi=%.3f" % DXI_PRIMARY)
    xi = np.arange(-XI_MAX, XI_MAX + 0.5 * DXI_PRIMARY, DXI_PRIMARY)
    dxi = float(xi[1] - xi[0])
    log("  |xi| grid points = %d" % xi.size)
    trend = []
    for n in range(0, N_MAX + 1):
        s_n = 2.0 * (n + 2)
        W = build_density(xi, seed_transform, seed0, owner, targets, values, n)
        P = np.real(legacy.P_from_nodes(xi, centered_orbit))
        integrands = (W, P * W, P * P * W)
        sig = rig.sigma_vec(2.0 * np.pi * xi)
        arch = [float(np.trapezoid(sig * f, xi)) for f in integrands]
        vals, logs = fast_prime_powers_up_to(math.exp(s_n))
        avail = route_availability(int(vals.size))
        row = {
            "n": n,
            "support_radius": s_n,
            "prime_power_count": int(vals.size),
            "routes_available": avail,
            "arch": arch,
        }
        prime_by_route = {}
        if "B" in avail:
            log("  n=%d direct route (%d prime powers)" % (n, vals.size))
            kp = direct_prime_channel(xi, vals, logs)
            prime_by_route["B"] = [float(np.trapezoid(kp * f, xi))
                                   for f in integrands]
        if "A" in avail:
            log("  n=%d route A" % n)
            pa, meta = fft_prime_channel(xi, integrands, vals, logs)
            row["route_A_coverage"] = meta
            if pa is not None and meta["n_covered"] == vals.size:
                prime_by_route["A"] = pa
            elif pa is not None:
                row["route_A_note"] = (
                    "partial coverage %d/%d: prime channel truncated at Nyquist"
                    % (meta["n_covered"], vals.size))
        row["prime_by_route"] = prime_by_route
        key = next((kk for kk in CERTIFIED_ROUTES if kk in prime_by_route),
                   next(iter(prime_by_route), None))
        row["route_key"] = key
        if key is not None:
            pr = prime_by_route[key]
            C = arch[0] + pr[0]
            b = arch[1] + pr[1]
            D = arch[2] + pr[2]
            det = C * D - b * b
            lam = b / C if C != 0 else float("nan")
            H = 3.0 + abs(RHO)
            base_c4, base_c2, corr_c2 = report_precomputed_decay(
                seed_transform, seed0, owner, targets, values)
            L = (H ** 4 * (H ** 4 + abs(lam)) ** 2 * (2.0 * math.pi) ** 12 *
                 ((0.5 ** n) * base_c4 * corr_c2) ** 2)
            row.update({
                "C": C, "b": b, "D": D, "det": det, "lambda": lam,
                "cancellation_depth": (-det / (C * D)) if C * D != 0 else None,
                "gate_signs": bool(C > 0 and b > 0 and det < 0),
                "tail_proxy_L_over_lambda_sq": (
                    L / (lam * lam) if lam else float("inf")),
            })
        trend.append(row)
    report["decay_constants"] = {
        "base_C4": base_c4_last[0], "base_C2": base_c4_last[1],
        "correction_C2": base_c4_last[2], "source": "record 1981 grid values",
    }
    report["trend"] = trend

    # ------------------------------------------------------ refinement block
    log("refinement block (aliasing audit)")
    committed = json.loads(
        (ROOT / "results" / "1981_powered_seed_underapprox.json").read_text())
    refine = []
    for n in REFINE_N:
        s_n = 2.0 * (n + 2)
        vals, logs = fast_prime_powers_up_to(math.exp(s_n))
        anchor = None
        for d in REFINE_DXI:
            xg = np.arange(-XI_MAX, XI_MAX + 0.5 * d, d)
            Wg = build_density(xg, seed_transform, seed0, owner, targets,
                               values, n)
            Pg = np.real(legacy.P_from_nodes(xg, centered_orbit))
            sigg = rig.sigma_vec(2.0 * np.pi * xg)
            fs = (Wg, Pg * Wg, Pg * Pg * Wg)
            arch = [float(np.trapezoid(sigg * f, xg)) for f in fs]
            kp = direct_prime_channel(xg, vals, logs)
            pr = [float(np.trapezoid(kp * f, xg)) for f in fs]
            C = arch[0] + pr[0]
            b = arch[1] + pr[1]
            D = arch[2] + pr[2]
            det = C * D - b * b
            row = {"n": n, "dxi": d, "grid_points": int(xg.size),
                   "C": C, "b": b, "D": D, "det": det}
            if d == REFINE_DXI[0]:
                anchor = row
            if anchor is not None:
                row["C_dev_vs_finest_anchor"] = abs(C / anchor["C"] - 1.0)
                row["D_dev_vs_finest_anchor"] = abs(D / anchor["D"] - 1.0)
                row["det_dev_vs_anchor"] = abs(det / anchor["det"] - 1.0)
            ref = next((it for it in committed["rows"] if it["n"] == n), None)
            if ref is not None:
                row["C_committed_1981"] = ref["C"]
                row["C_dev_vs_committed_1981"] = abs(C / ref["C"] - 1.0)
                row["D_dev_vs_committed_1981"] = abs(D / ref["D"] - 1.0)
                row["det_dev_vs_committed_1981"] = (
                    abs(det / ref["det"] - 1.0) if ref["det"] else None)
            refine.append(row)
            log("    n=%d dxi=%g points=%d C=%.6e D=%.6e" % (
                n, d, xg.size, C, D))
    report["refinement"] = refine

    # ------------------------------------------------------------ verdicts
    readable = [row for row in trend if "lambda" in row]
    det_flip = [row["n"] for row in readable if not row["gate_signs"]
                and row.get("route_key") in CERTIFIED_ROUTES]
    lam_vals = [abs(row["lambda"]) for row in readable]
    blocks_n = next((row["n"] for row in structural
                     if not row["certified_route_available"]
                     and row["measurement"] == "exact"), None)
    report["verdicts"] = {
        "readable_n_with_gate": [row["n"] for row in readable],
        "lambda_min_abs": min(lam_vals) if lam_vals else None,
        "lambda_max_abs": max(lam_vals) if lam_vals else None,
        "certified_route_gate_failures": det_flip,
        "first_n_without_certified_route": blocks_n,
        "labels": [],
    }
    labels = report["verdicts"]["labels"]
    if lam_vals and min(lam_vals) > 0 and not det_flip:
        labels.append("COUPLING-HOLDS on the readable range")
    if det_flip:
        labels.append("COUPLING-COLLAPSES")
    if blocks_n is not None:
        labels.append("CONDITIONING-BLOCKS at n=%d" % blocks_n)
    report["status"] = " / ".join(labels) if labels else "INCONCLUSIVE"

    output = ROOT / "results" / "2028_coupling_scan.json"
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s" % output)
    print(json.dumps({k: report[k] for k in
                      ("status", "verdicts", "decay_constants")}, indent=2))


# decay constants are computed once; the helper records them for reporting
base_c4_last = [None, None, None]


def report_precomputed_decay(seed_transform, seed0, owner, targets, values):
    if base_c4_last[0] is None:
        heights = np.linspace(0.0, 160.0, 321)
        b4 = b2 = c2 = 0.0
        for sigma in (0.0, 0.5, 1.0):
            s = sigma + 1j * heights
            base = owner_probe.cardinal_transform(
                targets, [1.0 + 0j] * len(targets), seed0, s, seed_transform)
            corr = owner_probe.cardinal_transform(
                owner, values, seed0, s, seed_transform)
            scaled = np.abs(heights / (2.0 * math.pi))
            b4 = max(b4, float(np.max(scaled ** 4 * np.abs(base))))
            b2 = max(b2, float(np.max(scaled ** 2 * np.abs(base))))
            c2 = max(c2, float(np.max(scaled ** 2 * np.abs(corr))))
        base_c4_last[:] = [b4, b2, c2]
    return base_c4_last[:]


if __name__ == "__main__":
    main()
