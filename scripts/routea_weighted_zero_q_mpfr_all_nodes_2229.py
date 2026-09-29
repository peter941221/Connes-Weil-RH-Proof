"""Record 2229: all-30-node outward q-interval envelope.

Continuation of 2225/2228.  Same directed MPFR q interval and the same
binary64 evaluation pattern, but the propagated exponent-radius charge

    |c| * |w| * |exp(q + d) - exp(q)|,   |d| <= q-radius

is computed and accumulated with MPFR directed-upward rounding (mpfr_exp /
mpfr_mul / mpfr_add with RNDU) instead of binary64 nearest-rounding
arithmetic, so each reported per-node charge is an upper bound of the
mathematical charge under the discrete-defined operand convention (the
binary64 operands K, a, theta, node, x, c, w are exact; record 2230 states
the convention).  Exponential bound: 2*delta*exp(qr) for delta < 1 (the
Lean 2212/2213 form) and exp(delta)*exp(qr) otherwise (all-delta form);
delta is the nextafter-up sum of the two component radii, and the Simpson
panel factor (hi-lo)/(2*NSEG)/3 is inflated by 4 binary64 steps before the
directed products.

Modes (environment):
  NODE_INDEX=<i>   evaluate one node, write results/2229_q_mpfr_node<i>.json
  MODE=collect     aggregate results/2229_q_mpfr_node*.json into
                   results/2229_q_mpfr_all_nodes.json
  SMOKE_FAMILIES=<k>  optional smoke limiter (first k families, status flag)

Every per-node artifact carries status MPFR-Q-INTERVAL-NODE-OUTWARD; smoke
artifacts carry the SMOKE suffix and are not certificate evidence.
"""
import ctypes as C
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


q = _load("q2225", "routea_weighted_zero_q_mpfr_interval_binding_2225.py")
m = q.m
parent = q.parent
lib = m._lib
RNDU = m.RNDU

NSEG, NPAN = 1100, 12
NODE_COUNT = 30
CACHE = ROOT / "results" / "2229_operand_cache.npz"
UP = lambda v: math.nextafter(v, math.inf)


def load_operands(force_build=False):
    """Return (nodes, coeff, fam, xw) from the pinned operand cache.

    The node list, the coefficient solve, and the GL grids depend only on
    the owner construction, not on the node index, so they are built once
    and reused by every node worker.  The cache file pins the exact binary64
    operands under the discrete-defined convention (record 2230); its md5
    is recorded in the run artifacts.  The build is single-threaded and
    deterministic given the committed script."""
    if CACHE.exists() and not force_build:
        z = np.load(CACHE)
        nodes = z["nodes"]
        coeff = z["coeff"]
        fam = list(zip(z["fam_a"].tolist(), z["fam_theta"].tolist()))
        xw = [(z["X"][i], z["W"][i]) for i in range(z["X"].shape[0])]
        return nodes, coeff, fam, xw
    nodes, fam, A0, _b, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
    coeff = np.linalg.solve(A0, b_corr)
    xw = [parent.v.q.r.r59.phi_weights(a, panels=6, m=parent.M)
          for a, _ in fam]
    np.savez(CACHE,
             nodes=np.asarray(nodes, dtype=complex),
             coeff=np.asarray(coeff, dtype=complex),
             fam_a=np.asarray([a for a, _ in fam], dtype=float),
             fam_theta=np.asarray([t for _, t in fam], dtype=float),
             X=np.stack([X for X, _ in xw]),
             W=np.stack([W for _, W in xw]))
    return nodes, coeff, fam, xw


def _md5(path):
    import hashlib
    return hashlib.md5(path.read_bytes()).hexdigest()


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def charge_term(cabs, wabs, qr, delta, work):
    """MPFR-RNDU upper bound of |c||w| * |exp(qr+d) - exp(qr)|, |d| <= delta.

    work = [tmp0, tmp1]; returns the MPFR object tmp1 holding the bound, or
    None when delta == 0.0 (degenerate exact center)."""
    if delta == 0.0:
        return None
    t0, t1 = work
    lib.mpfr_set_d(C.byref(t0.x), C.c_double(qr), 0)
    lib.mpfr_exp(C.byref(t1.x), C.byref(t0.x), RNDU)
    if delta < 1.0:
        lib.mpfr_set_d(C.byref(t0.x), C.c_double(2.0 * delta), 0)
    else:
        lib.mpfr_set_d(C.byref(t0.x), C.c_double(delta), 0)
        lib.mpfr_exp(C.byref(t0.x), C.byref(t0.x), RNDU)
    lib.mpfr_mul(C.byref(t1.x), C.byref(t1.x), C.byref(t0.x), RNDU)
    lib.mpfr_set_d(C.byref(t0.x), C.c_double(cabs), 0)
    lib.mpfr_mul(C.byref(t1.x), C.byref(t1.x), C.byref(t0.x), RNDU)
    lib.mpfr_set_d(C.byref(t0.x), C.c_double(wabs), 0)
    lib.mpfr_mul(C.byref(t1.x), C.byref(t1.x), C.byref(t0.x), RNDU)
    return t1


def add_into(acc, term):
    if term is None:
        return
    lib.mpfr_add(C.byref(acc.x), C.byref(acc.x), C.byref(term.x), RNDU)


def evaluate_node(ni, smoke_families=None):
    nodes, coeff, fam, xw = load_operands()
    node = nodes[ni]
    K = parent.v.q.r.K
    DELTA = parent.DELTA
    if smoke_families is not None:
        fam = fam[:smoke_families]
        xw = xw[:smoke_families]
        coeff = coeff[:smoke_families]
    qscratch = [m.M(), m.M(), m.M()]
    work = [m.M(), m.M()]
    acc_gl, acc_sim = m.M(), m.M()
    total = 0.0
    terms = failures = 0
    max_rr = max_ri = max_delta = 0.0
    rows = []
    try:
        for fi, (c, (a, theta), (X, W)) in enumerate(zip(coeff, fam, xw)):
            z = a * (node + 1j * theta)
            cabs = abs(c)
            lib.mpfr_set_d(C.byref(acc_gl.x), C.c_double(0.0), 0)
            lib.mpfr_set_d(C.byref(acc_sim.x), C.c_double(0.0), 0)
            for x, w in zip(X, W):
                qv = -K / (1.0 - (x / a) ** 2) + z * x
                qr, qi = float(np.real(qv)), float(np.imag(qv))
                ir, ii = q.q_interval(K, a, theta, node, float(x), qscratch)
                rr = q.radius(ir, qr)
                ri = q.radius(ii, qi)
                failures += not (ir[0] <= qr <= ir[1] and ii[0] <= qi <= ii[1])
                delta = UP(rr + ri)
                max_rr = max(max_rr, rr)
                max_ri = max(max_ri, ri)
                max_delta = max(max_delta, delta)
                add_into(acc_gl, charge_term(cabs, abs(float(w)), qr, delta, work))
            lo_all, hi_all = -a * (1.0 - DELTA), a * (1.0 - DELTA)
            for panel in range(NPAN):
                lo = lo_all + (hi_all - lo_all) * panel / NPAN
                hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
                xx = np.linspace(lo, hi, 2 * NSEG + 1)
                hh3 = up_many((hi - lo) / (2 * NSEG) / 3.0, 4)
                pf = UP(cabs * hh3)
                weights = np.ones(len(xx))
                weights[1:-1:2] = 4.0
                weights[2:-1:2] = 2.0
                for x, weight in zip(xx, weights):
                    qv = -K / (1.0 - (x / a) ** 2) + z * x
                    qr, qi = float(np.real(qv)), float(np.imag(qv))
                    ir, ii = q.q_interval(K, a, theta, node, float(x), qscratch)
                    rr = q.radius(ir, qr)
                    ri = q.radius(ii, qi)
                    failures += not (ir[0] <= qr <= ir[1] and ii[0] <= qi <= ii[1])
                    delta = UP(rr + ri)
                    max_rr = max(max_rr, rr)
                    max_ri = max(max_ri, ri)
                    max_delta = max(max_delta, delta)
                    add_into(acc_sim,
                             charge_term(pf, float(weight), qr, delta, work))
            gl = acc_gl.get_d(RNDU)
            sim = acc_sim.get_d(RNDU)
            total = UP(total + gl + sim)
            terms += len(X) + NPAN * (2 * NSEG + 1)
            fam_total = UP(gl + sim)
            rows.append({"family": fi, "gl": gl, "simpson": sim,
                         "total": fam_total})
            print(f"family={fi} total={fam_total:.17e}", flush=True)
    finally:
        for obj in qscratch + work + [acc_gl, acc_sim]:
            obj.clear()
    smoke = smoke_families is not None
    result = {
        "record": 2229,
        "status": ("MPFR-Q-INTERVAL-NODE-OUTWARD-SMOKE" if smoke
                   else "MPFR-Q-INTERVAL-NODE-OUTWARD"),
        "backend": {"library": "libmpfr.so.6", "precision_bits": m.PREC,
                    "rounding": "RNDD/RNDU; charge accumulation RNDU",
                    "charge_backend": "mpfr_exp/mpfr_mul/mpfr_add RNDU"},
        "scope": {"node_index": ni, "families": len(fam), "NSEG": NSEG,
                  "panels": NPAN, "terms": terms,
                  "smoke_families": smoke_families},
        "q_interval": {"operation": "directed MPFR scalar interval (2225)",
                       "failures": failures,
                       "max_real_radius": max_rr,
                       "max_imag_radius": max_ri,
                       "max_delta": max_delta},
        "exp_lipschitz_charge": total,
        "rows": rows,
        "outward": {
            "delta": "nextafter-up of rr + ri",
            "exponential": "2*delta*exp(qr) for delta<1; exp(delta)*exp(qr) else",
            "panel_factor": "4-step up-inflation of (hi-lo)/(2*NSEG)/3",
            "accumulation": "per-term MPFR RNDU into family accumulators",
        },
        "nonclaims": [
            "binary64 operands are taken as exact (discrete-defined "
            "convention; record 2230)",
            "family totals are combined in binary64 with upward inflation; "
            "the per-term chain is MPFR RNDU",
            "complete-owner transfer and the signed producer margin "
            "remain open; no RH claim",
        ],
        "provenance": {
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
            "predecessor": "2225/2228 binding-node evaluator",
            "theorem_interface": "2212/2213 exp perturbation bound",
            "operand_cache": {
                "path": "results/2229_operand_cache.npz",
                "md5": _md5(CACHE) if CACHE.exists() else None,
            },
        },
    }
    return result


def collect():
    results_dir = ROOT / "results"
    per = {}
    for path in sorted(results_dir.glob("2229_q_mpfr_node*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if not data.get("status", "").endswith(("-OUTWARD",)):
            continue
        per[int(data["scope"]["node_index"])] = data
    missing = [i for i in range(NODE_COUNT) if i not in per]
    charges = {i: per[i]["exp_lipschitz_charge"] for i in sorted(per)}
    worst = max(charges, key=charges.get) if charges else None
    total_failures = sum(per[i]["q_interval"]["failures"] for i in per)
    summary = {
        "record": 2229,
        "status": "MPFR-Q-INTERVAL-ALL-NODE-OUTWARD",
        "backend": per[worst]["backend"] if worst is not None else None,
        "scope": {"nodes_present": len(per), "expected_nodes": NODE_COUNT,
                  "missing": missing, "families": 30, "NSEG": NSEG,
                  "panels": NPAN, "terms_per_node": 1944360},
        "charges": charges,
        "worst_node": worst,
        "max_charge": charges[worst] if worst is not None else None,
        "min_charge": min(charges.values()) if charges else None,
        "total_failures": total_failures,
        "operand_cache": {
            "path": "results/2229_operand_cache.npz",
            "md5": _md5(CACHE) if CACHE.exists() else None,
        },
        "nonclaims": [
            "all-node outward envelope only; complete-owner transfer and "
            "the signed producer margin remain open; no RH claim",
        ],
    }
    out = results_dir / "2229_q_mpfr_all_nodes.json"
    out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: summary[k] for k in
                      ("status", "worst_node", "max_charge", "min_charge",
                       "scope", "total_failures")}, indent=2), flush=True)
    return summary


def main():
    mode = os.environ.get("MODE", "node" if "NODE_INDEX" in os.environ else "collect")
    if mode == "collect":
        collect()
        return
    if mode == "build":
        load_operands(force_build=True)
        print(json.dumps({"mode": "build",
                          "cache": os.fspath(CACHE.relative_to(ROOT)),
                          "md5": _md5(CACHE),
                          "size_bytes": CACHE.stat().st_size}, indent=2),
              flush=True)
        return
    ni = int(os.environ["NODE_INDEX"])
    smoke = os.environ.get("SMOKE_FAMILIES")
    result = evaluate_node(ni, int(smoke) if smoke else None)
    out = ROOT / "results" / os.environ.get(
        "Q_OUT", f"2229_q_mpfr_node{ni}.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"record": 2229, "status": result["status"],
                      "node_index": ni, "failures": result["q_interval"]["failures"],
                      "exp_lipschitz_charge": result["exp_lipschitz_charge"],
                      "max_delta": result["q_interval"]["max_delta"]},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()