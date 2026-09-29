"""Record 2233, part 2: x-channel charge sensitivity.

Convention A (record 2230) takes the stored binary64 operand tuple as exact,
including the 38400 GL/Simpson x nodes per family.  This part prices the
last construction channel: an ideal x differing from the stored x by k ulps
(k in {1, 16}) shifts q by

    |dq| <= |dq/dx| * d_k + (1/2) |q''| * d_k^2,   d_k = k * 2^-52 * |x|,

so the per-term charge is re-evaluated at the widened exponent radius
delta_k = nextafter-up(rr + ri + extra_k) and accumulated with MPFR RNDU on
both the GL grid and the Simpson panels of the two sampled nodes (2 =
binding charge, 1 = minimum charge).  The base radius is recomputed on the
same path as a drift control against the committed 2229 rows.

Modes (environment):
  MODE=node NODE_INDEX=i FAMILY_LO=f FAMILY_HI=g
      evaluate families [f, g) of node i -> results/2233x_node<i>_fam<f>_<g>.json
  MODE=reduce NODES=2,1
      aggregate one node over its family chunks -> results/2233_xwidth_charge.json
"""
import ctypes as C
import importlib.util
import json
import math
import os
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
LEVELS = (1, 16)


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


n29 = _load("n29x", "routea_weighted_zero_q_mpfr_all_nodes_2229.py")
q = n29.q
m = n29.m
lib = n29.lib
RNDU = m.RNDU
UP = n29.UP
K = n29.parent.v.q.r.K
DELTA = n29.parent.DELTA
NSEG, NPAN = n29.NSEG, n29.NPAN


def deriv_bounds(a, x, zabs):
    """Upper bounds (binary64, up-inflated) on |dq/dx| and |q''| at x."""
    u = x / a
    q0 = 1.0 - u * u
    if q0 <= 0.0:
        return None
    inv2 = 1.0 / (q0 * q0)
    d1 = UP(UP(2.0 * K * abs(x) / (a * a) * inv2) + zabs)
    d2 = UP(2.0 * K / (a * a) * UP(inv2 + 4.0 * u * u * inv2 / q0))
    return d1, d2


def extra_shift(d1, d2, x, k):
    """nextafter-up of |dq/dx| d_k + 0.5 |q''| d_k^2, d_k = k 2^-52 |x|."""
    dk = n29.up_many(k * 2.0 ** -52 * abs(x), 5)
    lin = UP(d1 * dk)
    quad = UP(UP(0.5 * d2) * UP(dk * dk))
    return UP(lin + quad)


def family_node(ni, fl, fam, coeff, xw, nodes, work, qscratch, accs):
    """Charge rows for families [fl, fl+len(xw)) at node ni on all levels.

    accs = dict level -> [gl, sim] MPFR accumulators; level 0 is the base
    (committed-radius) path.  Returns the per-family row."""
    node = nodes[ni]
    row = {"family": fl}
    max_delta = {0: 0.0, 1: 0.0, 16: 0.0}
    for level, (acc_gl, acc_sim) in accs.items():
        lib.mpfr_set_d(C.byref(acc_gl.x), C.c_double(0.0), 0)
        lib.mpfr_set_d(C.byref(acc_sim.x), C.c_double(0.0), 0)
    a, theta = fam[fl]
    c = coeff[fl]
    X, W = xw[fl]
    z = a * (node + 1j * theta)
    zabs = abs(z)
    cabs = abs(c)
    for x, w in zip(X, W):
        x = float(x)
        qv = -K / (1.0 - (x / a) ** 2) + z * x
        qr, qi = float(np.real(qv)), float(np.imag(qv))
        ir, ii = q.q_interval(K, a, theta, node, x, qscratch)
        rr = q.radius(ir, qr)
        ri = q.radius(ii, qi)
        base = UP(rr + ri)
        db = deriv_bounds(a, x, zabs)
        assert db is not None, ("x outside support", ni, fl, x, a)
        d1, d2 = db
        wabs = abs(float(w))
        deltas = {0: base}
        for level in LEVELS:
            deltas[level] = UP(base + extra_shift(d1, d2, x, level))
        for level in (0,) + LEVELS:
            d = deltas[level]
            max_delta[level] = max(max_delta[level], d)
            n29.add_into(accs[level][0],
                         n29.charge_term(cabs, wabs, qr, d, work))
    lo_all, hi_all = -a * (1.0 - DELTA), a * (1.0 - DELTA)
    for panel in range(NPAN):
        lo = lo_all + (hi_all - lo_all) * panel / NPAN
        hi = lo_all + (hi_all - lo_all) * (panel + 1) / NPAN
        xx = np.linspace(lo, hi, 2 * NSEG + 1)
        hh3 = n29.up_many((hi - lo) / (2 * NSEG) / 3.0, 4)
        pf = UP(cabs * hh3)
        weights = np.ones(len(xx))
        weights[1:-1:2] = 4.0
        weights[2:-1:2] = 2.0
        for x, weight in zip(xx, weights):
            x = float(x)
            qv = -K / (1.0 - (x / a) ** 2) + z * x
            qr, qi = float(np.real(qv)), float(np.imag(qv))
            ir, ii = q.q_interval(K, a, theta, node, x, qscratch)
            rr = q.radius(ir, qr)
            ri = q.radius(ii, qi)
            base = UP(rr + ri)
            db = deriv_bounds(a, x, zabs)
            assert db is not None, ("x outside support", ni, fl, x, a)
            d1, d2 = db
            wabs = abs(float(weight))
            deltas = {0: base}
            for level in LEVELS:
                deltas[level] = UP(base + extra_shift(d1, d2, x, level))
            for level in (0,) + LEVELS:
                d = deltas[level]
                max_delta[level] = max(max_delta[level], d)
                n29.add_into(accs[level][1],
                             n29.charge_term(pf, wabs, qr, d, work))
    for level, (acc_gl, acc_sim) in accs.items():
        gl = acc_gl.get_d(RNDU)
        sim = acc_sim.get_d(RNDU)
        tag = "base" if level == 0 else f"k{level}"
        row[f"gl_{tag}"] = gl
        row[f"sim_{tag}"] = sim
        row[f"total_{tag}"] = n29.up_many(gl + sim, 3)
        row[f"max_delta_{tag}"] = max_delta[level]
    return row


def node_worker(ni, fl, fh):
    nodes, coeff, fam, xw = n29.load_operands()
    work = [m.M(), m.M()]
    qscratch = [m.M(), m.M(), m.M()]
    accs = {level: [m.M(), m.M()] for level in (0,) + LEVELS}
    rows = []
    try:
        for fi in range(fl, fh):
            rows.append(family_node(ni, fi, fam, coeff, xw, nodes,
                                    work, qscratch, accs))
    finally:
        for pair in accs.values():
            for o in pair:
                o.clear()
        for o in work + qscratch:
            o.clear()
    out = {"record": 2233, "part": "x-channel", "mode": "node",
           "status": "XWIDTH-CHANNEL-SAMPLED", "node_index": ni,
           "family_lo": fl, "family_hi": fh, "levels": list(LEVELS),
           "rows": rows}
    path = R / f"2233x_node{ni}_fam{fl}_{fh}.json"
    path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"node": ni, "families": [fl, fh],
                      "fam_total_base": rows[-1]["total_base"],
                      "fam_total_k16": rows[-1]["total_k16"]}), flush=True)


def reduce_worker(nodes_list):
    per_node = {}
    for ni in nodes_list:
        rows = []
        for path in sorted(R.glob(f"2233x_node{ni}_fam*.json")):
            rows.extend(json.loads(path.read_text(encoding="utf-8"))["rows"])
        rows.sort(key=lambda r: r["family"])
        assert len(rows) == 30, (ni, len(rows))
        totals = {}
        for tag in ("base", "k1", "k16"):
            t = 0.0
            for r in rows:
                t = n29.up_many(t + r[f"gl_{tag}"] + r[f"sim_{tag}"], 1)
            totals[tag] = t
        committed = None
        cpath = R / f"2229_q_mpfr_node{ni}.json"
        if cpath.exists():
            committed = json.loads(cpath.read_text(encoding="utf-8"))[
                "exp_lipschitz_charge"]
        max_delta = {tag: max(r[f"max_delta_{tag}"] for r in rows)
                     for tag in ("base", "k1", "k16")}
        per_node[str(ni)] = {
            "totals": totals,
            "committed_2229": committed,
            "base_relative_drift": ((totals["base"] - committed) / committed
                                    if committed else None),
            "inflation_k1": totals["k1"] / totals["base"] - 1.0,
            "inflation_k16": totals["k16"] / totals["base"] - 1.0,
            "max_delta": max_delta,
        }
    worst = max(per_node, key=lambda i: per_node[i]["inflation_k1"])
    result = {
        "record": 2233,
        "part": "x-channel",
        "status": "XWIDTH-CHARGE-MEASURED",
        "model": {
            "delta_k": "k * 2^-52 * |x|, one and sixteen ulps of the stored "
                       "binary64 x node",
            "shift": "|dq| <= |dq/dx| d_k + (1/2)|q''| d_k^2 with analytic "
                     "d1 = 2K|x|/a^2 (1-u^2)^-2 + |z|, "
                     "d2 = (2K/a^2)((1-u^2)^-2 + 4u^2 (1-u^2)^-3)",
            "charge": "re-evaluated at nextafter-up(rr + ri + extra) with "
                      "MPFR RNDU accumulation",
        },
        "per_node": per_node,
        "worst_node_k1": int(worst),
        "nonclaims": [
            "the GL/Simpson nodes are taken from the stored binary64 grids; "
            "k ulps is a stated model of their generation error, not a "
            "certified bound on it",
            "two nodes sampled (binding charge and minimum charge), not all "
            "30",
            "convention A (stored operands exact) remains the certificate "
            "reference",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_xwidth_charge_2233.py",
            "charge_backend": "scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py",
        },
    }
    out = R / "2233_xwidth_charge.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "worst_node_k1": int(worst),
                      "per_node": {k: {"inflation_k1": v["inflation_k1"],
                                       "inflation_k16": v["inflation_k16"],
                                       "base_relative_drift":
                                       v["base_relative_drift"]}
                                   for k, v in per_node.items()}},
                     indent=2), flush=True)


def main():
    mode = os.environ.get("MODE", "reduce")
    if mode == "node":
        ni = int(os.environ["NODE_INDEX"])
        fl = int(os.environ["FAMILY_LO"])
        fh = int(os.environ["FAMILY_HI"])
        node_worker(ni, fl, fh)
    elif mode == "reduce":
        nodes_list = [int(t) for t in
                      os.environ.get("NODES", "2,1").split(",")]
        reduce_worker(nodes_list)
    else:
        raise SystemExit(f"unknown MODE={mode}")


if __name__ == "__main__":
    main()