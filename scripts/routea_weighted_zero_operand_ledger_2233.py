"""Record 2233, part 1: operand construction ledger, c and w channels.

Convention A (record 2230) takes the stored binary64 operand tuple as exact.
This script prices the two channels of the ideal-to-stored ledger that can be
bounded from committed data:

  c channel   the q-terminal charge is linear in |c|, so a uniform coefficient
              radius r_c inflates the charge by at most r_c * sum_f T_f /
              charge, with T_f = family charge / |c_f|.  The radius is the
              record-2201 Neumann preflight value (provisional).
  w channel   the charge is linear in |w|, so a relative weight error r_w
              inflates the charge by r_w.  r_w is screened through the GL
              moment identities sum W = 2a, sum W x^2 = 2a^3/3,
              sum W x^4 = 2a^5/5, evaluated in directed MPFR on the stored
              grids.

Writes results/2233_operand_ledger.json.
"""
import ctypes as C
import importlib.util
import json
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
CACHE = R / "2229_operand_cache.npz"

R_BASE_2201 = 1.725905221940381e8
R_CORR_2201 = 3.536472115641207e11


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


m = _load("mpfr2233", "routea_weighted_zero_mpfr_exp_binding_2223.py")
lib = m._lib
M = m.M
RNDD, RNDU = m.RNDD, m.RNDU


def moment_bounds(X, W, exponent):
    """Directed [lo, hi] of sum_j W_j * X_j^exponent (exponent in {0,2,4}).

    GL weights are positive and even powers are nonnegative, so every
    directed product/accumulation below is a valid one-sided bound.
    """
    acc_lo, acc_hi = M(), M()
    t0, t1, t2, t3 = M(), M(), M(), M()
    try:
        lib.mpfr_set_d(C.byref(acc_lo.x), C.c_double(0.0), 0)
        lib.mpfr_set_d(C.byref(acc_hi.x), C.c_double(0.0), 0)
        for x, w in zip(X, W):
            lib.mpfr_set_d(C.byref(t0.x), C.c_double(float(w)), 0)
            if exponent == 0:
                lib.mpfr_add(C.byref(acc_hi.x), C.byref(acc_hi.x),
                             C.byref(t0.x), RNDU)
                lib.mpfr_add(C.byref(acc_lo.x), C.byref(acc_lo.x),
                             C.byref(t0.x), RNDD)
                continue
            lib.mpfr_set_d(C.byref(t1.x), C.c_double(float(x)), 0)
            lib.mpfr_mul(C.byref(t2.x), C.byref(t1.x), C.byref(t1.x), RNDU)
            if exponent == 4:
                lib.mpfr_mul(C.byref(t2.x), C.byref(t2.x), C.byref(t2.x), RNDU)
            lib.mpfr_mul(C.byref(t3.x), C.byref(t0.x), C.byref(t2.x), RNDU)
            lib.mpfr_add(C.byref(acc_hi.x), C.byref(acc_hi.x),
                         C.byref(t3.x), RNDU)
            lib.mpfr_mul(C.byref(t2.x), C.byref(t1.x), C.byref(t1.x), RNDD)
            if exponent == 4:
                lib.mpfr_mul(C.byref(t2.x), C.byref(t2.x), C.byref(t2.x), RNDD)
            lib.mpfr_mul(C.byref(t3.x), C.byref(t0.x), C.byref(t2.x), RNDD)
            lib.mpfr_add(C.byref(acc_lo.x), C.byref(acc_lo.x),
                         C.byref(t3.x), RNDD)
        return acc_lo.get_d(RNDD), acc_hi.get_d(RNDU)
    finally:
        for o in (acc_lo, acc_hi, t0, t1, t2, t3):
            o.clear()


def identity_bounds(a, exponent):
    """Directed [lo, hi] of the exact GL identity values 2a, 2a^3/3, 2a^5/5."""
    t0, t1, t2 = M(), M(), M()
    try:
        div = 1.0 if exponent == 0 else (3.0 if exponent == 2 else 5.0)
        power = 1 if exponent == 0 else (3 if exponent == 2 else 5)
        # lower
        lib.mpfr_set_d(C.byref(t1.x), C.c_double(1.0), 0)
        lib.mpfr_set_d(C.byref(t0.x), C.c_double(a), 0)
        for _ in range(power):
            lib.mpfr_mul(C.byref(t1.x), C.byref(t1.x), C.byref(t0.x), RNDD)
        lib.mpfr_set_d(C.byref(t2.x), C.c_double(2.0), 0)
        lib.mpfr_mul(C.byref(t1.x), C.byref(t2.x), C.byref(t1.x), RNDD)
        lib.mpfr_set_d(C.byref(t2.x), C.c_double(div), 0)
        lib.mpfr_div(C.byref(t1.x), C.byref(t1.x), C.byref(t2.x), RNDD)
        lo = t1.get_d(RNDD)
        # upper
        lib.mpfr_set_d(C.byref(t1.x), C.c_double(1.0), 0)
        lib.mpfr_set_d(C.byref(t0.x), C.c_double(a), 0)
        for _ in range(power):
            lib.mpfr_mul(C.byref(t1.x), C.byref(t1.x), C.byref(t0.x), RNDU)
        lib.mpfr_set_d(C.byref(t2.x), C.c_double(2.0), 0)
        lib.mpfr_mul(C.byref(t1.x), C.byref(t2.x), C.byref(t1.x), RNDU)
        lib.mpfr_set_d(C.byref(t2.x), C.c_double(div), 0)
        lib.mpfr_div(C.byref(t1.x), C.byref(t1.x), C.byref(t2.x), RNDU)
        hi = t1.get_d(RNDU)
        return lo, hi
    finally:
        for o in (t0, t1, t2):
            o.clear()


def main():
    z = np.load(CACHE)
    coeff = z["coeff"]
    fam_a = z["fam_a"].tolist()
    xw = [(z["X"][i], z["W"][i]) for i in range(z["X"].shape[0])]

    node_rows = {}
    for path in sorted(R.glob("2229_q_mpfr_node*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("status") != "MPFR-Q-INTERVAL-NODE-OUTWARD":
            continue
        ni = int(data["scope"]["node_index"])
        rows = data["rows"]
        total = sum(r["gl"] + r["simpson"] for r in rows)
        tsum = 0.0
        for r in rows:
            f = r["family"]
            tsum += (r["gl"] + r["simpson"]) / abs(coeff[f])
        node_rows[ni] = {"charge": total, "t_sum": tsum}
    assert node_rows, "no 2229 node artifacts found"
    worst = max(node_rows, key=lambda i: node_rows[i]["charge"])
    worst_tsum = node_rows[worst]["t_sum"]
    worst_charge = node_rows[worst]["charge"]
    infl_corr = R_CORR_2201 * worst_tsum / worst_charge
    infl_base = R_BASE_2201 * worst_tsum / worst_charge

    moment_rows = []
    for i, (a, (X, W)) in enumerate(zip(fam_a, xw)):
        row = {"family": i, "a": a}
        for exponent in (0, 2, 4):
            lo, hi = moment_bounds(X, W, exponent)
            ilo, ihi = identity_bounds(a, exponent)
            gap = max(ilo - hi, lo - ihi, 0.0)
            scale = max(abs(ilo), abs(ihi))
            row[f"m{exponent}"] = {"sum_lo": lo, "sum_hi": hi,
                                   "identity_lo": ilo, "identity_hi": ihi,
                                   "gap": gap,
                                   "relative_gap": gap / scale if scale else 0.0}
        moment_rows.append(row)
    worst_gap = max(moment_rows, key=lambda r: max(r[f"m{e}"]["relative_gap"]
                                                    for e in (0, 2, 4)))

    result = {
        "record": 2233,
        "part": "c-w-channels",
        "status": "OPERAND-LEDGER-PRICED-C-W-SCREENED",
        "scope": {"families": len(fam_a),
                  "charge_source": "results/2229_q_mpfr_node*.json",
                  "operand_cache_md5_note": "c78a0342fad8ac0166c23d01f653f666"},
        "c_channel": {
            "binding_node": worst,
            "charge": worst_charge,
            "t_sum": worst_tsum,
            "radius_base_2201": R_BASE_2201,
            "radius_corr_2201": R_CORR_2201,
            "inflation_base_labeled": infl_base,
            "inflation_corr_labeled": infl_corr,
            "coeff_abs_min": float(np.min(np.abs(coeff))),
            "coeff_abs_max": float(np.max(np.abs(coeff))),
            "note": "linearity of the charge in |c|; provisional 2201 radii",
        },
        "w_channel": {
            "worst_family": worst_gap["family"],
            "worst_relative_gap": max(worst_gap[f"m{e}"]["relative_gap"]
                                      for e in (0, 2, 4)),
            "rows": moment_rows,
            "note": "GL moment identities screened in directed MPFR; a "
                    "few-ulp weight error is consistent with relative gaps "
                    "at the 1e-15 level",
        },
        "nonclaims": [
            "the c-channel radius is the provisional 2201 Neumann preflight, "
            "not a certified solve enclosure",
            "the w-channel is screened through moment identities, not a "
            "per-weight certificate; the x-channel is priced separately",
            "convention A (stored operands exact) remains the certificate "
            "reference; this ledger prices the ideal-to-stored conversion",
            "no producer or RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_operand_ledger_2233.py",
            "inputs": ["results/2229_operand_cache.npz",
                       "results/2229_q_mpfr_node*.json"],
        },
    }
    out = R / "2233_operand_ledger.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "c_channel": {k: result["c_channel"][k] for k in
                                    ("binding_node", "inflation_corr_labeled",
                                     "inflation_base_labeled",
                                     "coeff_abs_min", "coeff_abs_max")},
                      "w_channel_worst": {"family": worst_gap["family"],
                                          "relative_gap": result["w_channel"]
                                          ["worst_relative_gap"]}},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()