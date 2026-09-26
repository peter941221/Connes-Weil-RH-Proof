#!/usr/bin/env python3
"""Record 2015: the resolution-convergence ladder.

Pre-registered in docs/proofs/2015_resolution_ladder_preregistration.md
(committed before this run).  Four owners of the record-2011 cone layer, the
committed selector only (rank 0, sigma = 0), at dxi = 0.008, 0.004, 0.002,
0.001: sixteen rows.  The owner construction is imported from
`routea_ahd_dual_2011` (which imports `routea_health_cone_2006`), so the
dxi = 0.008 rows are the same code path as the record-2011 anchors and L1 can
require equality rather than a band.

No theorem, no Lean brick, no RH claim.
"""

import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402
import routea_ahd_dual_2011 as r11  # noqa: E402
import routea_health_cone_2006 as r06  # noqa: E402

T0 = time.time()
CASES = [
    (0.10, r94.G5, 0.92, "G5-H"),
    (0.10, r94.G5, 0.90, "G5-W"),
    (0.10, r94.G7, 0.92, "G7-H"),
    (0.10, r94.G8, 0.88, "G8-H"),
]
DXI_LADDER = (0.008, 0.004, 0.002, 0.001)
PAIRS = ((0.008, 0.004), (0.004, 0.002), (0.002, 0.001))
FINEST = 0.001
L1_BAR = 1.0e-9
L2_BAR = 1.0e-9
IDENT_VAR_BAR = 5.0e-3
IDENT_ALG_BAR = 1.0e-9
SH_BAR = 0.7
FLOOR_BAR = 1.0
R_ATTAINED = 0.5
R_SLACK = 0.1
# Record 2014 section 5 lower bounds on eps(0.008, 0.004), per owner.
BAND_LO = {"G5-H": 3.64e-07, "G5-W": 2.60e-07, "G7-H": 6.17e-06,
           "G8-H": 6.91e-06}
BAND_HI_FACTOR = 100.0
# Committed anchors for L1 (record-2011 / record-2006 cone layer, dxi = 0.008)
# and L2 (record-2004, results/2003_route_a_health_selector.json, dxi = 0.004).
ANCHOR_L1 = {
    "G5-H": (+1.49089499804813386e+00, -6.30752072626298047e+12),
    "G5-W": (+2.50171187903106329e-01, -2.25136825561206312e+14),
    "G7-H": (+1.73154001136437728e+02, -2.03596080584510210e+20),
    "G8-H": (+6.64107474896016356e+02, -1.11126519153653187e+20),
}
ANCHOR_L2 = {
    "G5-H": (+1.494812e+00, -6.307381e+12),
    "G5-W": (+2.559099e-01, -2.251357e+14),
    "G7-H": (+1.732980e+02, -2.035919e+20),
    "G8-H": (+6.643519e+02, -1.111262e+20),
}
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def log(message):
    print("[%7.1fs] %s" % (time.time() - T0, message), flush=True)


def measure_at(env, dxi):
    """One sigma = 0 row at one resolution, the record-2011 anchor call."""
    saved = r06.DXI
    r06.DXI = dxi
    try:
        return r06.measure(env["nodes"], env["values"], env["rho"], env["delta"],
                           env["fam"], env["xw"], env["base"], env["corr"],
                           env["cond"], 0, 0.0)
    finally:
        r06.DXI = saved


def mass_of(row):
    ident = row.get("identity") or {}
    mp, mm = ident.get("mp"), ident.get("mm")
    if mp is None or mm is None:
        return None
    return float(mp), float(mm)


def rel(a, b):
    """Relative deviation of a from b (b is the reference)."""
    if b == 0.0:
        return float("inf")
    return abs(a - b) / abs(b)


def pair_reading(rows, owner, coarse, fine):
    """eps, C offset and the amplification fraction for one (owner, pair)."""
    a, b = rows[coarse], rows[fine]
    ma, mb = mass_of(a), mass_of(b)
    ident_b = b.get("identity") or {}
    f_ref = ident_b.get("f")
    out = {"owner": owner, "coarse": coarse, "fine": fine,
           "eps": None, "C_offset": None, "D_offset": None, "r": None,
           "f_ref": f_ref}
    out["C_offset"] = rel(a["C"], b["C"])
    out["D_offset"] = rel(a["D"], b["D"])
    if ma is None or mb is None:
        return out
    eps = max(rel(ma[0], mb[0]), rel(ma[1], mb[1]))
    out["eps"] = eps
    if f_ref is not None and eps > 0.0:
        out["r"] = out["C_offset"] / (eps * abs(2.0 + f_ref))
    out["amp"] = abs(2.0 + f_ref) if f_ref is not None else None
    return out


def row_check(row, tag, dxi):
    ident = row.get("identity") or {}
    check = {
        "owner": tag, "dxi": dxi, "certified": bool(row["certified"]),
        "finite": bool(row["finite"]),
        "three_routes": bool(set(("Ap", "B")) <= set(row["routes"])),
        "pins_ok": bool(row["pin_err_base"] <= 1e-6
                        and row["pin_err_corr"] <= 1e-6),
        "cond_ok": bool(row["cond"] <= 1e8),
        "spread_D_ok": bool(row["spread_D"] < 1.0 / 3.0),
        "identity_ok": bool(ident
                            and ident.get("dev_var", 1.0) <= IDENT_VAR_BAR
                            and ident.get("dev_alg", 1.0) <= IDENT_ALG_BAR),
        "mass_present": mass_of(row) is not None,
        "n_primes": row["n_primes"], "routes": row["routes"],
    }
    check["pass"] = bool(check["certified"] and check["three_routes"]
                         and check["pins_ok"] and check["cond_ok"]
                         and check["spread_D_ok"] and check["identity_ok"]
                         and check["mass_present"])
    return check


def anchor_check(tag, row, table, bar):
    ref = table.get(tag)
    if ref is None:
        return None
    dev_C = rel(row["C"], ref[0])
    dev_D = rel(row["D"], ref[1])
    return {"ref_C": ref[0], "ref_D": ref[1], "dev_C": dev_C, "dev_D": dev_D,
            "pass": bool(dev_C <= bar and dev_D <= bar)}


def main():
    log("record 2015 - resolution-convergence ladder (pre-reg 2015)")
    records = []
    for delta, gamma, scale, tag in CASES:
        log("owner %s (delta %.2f gamma %.4f scale %.2f)" % (tag, delta, gamma,
                                                            scale))
        env = r11.setup_case(delta, gamma, scale, tag)
        rows = {}
        for dxi in DXI_LADDER:
            row = measure_at(env, dxi)
            rows[dxi] = row
            ident = row.get("identity") or {}
            log("  dxi=%.3f C=%+.10e D=%+.10e det=%+.6e f=%s mp=%s mm=%s "
                "sD=%.1e np=%s cert=%s"
                % (dxi, row["C"], row["D"], row["det"],
                   "%.6g" % ident["f"] if ident.get("f") is not None else None,
                   "%.10e" % ident["mp"] if ident.get("mp") is not None
                   else None,
                   "%.10e" % ident["mm"] if ident.get("mm") is not None
                   else None,
                   row["spread_D"], row["n_primes"], row["certified"]))
        pairs = [pair_reading(rows, tag, c, f) for c, f in PAIRS]
        for p in pairs:
            log("  pair %s->%s eps=%s C_off=%s D_off=%s r=%s"
                % (p["coarse"], p["fine"],
                   "%.6e" % p["eps"] if p["eps"] is not None else None,
                   "%.6e" % p["C_offset"], "%.6e" % p["D_offset"],
                   "%.4f" % p["r"] if p["r"] is not None else None))
        checks = [row_check(rows[dxi], tag, dxi) for dxi in DXI_LADDER]
        l1 = anchor_check(tag, rows[0.008], ANCHOR_L1, L1_BAR)
        l2 = anchor_check(tag, rows[0.004], ANCHOR_L2, L2_BAR)
        if l1 is None or l2 is None:
            raise RuntimeError("anchor table missing registered tag %s" % tag)
        log("  L1 dev_C=%.2e dev_D=%.2e pass=%s | L2 dev_C=%.2e dev_D=%.2e "
            "pass=%s"
            % (l1["dev_C"], l1["dev_D"], l1["pass"], l2["dev_C"], l2["dev_D"],
               l2["pass"]))
        records.append({
            "tag": tag, "delta": delta, "gamma": gamma, "scale": scale,
            "basis_size": env["basis_size"], "cond": env["cond"],
            "nullity": env["nullity"], "e_ref": env["e_ref"],
            "rows": {("%.4f" % dxi): rows[dxi] for dxi in DXI_LADDER},
            "pairs": pairs, "row_checks": checks, "L1": l1, "L2": l2,
        })
        partial = os.path.join(REPO, "results",
                               "2015_resolution_ladder_partial.json")
        with open(partial, "w", encoding="utf-8") as stream:
            json.dump({"record": "2015", "status": "PARTIAL", "owners": records},
                      stream, indent=2)
            stream.write("\n")

    # ------------------------------------------------------------ verdicts
    all_checks_ok = all(c["pass"] for rec in records for c in rec["row_checks"])
    l1_ok = all(rec["L1"] and rec["L1"]["pass"] for rec in records)
    l2_ok = all(rec["L2"] and rec["L2"]["pass"] for rec in records)

    shrinkage, orders = {}, {}
    for rec in records:
        tag = rec["tag"]
        by_pair = {("%.4f" % p["coarse"], "%.4f" % p["fine"]): p
                   for p in rec["pairs"]}
        e1 = by_pair[("0.0080", "0.0040")]["eps"]
        e2 = by_pair[("0.0040", "0.0020")]["eps"]
        e3 = by_pair[("0.0020", "0.0010")]["eps"]
        shrinkage[tag] = (e3 / e2) if (e2 and e3) else None
        orders[tag] = (math.log(e1 / e2) / math.log(2.0)
                       if (e1 and e2 and e1 > 0.0 and e2 > 0.0) else None)
    if not (all_checks_ok and l1_ok and l2_ok):
        mass_verdict = "INSTRUMENT-FAIL"
    else:
        monotone = {}
        for rec in records:
            tag = rec["tag"]
            by_pair = {("%.4f" % p["coarse"], "%.4f" % p["fine"]): p["eps"]
                       for p in rec["pairs"]}
            monotone[tag] = bool(by_pair[("0.0080", "0.0040")]
                                 > by_pair[("0.0040", "0.0020")]
                                 > by_pair[("0.0020", "0.0010")])
        n_conv = sum(1 for tag in shrinkage
                     if monotone[tag] and shrinkage[tag] is not None
                     and shrinkage[tag] <= SH_BAR)
        n_floor = sum(1 for tag in shrinkage
                      if shrinkage[tag] is not None
                      and shrinkage[tag] >= FLOOR_BAR)
        if n_floor >= 2:
            mass_verdict = "LADDER-FLOOR"
        elif n_conv >= 3:
            mass_verdict = "LADDER-CONVERGED"
        else:
            mass_verdict = "LADDER-MIXED"

    rvals = [p["r"] for rec in records for p in rec["pairs"]
             if p["r"] is not None]
    n_pairs = len([p for rec in records for p in rec["pairs"]])
    if len(rvals) < n_pairs:
        amp_verdict = "AMP-UNDEFINED"
    elif sum(1 for v in rvals if v >= R_ATTAINED) >= 8:
        amp_verdict = "AMP-ATTAINED"
    elif sum(1 for v in rvals if v <= R_SLACK) >= 10:
        amp_verdict = "AMP-SLACK"
    else:
        amp_verdict = "AMP-MIXED"

    band = {}
    for rec in records:
        tag = rec["tag"]
        eps1 = rec["pairs"][0]["eps"]
        lo, hi = BAND_LO.get(tag), None
        if lo:
            hi = lo * BAND_HI_FACTOR
        band[tag] = {"eps_0.008_0.004": eps1, "lo": lo, "hi": hi,
                     "in_band": bool(eps1 is not None and lo is not None
                                     and lo <= eps1 <= hi)}
    band_verdict = ("LADDER-BAND-CONFIRMED"
                    if all(v["in_band"] for v in band.values())
                    else "LADDER-BAND-OUT")
    verdict = "/".join((mass_verdict, amp_verdict, band_verdict))

    log("=" * 96)
    for rec in records:
        tag = rec["tag"]
        log("  %s L1=%s L2=%s rows=%s | sh=%s order=%s"
            % (tag, rec["L1"]["pass"], rec["L2"]["pass"],
               all(c["pass"] for c in rec["row_checks"]),
               "%.4f" % shrinkage[tag] if shrinkage[tag] is not None else None,
               "%.3f" % orders[tag] if orders[tag] is not None else None))
    log("r values: %s" % ["%.3f" % v for v in rvals])
    log("band: %s" % json.dumps(band))
    log("VERDICT: %s" % verdict)

    out = os.path.join(REPO, "results", "2015_resolution_ladder.json")
    with open(out, "w", encoding="utf-8") as stream:
        json.dump({"record": "2015", "verdict": verdict,
                   "dxi_ladder": list(DXI_LADDER), "pairs": [list(p) for p in
                                                             PAIRS],
                   "mass_verdict": mass_verdict, "amp_verdict": amp_verdict,
                   "band_verdict": band_verdict,
                   "shrinkage": shrinkage, "orders": orders, "band": band,
                   "r_values": rvals,
                   "owners": records}, stream, indent=2)
        stream.write("\n")
    log("results -> %s" % out)


if __name__ == "__main__":
    main()