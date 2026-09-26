#!/usr/bin/env python3
"""Record 2006 calibration helper: resolution ladder of the anchor row.

Measures the committed anchor row (G5-H and G7-H) of record 2006 at
dxi in {0.004, 0.008, 0.016} and reports the relative deviation of the
gate entries against the record-2003 anchors, together with the two
determinant forms used by the record-1919 identity check.

This is instrument calibration for the registered checks I1 and I3 of
record 2006; it is not the registered measurement.
"""

import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routea_opposite_gates_height_1994 as r94  # noqa: E402
import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59  # noqa: E402
import routea_health_cone_2006 as h06  # noqa: E402

CASES = [(r94.G5, 0.92, "G5-H"), (r94.G5, 0.90, "G5-W"),
         (r94.G7, 0.92, "G7-H"), (r94.G8, 0.88, "G8-H")]
DXIS = (0.004, 0.008, 0.016)


def anchor_row(delta, gamma, scale, dxi):
    h06.DXI = dxi
    rho = (0.5 + delta) + 1j * gamma
    nodes, values = r94.owner_nodes_ext(rho, gamma)
    fam, base_fam = h06.two_copy_family(nodes, scale, gamma)
    xw = r80.family_quad(fam, h06.K)
    base_ref, corr_ref, amp_info = r80.amplitudes(
        nodes, values, base_fam, h06.K, r80.family_quad(base_fam, h06.K))
    cond = max(amp_info["base"]["cond"], amp_info["corr"]["cond"])
    base = h06.embedded_reference(base_ref)
    corr = h06.embedded_reference(corr_ref)
    row = h06.measure(nodes, values, rho, delta, fam, xw, base, corr, cond,
                      0, 0.0)
    row["cond"] = cond
    row["n_fam"] = len(fam)
    row["support_radius"] = max(a for a, _t in fam) * (h06.N + 2)
    return row


def main():
    anchors = h06.load_anchors()
    out = {"record": "2006-calibration", "cases": []}
    for gamma, scale, tag in CASES:
        ref = anchors[tag]
        block = {"tag": tag, "gamma": gamma, "scale": scale,
                 "reference": {"C": float(ref["C"]), "D": float(ref["D"]),
                               "n_primes": ref.get("n_primes")},
                 "rungs": []}
        print("== %s  ref C=%.10e D=%.6e" % (tag, float(ref["C"]),
                                             float(ref["D"])))
        for dxi in DXIS:
            row = anchor_row(0.10, gamma, scale, dxi)
            ident = row.get("identity") or {}
            dev_c = abs(row["C"] - float(ref["C"])) / abs(float(ref["C"]))
            dev_d = abs(row["D"] - float(ref["D"])) / abs(float(ref["D"]))
            dev_var = ident.get("dev_var")
            dev_mom = ident.get("dev_moment")
            alg = None
            dev_a_c = None
            if ident:
                alg = abs(ident["det_var"] - ident["det_moment"]) / max(
                    abs(ident["det_var"]), 1.0)
                dev_a_c = ident.get("dev_A_C")
            block["rungs"].append({
                "dxi": dxi, "C": row["C"], "D": row["D"], "det": row["det"],
                "n_primes": row["n_primes"], "routes": row["routes"],
                "certified": row["certified"], "spread_D": row["spread_D"],
                "dev_C": dev_c, "dev_D": dev_d, "dev_var": dev_var,
                "dev_moment": dev_mom, "algebraic_var_vs_moment": alg,
                "C_B": ident.get("C_B"), "B01_B": ident.get("B01_B"),
                "D_B": ident.get("D_B"), "dev_A_C_B": dev_a_c,
            })
            print("   dxi=%.3f  C=%+.8e dev_C=%.3e  D=%+.6e dev_D=%.3e"
                  " n_pr=%s rt=%s"
                  % (dxi, row["C"], dev_c, row["D"], dev_d,
                     row["n_primes"], row["routes"]))
            print("            dev_var=%.3e dev_moment=%.3e"
                  " |var-mom|/|var|=%.3e"
                  % (dev_var, dev_mom, alg))
            print("            C_B=%+.8e  |A - C_B|/|C_B|=%.3e"
                  % (ident.get("C_B", float("nan")), dev_a_c))
        out["cases"].append(block)
    path = os.path.join(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), "results",
        "2006_route_a_health_cone_calibration.json")
    with open(path, "w", encoding="utf-8") as stream:
        json.dump(out, stream, indent=2)
        stream.write("\n")
    print("results -> %s" % path)


if __name__ == "__main__":
    main()
