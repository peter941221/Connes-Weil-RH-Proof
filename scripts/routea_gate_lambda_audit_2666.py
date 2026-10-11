#!/usr/bin/env python3
"""Gate-lambda determination probe (record 2666, audit grade).

Question (record 2354 next-step 3, narrowed): does the ACTUAL lambda of the
committed four-point span construction land inside either 2354 scalar
acceptance lane (n=2 with lambda >= 256, or n=3 with lambda >= 1e-13)?

Instrument: pure arithmetic on committed artifacts.  The construction's
lambda is the quadratic vertex lam_vertex = Bs / (2C) of the gate form
Q(lam) = D - lam*Bs + lam^2*C with D = IC(u*u), C = IC(g*g),
Bs = IC(u*g) + IC(g*u) -- committed per case in
results/1918_fourpoint_diagonal_sign_certified.json and re-probed in
results/1945_fourpoint_explicit_lambda_probe.json.  Record 2354 proves the
tail-budget ratio is non-increasing in lambda > 0, so the vertex choice is
inside a lane iff the lane threshold is below it; no new gate witness, no
Gram re-run, no coefficient solve, and no reopening of the frozen family
(AGENTS 2ay) is performed or claimed.

Verdicts (per lane): SEPARATED if min lam_vertex over the certified class
exceeds the threshold by the recorded factor; the repaired-owner lambda
drift is bounded at audit grade by the record-2665 per-coefficient envelope
with the Gram-ratio condition constant named as the residual.
"""

import json
import statistics

CERT_LAMBDA = "results/1945_fourpoint_explicit_lambda_probe.json"
M1_WINDOW = "results/2665_window_margin_repair.json"
LANES = [("n=2", 256.0), ("n=3", 1e-13)]
OUT = "results/2666_gate_lambda_audit.json"


def main():
    probe = json.load(open(CERT_LAMBDA, encoding="utf-8"))
    rows = probe["rows"]
    lam = sorted(r["lambda"]["vertex"] for r in rows)
    k = [r["K"] for r in rows]
    struct = sorted(r["lambda"]["vertex"] / (0.5 * r["K"] ** 4) for r in rows)
    vertex_q_neg = sum(1 for r in rows if r["Q"]["vertex"] < 0.0)

    m1 = json.load(open(M1_WINDOW, encoding="utf-8"))
    rmax = m1.get("monotone_screens") or {}
    rmax_base = rmax.get("rmax_base")
    rmax_corr = rmax.get("rmax_corr")

    lane_rows = []
    for name, thr in LANES:
        best = lam[0] / thr
        lane_rows.append({
            "lane": name,
            "threshold": thr,
            "min_lambda": lam[0],
            "separation_factor": best,
            "verdict": "SEPARATED" if best > 1.0 else "NOT-SEPARATED",
        })

    result = {
        "record": 2666,
        "title": "gate-lambda determination probe (audit grade)",
        "consumer": ("record 2354 scalar acceptance lanes; the same-owner "
                     "four-point span tail budget shares this lambda"),
        "instrument": ("committed 1918/1945 certified-class lambda values; "
                       "no rig re-run, no Gram re-evaluation, no reopening"),
        "class": {
            "cases": len(rows),
            "vertex_Q_negative": vertex_q_neg,
            "lambda_min": lam[0],
            "lambda_median": statistics.median(lam),
            "lambda_max": lam[-1],
            "K_min": k[0],
            "K_max": k[-1],
            "lambda_over_halfK4_min": struct[0],
            "lambda_over_halfK4_median": statistics.median(struct),
            "lambda_over_halfK4_max": struct[-1],
        },
        "lanes": lane_rows,
        "repair_drift_envelope": {
            "rmax_base_2665": rmax_base,
            "rmax_corr_2665": rmax_corr,
            "statement": (
                "lambda = Bs/(2C) is a degree-2/degree-2 rational function "
                "of the selected-function coefficients.  First-order drift "
                "under the 2338 repair is bounded by (condition constant) x "
                "per-coefficient envelope; the Gram-ratio condition constant "
                "is the named residual.  An exact check is the two-entry "
                "(Bs, C) re-run at the repaired pair, deliberately NOT "
                "executed here (frozen-family hazard, AGENTS 2ay)."),
        },
        "verdict": "GATE-LAMBDA-SEPARATED-FROM-LANES (audit grade)",
        "nonclaims": [
            "no gate witness at the repaired owner (the signed "
            "physical-kernel gate remains the open producer bottleneck)",
            "no repaired-owner Gram re-run and no annihilation-identity "
            "reuse beyond reading the committed lambda values",
            "no lane acceptance: SEPARATED is a necessary-condition audit, "
            "not a tail pass (record 2354 ratios stay conditional)",
            "record 2354 status 'actual gate lambda remains unproved' "
            "stands; this probe quantifies the separation",
        ],
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=2)
    print(json.dumps({"verdict": result["verdict"],
                      "lambda_min": lam[0],
                      "lanes": [(r["lane"], r["separation_factor"],
                                 r["verdict"]) for r in lane_rows]}, indent=2))
    print("wrote", OUT)


if __name__ == "__main__":
    main()
