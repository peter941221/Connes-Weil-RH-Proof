#!/usr/bin/env python3
"""Record the vertex gate budget split for the committed four-point cases."""

import json
import math
import os


INPUT = "results/1918_fourpoint_diagonal_sign_certified.json"
OUTPUT = "results/1946_fourpoint_vertex_channel_budget.json"


def main():
    with open(INPUT, encoding="utf-8") as fh:
        cases = json.load(fh)["cases"]

    rows = []
    for case in cases:
        d = case["cert"]["D_cert"]
        c = case["C"]["IC"]
        b = case["Bs"]
        lam = case["lam_vertex"]
        q = d - lam * b + lam * lam * c

        da = case["D"]["arch_sigma"]
        ca = case["C"]["arch_sigma"]
        ba = case["B01"]["arch_sigma"] + case["B10"]["arch_sigma"]
        qa = da - lam * ba + lam * lam * ca
        qp = q - qa
        rows.append(
            {
                "tag": case["tag"],
                "c": case["c"],
                "gamma": case["rho"][1],
                "lambda_vertex": lam,
                "Q_full": q,
                "Q_arch": qa,
                "Q_prime": qp,
                "prime_beats_positive_arch": (
                    -qp / qa if qa > 0.0 else None
                ),
                "relative_full_margin": -q / max(abs(d), 1.0),
            }
        )

    positive_arch = [row for row in rows if row["Q_arch"] > 0.0]
    ratios = [row["prime_beats_positive_arch"] for row in positive_arch]
    summary = {
        "case_count": len(rows),
        "full_negative_count": sum(row["Q_full"] < 0.0 for row in rows),
        "arch_positive_count": len(positive_arch),
        "prime_negative_count": sum(row["Q_prime"] < 0.0 for row in rows),
        "min_full_relative_margin": min(row["relative_full_margin"] for row in rows),
        "min_prime_over_positive_arch": min(ratios) if ratios else None,
        "min_Q_full": min(row["Q_full"] for row in rows),
        "max_Q_full": max(row["Q_full"] for row in rows),
    }
    result = {"provenance": "1918 certified gate entries; vertex Q split by linear ICgate entries", "summary": summary, "rows": rows}
    os.makedirs(os.path.dirname(OUTPUT), exist_ok=True)
    with open(OUTPUT, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=2)
    print(json.dumps(summary, indent=2))
    print("wrote", OUTPUT)


if __name__ == "__main__":
    main()
