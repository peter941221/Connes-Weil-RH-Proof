#!/usr/bin/env python3
"""2246 - Strict signed-margin statement at the 2243/2245/2248 standing.

Fixes the exact inequality the producer gate still owes, assembles the
current ledger from committed artifacts, and decomposes the obligation
into its three bricks:

  L1  a certified downward enclosure of the finite-window functional
      `|Q|` (the anchor is a binary64 sample without an error bar);
  L2  the complete-owner transfer: owner-count brick (2245: <= 26
      unconditional, 21 under the Platt-Trudgian import at the stress
      point) times the per-node uniformity lemma (open; the current
      product is a reading, not a proof);
  L3  the strict arithmetic: assemble `q_lower` against the upward
      charge bounds with a positive slack.

Writes results/2246_signed_margin_statement.json.  Statement artifact
only: no producer claim, no RH claim.
"""

import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
OUTPUT = R / "2246_signed_margin_statement.json"


def up(v, n=1):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def main():
    anchor_row = json.loads((R / "2103_full_known_prefix_direct_owner_grid_m6400.json")
                            .read_text(encoding="utf-8"))
    ledger = json.loads((R / "2109_known_prefix_margin_ledger.json")
                        .read_text(encoding="utf-8"))
    screen2243 = json.loads((R / "2243_panel_cem_reprice.json")
                            .read_text(encoding="utf-8"))
    brick2245 = json.loads((R / "2245_owner_count_brick.json")
                           .read_text(encoding="utf-8"))
    tight2248 = json.loads((R / "2248_multiplicity_tightening.json")
                           .read_text(encoding="utf-8"))

    gamma = 39.25244858548658
    rows = [r for r in anchor_row["rows"]
            if r["gamma"] == gamma and r["delta"] == 0.445]
    assert len(rows) == 1
    q_sample = rows[0]["q_step_002"]
    margin = abs(q_sample)
    assert margin == ledger["sampled_negative_margin"] == 1675397327895.099

    known_error = ledger["known_error_sum"]
    tail_old = screen2243["screen"]["high_shell_budget_upper"]
    tail_new = tight2248["reprice"]["tail_new"]
    mult_new = tight2248["proxy"]["mult_new_c72"]
    mult_old = tight2248["proxy"]["mult_old_c192"]
    b_upper = tight2248["reprice"]["b_upper"]
    stress = brick2245["stress"]

    charge_uncond = up(up(tail_new, 2) * stress["ratio_unconditional"], 2)
    charge_import = up(up(tail_new, 2) * stress["ratio_imported"], 2)
    total_uncond = up(up(charge_uncond, 1) + known_error, 1)
    total_import = up(up(charge_import, 1) + known_error, 1)
    reading_uncond = total_uncond / margin
    reading_import = total_import / margin
    stale = anchor_row["provenance"]["script"]
    result = {
        "record": 2246,
        "status": "SIGNED-MARGIN-STATEMENT-FIXED",
        "date": "2026-09-30",
        "target": {
            "rho": [0.945, gamma],
            "n_shell": 0,
            "support": 5.12,
            "scale": 0.8,
            "anchor_source": q_sample,
            "margin": margin,
            "anchor_is_sample_not_enclosure": True,
            "anchor_construction": stale,
        },
        "statement": (
            "There is eps0 > 0 and a certified downward enclosure q_lo of "
            "the finite-window functional with (-q_lo) - (4 * mult * "
            "B_upper + known_error_sum) >= eps0, where the high-shell "
            "budget is first transferred from the 62-node screen to the "
            "complete owner by the 2245 count brick and the per-node "
            "uniformity lemma.  The producer gate B_zm < epsilon(rho, N) "
            "is this inequality in the formal shell."),
        "ledger": {
            "anchor_margin": margin,
            "known_error_sum": known_error,
            "known_error_over_margin": ledger["known_error_over_margin"],
            "high_shell_budget_2234_standing": tail_old,
            "high_shell_budget_2248_standing": tail_new,
            "spectral_multiplicity_2243": mult_old,
            "spectral_multiplicity_2248": mult_new,
            "b_upper": b_upper,
            "count_ratio_unconditional": stress["ratio_unconditional"],
            "count_ratio_imported": stress["ratio_imported"],
            "transferred_charge_unconditional": charge_uncond,
            "transferred_charge_imported": charge_import,
            "total_charge_unconditional": total_uncond,
            "total_charge_imported": total_import,
            "reading_unconditional": reading_uncond,
            "reading_imported": reading_import,
            "slack_unconditional": 1.0 - reading_uncond,
            "slack_imported": 1.0 - reading_import,
        },
        "bricks": {
            "L1_downward_enclosure": {
                "status": "OPEN",
                "content": "certified interval enclosure of the direct "
                           "finite-window functional (trapezoid/solve/"
                           "quadrature outward) at the candidate",
                "note": "the known-error ledger (2109) prices the "
                        "evaluation errors but is charged against the "
                        "sampled margin, not an interval of it",
            },
            "L2_transfer": {
                "status": "COUNT-SIDE-DONE / PER-NODE-OPEN",
                "content": "owner cardinality at the stress point: <= 26 "
                           "unconditional (Trudgian window count), = 21 "
                           "under the Platt-Trudgian import (2245); "
                           "per-node uniformity of the screen charges "
                           "remains the open half",
            },
            "L3_strict_arithmetic": {
                "status": "STATEMENT-FIXED",
                "content": "q_lo > total charge with positive slack; "
                           "current slack ~0.9987 of the anchor",
            },
        },
        "combination_2245_2248": tight2248["reprice"],
        "nonclaims": [
            "the anchor is a binary64 sample; the strict inequality is not "
            "established until L1 lands",
            "the transferred charge uses the coarse linear reading; L2's "
            "per-node half is open",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_item5_margin_statement_2246.py",
            "artifacts": ["results/2103_full_known_prefix_direct_owner_grid_m6400.json",
                          "results/2109_known_prefix_margin_ledger.json",
                          "results/2243_panel_cem_reprice.json",
                          "results/2245_owner_count_brick.json",
                          "results/2248_multiplicity_tightening.json"],
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n",
                      encoding="utf-8", newline="\n")
    print(json.dumps({"status": result["status"],
                      "ledger": result["ledger"]}, indent=2))


if __name__ == "__main__":
    main()