#!/usr/bin/env python3
"""Reduce the record-2664 full off-diagonal survey (376 MB, rung boxes
inline) to a committable per-entry projection.

The full artifact `results/2664_offdiag_survey.json` holds every ladder
rung's exact box for all 870 entries; only the per-entry screen verdicts
(first-pass degree, degree-55 margins, psi-zero flags) and the summary
block are needed for the batch plan and for the record.  This reducer
reads the full artifact and writes

    results/2664_offdiag_survey_summary.json

with `entries` projected to {row, column, psi_zero, first_pass_degree,
abs_psi, deg55 min-margin, per-rung margins}, plus the summary block
verbatim.  It also prints the ladder-needed list (first pass above the
degree-55 floor) sorted by required degree, so the extended-ladder wave
can be scoped with `survey_offdiag_2664.py --entries=... --ladder=...`.

The full artifact itself stays untracked on disk (gitignored): it is
regenerable in ~37 minutes with the committed survey script, and its
content is dominated by per-rung exact boxes that the summary projection
retains as margins.
"""

import json
import os
import sys
from fractions import Fraction as F

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FULL = os.path.join(ROOT, "results", "2664_offdiag_survey.json")
OUT = os.path.join(ROOT, "results", "2664_offdiag_survey_summary.json")


def rung_margin(rung):
    return min(F(rung["real"]["min_margin_over_box"]),
               F(rung["imag"]["min_margin_over_box"]))


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    with open(FULL, encoding="utf-8") as fh:
        payload = json.load(fh)

    # The screen margins are monster rationals (hundreds of digits); the
    # committed projection keeps them as display floats plus the exact
    # `inside` verdicts.  The exact strings stay in the untracked full
    # artifact, and every Lean literal is regenerated from the capture by
    # the pricing pipeline, never read from this screen (AGENTS 2cn).
    entries = []
    for r in payload["entries"]:
        if "error" in r:
            entries.append({"row": r["row"], "column": r["column"],
                            "error": r["error"]})
            continue
        rungs = [{"degree": g["degree"],
                  "inside": g["inside"],
                  "min_margin_over_box_float": float(rung_margin(g))}
                 for g in r["rungs"]]
        entries.append({
            "row": r["row"], "column": r["column"],
            "psi_zero": r["psi_zero"],
            "abs_psi_float": float(F(r["abs_psi"])),
            "first_pass_degree": r["first_pass_degree"],
            "deg55_min_margin_over_box_float":
                float(rung_margin(r["rungs"][0])),
            "rungs": rungs,
        })

    summary = dict(payload.get("summary", {}))
    out = {
        "record": payload.get("record"),
        "purpose": payload.get("purpose"),
        "source_artifact": "results/2664_offdiag_survey.json "
                           "(full rung boxes; untracked, regenerable)",
        "anchor_2624_pilot": payload.get("anchor_2624_pilot"),
        "degree_ladder_run": payload.get("degree_ladder_run"),
        "margin_floor": payload.get("margin_floor"),
        "witness_sha256": payload.get("witness_sha256"),
        "generator_sha256": payload.get("generator_sha256"),
        "summary": summary,
        "entries": entries,
    }
    with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
        fh.write("\n")

    # ladder-needed: inside-and-margin clean at degree 55? no ->
    # (a) first inside rung ABOVE 55, or (b) inside at 55 but margin floor
    # not met (the survey's ladder break condition includes the floor).
    ladder = [e for e in entries
              if "error" not in e and not e["psi_zero"]
              and (e["first_pass_degree"] is None
                   or e["first_pass_degree"] != 55
                   or e["deg55_min_margin_over_box_float"] < 4)]
    ladder.sort(key=lambda e: (-(e["first_pass_degree"] or 10 ** 6),))
    psi_zero = [e for e in entries if "error" not in e and e["psi_zero"]]
    print(f"projected {len(entries)} entries -> "
          f"{os.path.basename(OUT)} "
          f"({os.path.getsize(OUT)} bytes)")
    print(f"psi-zero class: {len(psi_zero)} entries "
          f"({[(e['row'], e['column']) for e in psi_zero]})")
    print(f"ladder-needed entries: {len(ladder)}")
    for e in ladder:
        last = e["rungs"][-1]
        print(f"  ({e['row']:2d},{e['column']:2d}) first_pass="
              f"{e['first_pass_degree']} "
              f"abs_psi={e['abs_psi_float']:.4f} "
              f"last_deg={last['degree']} last_margin="
              f"{last['min_margin_over_box_float']:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())