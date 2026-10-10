"""Lane A pricing audit (record 2649 evidence).

Turns the open question "how much of the qw(g) >= 0 core is left" into a
quantified inventory built ONLY from committed payloads:

* the C3' grid space: 10240 cells over [-stripRadius2303, +stripRadius2303]
  (R = 6.5536001, certified in C1RouteAItem5Arithmetic.lean; the cell
  arithmetic -R + 10240*(2R/10240) = R is proved in
  C1RouteACorrectionSecondChord2574.lean), two signs sigma = +-1/2,
  i.e. 20480 cell obligations;
* the conditional inventory actually certified so far, with each entry's
  provenance payload and its retaining conditions;
* the committed per-cell cost model (generators per cell from the
  2547-2551 pipeline, family-evaluation depths from 2552, Lean batch
  rhythm from the diagonal campaign);
* the known dead ends (never re-attempt): channelwise absolute
  majorants, fixed-prime countermodels, sign-equivalent hypotheses.

No new numerics are computed here: every number either comes from a
committed results/ payload or is a count over the certified grid space.

Scope: inventory only. No producer claim, no SourceRH, no RH.
"""

import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECORD = 2649

R_NUM, R_DEN = 65536001, 10 ** 7          # stripRadius2303 = 6.5536001
CELLS = 10240
SIGNS = ("+1/2", "-1/2")


def load(name):
    return json.loads((ROOT / "results" / name).read_text())


def main():
    # --- grid space -------------------------------------------------------
    radius = Fraction(R_NUM, R_DEN)
    step = 2 * radius / CELLS

    # --- committed payloads ----------------------------------------------
    p2543 = load("2543_derivative_pricing.json")
    p2546 = load("2546_cell_readback.json")
    p2551 = load("2551_boundary_integral_readback.json")
    p2552 = load("2552_batch_cost_inputs.json")

    # sanity: scope locks where payloads carry them must not be True
    LOCK_KEYS = ("full_grid_certificate", "producer_go", "rh_claim",
                 "exact_coefficient_membership", "formal_build_verified")
    lock_report = {}
    for name, payload in (("2543", p2543), ("2546", p2546),
                          ("2551", p2551), ("2552", p2552)):
        locks = {key: payload[key] for key in LOCK_KEYS if key in payload}
        assert not any(value is True for value in locks.values()), \
            f"scope lock opened in {name}"
        lock_report[name] = locks

    # grid arithmetic: both 2551 nodes stay inside the strip window
    for node in ("left_node", "right_node"):
        position = Fraction(p2551[node]["position"])
        assert -radius <= position <= radius, node

    # --- certified (conditional) inventory --------------------------------
    # provenance: committed payloads + the lane-A map bullet
    conditional = [
        {"cell": "5440", "sign": "+1/2", "class": "conditional_midpoint_envelope",
         "upper": "2494.6018425 (order two, actual midpoint)",
         "payload_scope": p2543.get("scope", ""),
         "retains": "coefficient-ball membership",
         "payloads": ["2543_derivative_pricing.json", "2544_endpoint_readback.json",
                      "2545_fourth_readback.json", "2546_cell_readback.json"]},
        {"cell": "2700", "sign": "+1/2", "class": "conditional_boundary_integral",
         "upper": "57/500000000000 (1.14e-10)",
         "retains": "coefficient-ball membership retained; "
                    "exact_coefficient_membership=False",
         "payloads": ["2547_boundary_readback.json", "2548_boundary_jets_readback.json",
                      "2549_boundary_bounds_readback.json",
                      "2550_boundary_fourth_readback.json",
                      "2551_boundary_integral_readback.json"]},
        {"cell": "2700", "sign": "-1/2", "class": "conditional_correction_pair",
         "upper": "correction-pair chains priced (2565-2576)",
         "retains": "strip-lane readbacks; same coefficient-ball caveat",
         "payloads": ["2565-2576 record family (see docs/proofs)"]},
    ]

    costed_evaluations = [
        {"family": case["family"], "position": case["position"],
         "depth": case["depth"],
         "derivative_error_display": case["derivative_error_display"]}
        for case in p2552["cases"]
    ]

    total_obligations = CELLS * len(SIGNS)
    conditional_cells = len(conditional)
    open_obligations = total_obligations - conditional_cells

    # --- cost model (all inputs committed) --------------------------------
    cost_model = {
        "generators_per_cell": 5,
        "generators_pattern": "2547-2551: boundary replay, jets, fourth, "
                              "bounds, integral",
        "lean_batch": "one 544-target xargs batch class per cell group "
                      "(diagonal-campaign rhythm, ~350-450 s wall, "
                      "triple acceptance 30/30 first-try)",
        "family_eval_depth_range": [min(int(c["depth"]) for c in costed_evaluations),
                                    max(int(c["depth"]) for c in costed_evaluations)],
        "deepest_certified_chain": "2551: 160-bit derivative evaluation, "
                                   "exact exterior-zero branches",
    }

    # --- unknowns, ranked (the honest part) -------------------------------
    unknowns = [
        {"rank": 1,
         "unknown": "coefficient-ball discharge margin per cell",
         "why": "every certified cell retains coefficient-ball membership "
                "(2546/2551 exact_coefficient_membership=False); whether the "
                "margins survive unconditional discharge is the only genuine "
                "mathematical unknown; tool = the 2618-2648 analytic/complex "
                "containment layers",
         "resolution": "discharge cell2700 first (tightest margin, 1.14e-10)"},
        {"rank": 2,
         "unknown": "sign coverage of the boundary-jets method near "
                    "support crossings",
         "why": "certified cells sit at sigma=+1/2 (2543-2551) with one "
                "correction-pair counterpart; the minus-sign chain 2565-2576 "
                "is priced but not boundary-integral certified",
         "resolution": "rerun the 2547-2551 pipeline at sigma=-1/2"},
        {"rank": 3,
         "unknown": "exact-owner transfer composition at full grid",
         "why": "point import (2452), node norm (2453-54) and quadrature "
                "import (2455-59) exist per-seam; the full-grid composition "
                "is unbuilt",
         "resolution": "assemble after the first discharged cell; the 2334 "
                       "lesson forbids proxy-owner shortcuts"},
    ]

    dead_ends = [
        "channelwise absolute majorants (map: do not close it)",
        "fixed-prime countermodels (map: do not close it)",
        "hypotheses equivalent to the desired sign (map: do not close it)",
        "lane B four-point family (frozen DEAD_ON_CURRENT_FAMILY)",
    ]

    audit = {
        "record": RECORD,
        "scope": "inventory of the qw(g)>=0 core obligations from committed "
                 "payloads only",
        "grid": {
            "cells": CELLS,
            "strip_radius": "65536001/10^7 (stripRadius2303, "
                            "C1RouteAItem5Arithmetic.lean)",
            "cell_arithmetic_proof": "C1RouteACorrectionSecondChord2574.lean",
            "cell_step_exact": str(step),
            "signs": list(SIGNS),
            "total_obligations": total_obligations,
        },
        "inventory": {
            "unconditional": 0,
            "conditional_certified": conditional_cells,
            "conditional_cells": conditional,
            "open_obligations": open_obligations,
            "open_fraction": f"{open_obligations}/{total_obligations}",
        },
        "cost_model": cost_model,
        "costed_family_evaluations": costed_evaluations,
        "payload_lock_report": lock_report,
        "unknowns_ranked": unknowns,
        "dead_ends": dead_ends,
        "locks": {"producer_go": False, "source_rh": False, "rh": False},
        "conclusion": "the core reduces to: discharge #1 (coefficient-ball), "
                      "then certified-machinery scale-out over "
                      f"{open_obligations} obligations; the discharge of "
                      "cell2700 is the single cheapest experiment that "
                      "converts the only mathematical unknown into a number",
    }

    out = ROOT / "results" / f"{RECORD}_lane_a_pricing_audit.json"
    out.write_text(json.dumps(audit, indent=2) + "\n", encoding="utf-8",
                   newline="\n")
    print(f"wrote {out.name}: {total_obligations} obligations, "
          f"{conditional_cells} conditional, {open_obligations} open; "
          f"unknown #1 = coefficient-ball discharge (cell2700 first)")


if __name__ == "__main__":
    main()
