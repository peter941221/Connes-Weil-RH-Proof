#!/usr/bin/env python3
"""Record 2664 scoping: global off-diagonal survey of the entry-(0,3)
membership template.

Session finding that motivates this probe: the record-2624 degree
calibration searched ROW 0 only, while the exact entry parameters

    beta_ij = Re(node_i) * width_j^2,
    psi_ij  = (Im(node_i) - Im(node_j)) * width_j^2

(the committed capture has modulation_j = -Im(node_j) for every column)
reach |psi| = 638.30 at (29, 3) against the (0, 3) pilot's 422.87, and 14
off-diagonal pairs carry psi = 0 exactly.  This probe therefore

  1. builds the exact (beta, psi) matrix over all 900 entries from the
     committed capture (results/2275_gap_owner_audit.json owner_capture),
     reproducing the record-2624 pilot parameters exactly (anchor assert);
  2. reads every home rectangle from the committed 2597 Lean table
     (element `j` of `analyticMomentInterval2597_row_{i}`) and asserts
     agreement with the 2351 witness matrix on every entry;
  3. prices every off-diagonal entry with the record-2624 pipeline
     (`panel_pricing` at degree 55 over the 190 x 1/200 panels + the
     monotone edge charge), checking a per-panel regression against
     `build_complex_panel` and the (0,3) box anchor against the committed
     2624 payload, and records the four containment margins against the
     home rectangle (exact Fractions);
  4. ladders the entries that fail or sit below a margin floor through
     degrees 58, 60, 63, 66, 70 and records the first passing rung.

Output: results/2664_offdiag_survey.json.  Data layer only: no Lean
modules, no membership claim, no producer GO, no SourceRH, no RH.
"""

import hashlib
import json
import multiprocessing as mp
import os
import re
import sys
import time
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

from offdiagonal_residual_pricing_2624 import (  # noqa: E402
    CUT, PANEL_COUNT, build_complex_panel, column_parameters,
    panel_center, panel_pricing)
from generate_complex_panel_table_2648 import panel_tables  # noqa: E402
from generate_moment_scalar_certificate_2620 import compact_scalar  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEGREE = 55
LADDER = (58, 60, 63, 66, 70)
# entries below this min-margin-to-box ratio get laddered even when passing
MARGIN_FLOOR = 4
SAMPLE_PANELS = (0, 95, 189)


def load_capture():
    return json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]


def entry_parameters(capture, row, column):
    """The per-(row, column) exact parameters, in the 2624 dict shape."""
    width = F(float.fromhex(capture["families_hex"][column][0]))
    modulation = F(float.fromhex(capture["families_hex"][column][1]))
    node_real = F(float.fromhex(capture["nodes_hex"][row][0]))
    node_imag = F(float.fromhex(capture["nodes_hex"][row][1]))
    radius = width * width
    return {"radius": radius, "beta": node_real * radius,
            "psi": (node_imag + modulation) * radius}


def parse_home_rectangles():
    """Parse all 30x30 home rectangles from the committed 2597 Lean table."""
    src = (ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionAnalyticIntervals2597.lean"
           ).read_text(encoding="utf-8")
    starts = [m for m in re.finditer(
        r"noncomputable def analyticMomentInterval2597_row_(\d\d)\b"
        r"[^\n]*?:=\s*!\[", src)]
    assert len(starts) == 30, len(starts)
    rect = {}
    for pos, m in enumerate(starts):
        row = int(m.group(1))
        end = starts[pos + 1].start() if pos + 1 < len(starts) else len(src)
        elems = re.findall(r"\{[^{}]*\}", src[m.end():end])
        assert len(elems) == 30, (row, len(elems))
        for col, el in enumerate(elems):
            quad = re.findall(
                r"(reLo|reHi|imLo|imHi) := \(\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)\)",
                el)
            assert [q[0] for q in quad] == ["reLo", "reHi", "imLo", "imHi"], \
                (row, col)
            rect[(row, col)] = {q[0]: F(int(q[1]), int(q[2])) for q in quad}
    return rect


def anchor_checks(capture, rect):
    """The 2624 pilot reproduction and the witness agreement anchors."""
    pilot = column_parameters(capture, 3)
    mine = entry_parameters(capture, 0, 3)
    assert mine == pilot, "entry_parameters(0,3) != 2624 pilot parameters"
    payload = json.loads(
        (ROOT / "results/2655_panel_tables.json").read_text())
    assert F(payload["beta_exact"]) == pilot["beta"], "beta drift vs 2655"
    assert F(payload["psi_exact"]) == pilot["psi"], "psi drift vs 2655"
    witness = json.loads(
        (ROOT / "results/2351_moment_matrix_witness.json").read_text())
    mismatch = 0
    for (row, col), quad in rect.items():
        w = witness["matrix"][row][col]
        for lbl, key, sub in (("reLo", "real", "lower_exact"),
                              ("reHi", "real", "upper_exact"),
                              ("imLo", "imag", "lower_exact"),
                              ("imHi", "imag", "upper_exact")):
            if quad[lbl] != F(w[key][sub]):
                mismatch += 1
    assert mismatch == 0, f"{mismatch} 2597-vs-witness rectangle mismatches"
    return witness


def price_entry(capture, rect, row, col, ladder=LADDER,
                regress_all=False):
    """Price one entry with the 2624 pipeline; ladder if needed."""
    params = entry_parameters(capture, row, col)
    radius, beta, psi = params["radius"], params["beta"], params["psi"]
    quad = rect[(row, col)]
    real_half = (quad["reHi"] - quad["reLo"]) / 2
    imag_half = (quad["imHi"] - quad["imLo"]) / 2

    def run(degree):
        t0 = time.time()
        total_charge = F(0)
        worst_panel = (0, F(0))
        center = (F(0), F(0))
        for index in range(PANEL_COUNT):
            price = panel_pricing(params, panel_center(index), degree)
            total_charge += price["charge"]
            center = (center[0] + price["contribution"][0],
                      center[1] + price["contribution"][1])
            if price["charge"] > worst_panel[1]:
                worst_panel = (index, price["charge"])
        # regression: the 2648-table emitter (the object the Lean modules
        # are generated from) against the 2624 pricing recurrence
        panels = range(PANEL_COUNT) if regress_all else SAMPLE_PANELS
        for index in panels:
            reference = build_complex_panel(beta, psi, panel_center(index),
                                            degree)
            table = panel_tables(beta, psi, panel_center(index), degree)
            assert table["modulus_bound"] == reference["residual_modulus_upper"], \
                (row, col, index, degree, "residual upper drift")
            assert table["integral"] == reference["integral"], \
                (row, col, index, degree, "integral drift")
        edge_phase = F(-30) / (1 - CUT ** 2) + beta * CUT
        edge_center, edge_radius = compact_scalar(edge_phase)[-1]
        edge = radius * 2 * (1 - CUT) * (edge_center + edge_radius)
        box = total_charge + edge

        def margin(value, lo, hi):
            m_lo = (value - box) - lo
            m_hi = hi - (value + box)
            return {"slack_lo": str(m_lo), "slack_hi": str(m_hi),
                    "inside": m_lo >= 0 and m_hi >= 0,
                    "min_margin_over_box": str(min(m_lo, m_hi) / box)}

        real = margin(center[0], quad["reLo"], quad["reHi"])
        imag = margin(center[1], quad["imLo"], quad["imHi"])
        return {"degree": degree,
                "box_exact": str(box),
                "edge_exact": str(edge),
                "worst_panel": worst_panel[0],
                "center_re_exact": str(center[0]),
                "center_im_exact": str(center[1]),
                "real": real, "imag": imag,
                "inside": real["inside"] and imag["inside"],
                "wall_seconds": round(time.time() - t0, 3)}

    rung = run(DEGREE)
    rungs = [rung]
    if not rung["inside"] or \
            min(F(rung["real"]["min_margin_over_box"]),
                F(rung["imag"]["min_margin_over_box"])) < MARGIN_FLOOR:
        for degree in ladder:
            rung = run(degree)
            rungs.append(rung)
            if rung["inside"] and \
                    min(F(rung["real"]["min_margin_over_box"]),
                        F(rung["imag"]["min_margin_over_box"])) >= MARGIN_FLOOR:
                break
    return {"row": row, "column": col,
            "radius_exact": str(radius), "beta_exact": str(beta),
            "psi_exact": str(psi), "psi_zero": psi == 0,
            "abs_psi": str(abs(psi)),
            "rect_re_half_exact": str(real_half),
            "rect_im_half_exact": str(imag_half),
            "rungs": rungs,
            "first_pass_degree": next(
                (r["degree"] for r in rungs if r["inside"]), None)}


_WORKER = {}


def _init_worker():
    _WORKER["capture"] = load_capture()
    _WORKER["rect"] = parse_home_rectangles()


def _worker(task):
    row, col, ladder, regress_all = task
    try:
        return price_entry(_WORKER["capture"], _WORKER["rect"], row, col,
                           ladder=ladder, regress_all=regress_all)
    except Exception as exc:  # noqa: BLE001 - report per-entry failures
        return {"row": row, "column": col, "error": repr(exc)}


def main():
    args = sys.argv[1:]
    entries = None
    jobs = min(14, os.cpu_count() or 4)
    regress_all = False
    ladder = LADDER
    out_name = "2664_offdiag_survey.json"
    for arg in args:
        if arg == "--regress-all":
            regress_all = True
        elif arg.startswith("--jobs="):
            jobs = int(arg.split("=", 1)[1])
        elif arg.startswith("--out="):
            out_name = arg.split("=", 1)[1]
        elif arg.startswith("--ladder="):
            ladder = tuple(int(x) for x in arg.split("=", 1)[1].split(","))
        elif arg.startswith("--entries="):
            entries = [tuple(int(x) for x in pair.split(","))
                       for pair in arg.split("=", 1)[1].split(";")]
    capture = load_capture()
    rect = parse_home_rectangles()
    anchor_checks(capture, rect)
    if entries is None:
        entries = [(i, j) for i in range(30) for j in range(30) if i != j]
    print(f"surveying {len(entries)} entries at degree {DEGREE} "
          f"(ladder {ladder}), jobs={jobs}", flush=True)

    tasks = [(i, j, ladder, regress_all) for (i, j) in entries]
    results = []
    t0 = time.time()
    if jobs > 1 and len(tasks) > 1:
        with mp.Pool(processes=jobs, initializer=_init_worker) as pool:
            for k, res in enumerate(pool.imap_unordered(_worker, tasks)):
                results.append(res)
                if (k + 1) % 20 == 0 or (k + 1) == len(tasks):
                    print(f"  {k + 1}/{len(tasks)} done "
                          f"({time.time() - t0:.0f}s)", flush=True)
    else:
        _init_worker()
        for k, task in enumerate(tasks):
            results.append(_worker(task))
            if (k + 1) % 20 == 0:
                print(f"  {k + 1}/{len(tasks)} done", flush=True)
    results.sort(key=lambda r: (r["row"], r["column"]))

    # ---- (0,3) box anchor against the committed 2624 payload ----
    payload = json.loads(
        (ROOT / "results/2624_offdiagonal_pricing.json").read_text())
    ladder55 = [r for r in payload["degree_ladder"] if r["degree"] == 55][0]
    anchor = next(r for r in results if (r["row"], r["column"]) == (0, 3))
    anchor_ok = anchor["rungs"][0]["box_exact"] == ladder55["box_total_exact"]

    failures = [r for r in results if "error" in r]
    priced = [r for r in results if "error" not in r]
    nonzero = [r for r in priced if not r["psi_zero"]]
    pass55 = [r for r in nonzero
              if r["rungs"][0]["inside"] and r["rungs"][0]["degree"] == 55
              and F(r["rungs"][0]["real"]["min_margin_over_box"]) >= MARGIN_FLOOR
              and F(r["rungs"][0]["imag"]["min_margin_over_box"]) >= MARGIN_FLOOR]
    worst = sorted(
        nonzero,
        key=lambda r: min(F(r["rungs"][0]["real"]["min_margin_over_box"]),
                          F(r["rungs"][0]["imag"]["min_margin_over_box"])))
    degree_hist = {}
    for r in priced:
        key = r["first_pass_degree"] if r["first_pass_degree"] is not None \
            else f">{ladder[-1]}"
        degree_hist[str(key)] = degree_hist.get(str(key), 0) + 1
    times = [r["rungs"][0]["wall_seconds"] for r in priced]
    times_sorted = sorted(times)

    payload_out = {
        "record": 2664,
        "purpose": "global off-diagonal phase survey + degree-55 screen of "
                   "the 2624 pipeline against the committed 2597 home "
                   "rectangles",
        "anchor_2624_pilot": {
            "entry": [0, 3], "beta_exact": str(entry_parameters(capture, 0, 3)["beta"]),
            "psi_exact": str(entry_parameters(capture, 0, 3)["psi"]),
            "pilot_parameters_reproduced": True,
            "box55_equals_committed_2624_payload": anchor_ok},
        "degree_ladder_run": list(ladder),
        "margin_floor": MARGIN_FLOOR,
        "summary": {
            "entries_priced": len(priced),
            "errors": [ {k: r[k] for k in ("row", "column", "error")}
                        for r in failures],
            "psi_zero_offdiag": sorted(
                (r["row"], r["column"]) for r in priced if r["psi_zero"]),
            "pass_deg55_floor4": len(pass55),
            "need_ladder": len(nonzero) - len(pass55),
            "first_pass_degree_histogram": degree_hist,
            "worst5_by_deg55_margin": [
                {"entry": [r["row"], r["column"]],
                 "abs_psi_float": float(F(r["abs_psi"])),
                 "min_margin_over_box":
                     str(min(F(r["rungs"][0]["real"]["min_margin_over_box"]),
                             F(r["rungs"][0]["imag"]["min_margin_over_box"]))),
                 "first_pass_degree": r["first_pass_degree"]}
                for r in worst[:5]],
            "pipeline_seconds_per_entry_deg55": {
                "min": times_sorted[0],
                "median": times_sorted[len(times_sorted) // 2],
                "max": times_sorted[-1]},
            "lean_per_module_seconds_warm": {
                "table2655": 2.7, "analytic2656": 2.8, "amp2657": 2.9,
                "phase2658": 4.3, "trueball2662": 2.9,
                "source": "results/timing_2664_probe.txt (16-core "
                          "workspace run)"},
            "per_entry_lean_module_inventory": {
                "table": 190, "analytic": 189, "amp": 190, "phase": 190,
                "trueball": 190, "support_2663_style": 13, "assembly": 1},
        },
        "entries": [r for r in results],
        "witness_sha256": hashlib.sha256(
            (ROOT / "results/2351_moment_matrix_witness.json").read_bytes()
        ).hexdigest(),
        "generator_sha256": hashlib.sha256(
            Path(__file__).read_bytes()).hexdigest(),
        "pricing_lean_verified": False,
        "membership_claimed": False,
        "producer_go": False, "rh_claim": False,
    }
    out = ROOT / "results" / out_name
    out.write_text(json.dumps(payload_out, indent=1) + "\n",
                   encoding="utf-8", newline="\n")
    print(f"anchor (0,3) box55 == 2624 payload: {anchor_ok}", flush=True)
    print(f"priced {len(priced)} entries; pass deg55 (floor {MARGIN_FLOOR}x): "
          f"{len(pass55)}; ladder needed: {len(nonzero) - len(pass55)}",
          flush=True)
    print(f"degree histogram: {degree_hist}", flush=True)
    print(f"seconds/entry deg55: min {times_sorted[0]} "
          f"median {times_sorted[len(times_sorted)//2]} "
          f"max {times_sorted[-1]}", flush=True)
    print(f"wrote {out.name}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())