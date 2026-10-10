#!/usr/bin/env python3
"""Record-2664 refactor gate: the four refactored per-panel generators must
still reproduce the committed entry-(0,3) modules BYTE-IDENTICALLY.

The record-2664 entry-parameterization extracted `render_panel` from each of
generate_panel_tables_all_2655 / generate_panel_analytic_all_2656 /
generate_amp_pins_2657 / generate_phase_pins_2658 (legacy mains now call the
extracted functions).  This checker renders a sample of panels through the
extracted functions at the DEFAULT prefix and compares against the committed
module bytes on disk.  Any drift is a refactor defect, not a lane finding.

Run: python3 scripts/check_generator_legacy_bytes_2664.py
Exit 0 iff every sampled module is byte-identical.
"""

import json
import sys
from fractions import Fraction as F
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

import offdiagonal_residual_pricing_2624 as P  # noqa: E402
import generate_panel_tables_all_2655 as T  # noqa: E402
import generate_panel_analytic_all_2656 as A  # noqa: E402
import generate_amp_pins_2657 as M  # noqa: E402
import generate_phase_pins_2658 as H  # noqa: E402
import gen_2663_panels as TP  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH" / "Dev"
SAMPLE = (0, 45, 94, 95, 189)


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text()
    )["owner_capture"]
    params = P.column_parameters(capture, 3)
    vacuous = {p["panel"] for p in json.loads(
        (ROOT / "results/2656_panel_analytic.json").read_text())["panels"]
        if F(p["var"]) >= 1}

    checks = []

    def cmp(name, text):
        committed = (DEV / name).read_text(encoding="utf-8")
        checks.append((name, text == committed))

    for index in SAMPLE:
        tag = f"{index:03d}"
        src, _ = T.render_panel(index, params, T.DEGREE)
        cmp(f"C1RouteAComplexPanelTable2655P{tag}.lean", src)
        src, _ = A.render_panel(index)
        cmp(f"C1RouteAComplexPanelAnalytic2656P{tag}.lean", src)
        src, _ = M.render_panel(index, params, vacuous)
        cmp(f"C1RouteAAmpPin2657P{tag}.lean", src)
        src, _ = H.render_panel(index, params["psi"])
        cmp(f"C1RouteAPhasePin2658P{tag}.lean", src)

    # record-2649 pilot table (panel 109) reproduces under RECORD=2648
    saved = T.RECORD
    T.RECORD = 2648
    src, _ = T.render_panel(109, params, T.DEGREE)
    cmp("C1RouteAComplexPanelTable2648P109.lean", src)
    T.RECORD = saved

    # trueball legacy render (incl. the k=94 template identity and the
    # k=109 pilot overrides)
    for index in (0, 94, 109, 189):
        tag = f"{index:03d}"
        src, _ = TP.render(index)
        cmp(f"C1RouteAPanelTrueBall2662P{tag}.lean", src)

    bad = [n for n, ok in checks if not ok]
    print(f"{len(checks) - len(bad)}/{len(checks)} byte-identical")
    for name in bad:
        print("MISMATCH", name)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())