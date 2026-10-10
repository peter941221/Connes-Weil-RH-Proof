"""Generate every complex panel-table module of entry (0, 3) (record 2655).

Extends the record-2648 pilot (panel 109) to the full 190-panel cover of
the record-2624 GO route: panels k = 0..189, center = -19/20 + (2k+1)/200,
half width 1/200, degree 55.  Each module reuses the 2648 emitter verbatim
(monkey-patched TAG/RECORD) and is regression-checked per panel against
build_complex_panel itself, exactly as the pilot was.

Scope: data layer only.  No analytic containment (next brick), no
off-diagonal claim, no Producer GO, no RH.
"""

import hashlib
import json
import sys
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

sys.path.insert(0, str(Path(__file__).resolve().parent))

import generate_complex_panel_table_2648 as g
from offdiagonal_residual_pricing_2624 import (
    ROW, build_complex_panel, column_parameters, panel_center)

ROOT = Path(__file__).resolve().parents[1]
DEGREE = g.DEGREE
RECORD = 2655
SKIP = {109}  # pilot panel, committed at record 2648


def render_panel(index, params, degree, prefix="ConnesWeilRH.Dev"):
    """Emit one panel table module for entry parameters `params`.

    Legacy callers pass the row-0 (0,3) parameters and the default prefix.
    Entry-scoped lanes (record 2664+) pass `prefix` = the entry namespace
    (e.g. `ConnesWeilRH.Dev.OffDiagE29_03`); the module text then declares
    that namespace and opens the parent, and no import rewrite is needed
    because the only import is the shared generic layer.
    """
    center = panel_center(index)
    tables = g.panel_tables(params["beta"], params["psi"], center, degree)
    tables["beta"], tables["psi"], tables["center"] = \
        params["beta"], params["psi"], center

    # per-panel regression against the 2624 pricing pipeline itself
    reference = build_complex_panel(params["beta"], params["psi"], center, degree)
    assert tables["modulus_bound"] == reference["residual_modulus_upper"], \
        f"panel {index}: residual upper diverges from the 2624 pipeline"
    assert tables["integral"] == reference["integral"], \
        f"panel {index}: integral diverges from the 2624 pipeline"

    g.RECORD = RECORD
    # build_module reads the 2648 module GLOBAL DEGREE for the literal
    # positions (`take {degree}`, `drop {degree + 5}`); panel_tables takes
    # degree as a parameter.  Without this line an entry at degree != 55
    # emits a degree-55 literal against a degree-66 list (found by the
    # record-2664 smoke build: `drop 60 [71 slots] = [(0,0)]` is false).
    g.DEGREE = degree
    g.TAG = f"{index:03d}"
    source = g.build_module(tables)
    if prefix != "ConnesWeilRH.Dev":
        assert source.count("namespace ConnesWeilRH.Dev\n") == 1, index
        source = source.replace(
            "namespace ConnesWeilRH.Dev\n",
            f"namespace {prefix}\n\nopen ConnesWeilRH.Dev\n", 1)
        assert source.count("end ConnesWeilRH.Dev") == 1, index
        source = source.replace("end ConnesWeilRH.Dev", f"end {prefix}", 1)
    return source, dict(
        panel=index, center=str(center),
        residual_upper=str(tables["modulus_bound"]),
        integral_re=str(tables["integral"][0]),
        integral_im=str(tables["integral"][1]))


def main():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    pilot = column_parameters(capture, 3)
    reports = []
    for index in range(190):
        if index in SKIP:
            continue
        source, report = render_panel(index, pilot, DEGREE)
        out = ROOT / f"ConnesWeilRH/Dev/C1RouteAComplexPanelTable{RECORD}P{g.TAG}.lean"
        out.write_text(source, encoding="utf-8", newline="\n")
        reports.append(report)
        print(index, f"{float(report['residual_upper']):.6e}", flush=True)

    imports = "\n".join(
        f"import ConnesWeilRH.Dev.C1RouteAComplexPanelTable2648P109"
        if index == 109 else
        f"import ConnesWeilRH.Dev.C1RouteAComplexPanelTable{RECORD}P{index:03d}"
        for index in range(190))
    umbrella = f"""{imports}

namespace ConnesWeilRH.Dev

/-!
# Full 190-panel table cover of entry (0, 3) (record {RECORD})

Umbrella module: imports the committed pilot table (panel 109, record
2648) and the {190 - len(SKIP)} batch tables emitted by
scripts/generate_panel_tables_all_2655.py.  Data layer only.
-/

end ConnesWeilRH.Dev
"""
    (ROOT / f"ConnesWeilRH/Dev/C1RouteAPanelTables{RECORD}.lean").write_text(
        umbrella, encoding="utf-8", newline="\n")

    payload = dict(
        record=RECORD, degree=DEGREE, entry=[ROW, 3],
        panel_count=190, emitted=190 - len(SKIP), pilot_panel=109,
        half_width="1/200", cut="19/20",
        beta_exact=str(pilot["beta"]), psi_exact=str(pilot["psi"]),
        regression="per-panel build_complex_panel equality on residual "
                   "upper and integral (189/189)",
        panels=reports,
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        umbrella_module=f"C1RouteAPanelTables{RECORD}.lean")
    (ROOT / f"results/{RECORD}_panel_tables.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"wrote {190 - len(SKIP)} modules + umbrella")


if __name__ == "__main__":
    main()
