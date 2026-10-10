#!/usr/bin/env python3
"""Entry-scoped generator for the off-diagonal membership campaign (2664).

Generates the full per-panel five-family Lean chain of ONE off-diagonal
entry (row, col) at a chosen table degree, into its own module subtree

    ConnesWeilRH/Dev/OffDiagE{row:02d}_{col:02d}/
        C1RouteAComplexPanelTable2655P{000..189}.lean
        C1RouteAComplexPanelAnalytic2656P{...}.lean
        C1RouteAAmpPin2657P{...}.lean
        C1RouteAPhasePin2658P{...}.lean
        C1RouteAPanelTrueBall2662P{...}.lean
    C1RouteAOffDiagEntry2664E{row:02d}_{col:02d}.lean   (umbrella)

under namespace prefix `ConnesWeilRH.Dev.OffDiagE{row:02d}_{col:02d}`.
The five renderers are the byte-regression-gated functions of the (0,3)
lane (check_generator_legacy_bytes_2664.py: 25/25 byte-identical); entry
mode differs only by (beta, psi, degree, node literals, namespace/import
scoping), all asserted by exact token counts.

Default mode is DRY: render everything in memory, compare against any
existing files, report drift and exit nonzero on mismatch.  `--emit`
writes the tree (and the umbrella) plus results/2664_entry_{row}_{col}.json.

No Lean build, no containment claim, no producer GO, no RH.
"""

import hashlib
import json
import re
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
RECORD = 2664

# English-word name infixes for the column-scoped tie-theorem names; the
# template spells column 3 as `three`, so this map keeps the rendered (29,3)
# lane byte-identical while every other column gets a truthful name.
COL_WORDS = ("zero", "one", "two", "three", "four", "five", "six", "seven",
             "eight", "nine", "ten", "eleven", "twelve", "thirteen",
             "fourteen", "fifteen", "sixteen", "seventeen", "eighteen",
             "nineteen", "twenty", "twenty_one", "twenty_two",
             "twenty_three", "twenty_four", "twenty_five", "twenty_six",
             "twenty_seven", "twenty_eight", "twenty_nine")

# template literals of the trueball module C1RouteAPanelTrueBall2662P094
TEMPLATE_MOD = F(5524291025718029, 140737488355328)
TEMPLATE_WIDTH = F(5224175567749775, 2251799813685248)


def spell(frac):
    """Exact dyadic fraction as the double-wrapped `((num : ℝ) / den)`."""
    return f"(({frac.numerator} : ℝ) / {frac.denominator})"


def vector_elements(text, name):
    """Split the `![...]` literal of `def <name> : Fin 30 → ℝ :=` at depth-0
    commas; returns the 30 element spellings verbatim."""
    m = re.search(rf"def {name} : Fin 30 → ℝ :=\s*\n\s*!\[(.*?)\]\s*\n",
                  text, re.S)
    assert m, name
    body = m.group(1)
    elems, depth, cur = [], 0, ""
    for ch in body:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            elems.append(cur.strip())
            cur = ""
        else:
            cur += ch
    elems.append(cur.strip())
    assert len(elems) == 30, len(elems)
    return elems


def rational_spelling_value(t):
    """Exact Fraction of a capture-module element spelling:
    `((num : ℝ) / den)` or `(num : ℝ)`."""
    t = t.strip()
    assert t.startswith("(") and t.endswith(")"), t
    inner = t[1:-1].strip()
    if "/" in inner:
        m = re.fullmatch(r"\((-?\d+)\s*:\s*ℝ\)\s*/\s*(\d+)", inner)
        assert m, t
        return F(int(m.group(1)), int(m.group(2)))
    m = re.fullmatch(r"(-?\d+)\s*:\s*ℝ", inner)
    assert m, t
    return F(int(m.group(1)))


def single_wrapped(el):
    """Drop the capture module's outer parens from a fraction element; a bare
    `(c : ℝ)` element is kept verbatim (it has no fraction to unwrap)."""
    inner = el.strip()[1:-1].strip()
    return el.strip()[1:-1] if "/" in inner else el.strip()


def column_slots(col, capture):
    """Column-scoped trueball slots from the committed capture module and the
    capture JSON: the single-wrapped literal spellings, the value-driven
    template-retention flags, and the word infix."""
    cap_src = (ROOT / "ConnesWeilRH/Dev/"
               "C1RouteACorrectionCaptureParameters2584.lean").read_text(
        encoding="utf-8")
    mod_el = vector_elements(cap_src, "capturedModulations2584")[col]
    wid_el = vector_elements(cap_src, "capturedWidth2584")[col]
    mod_val = rational_spelling_value(mod_el)
    wid_val = rational_spelling_value(wid_el)
    # wire tie to the pricing capture (hex floats -> exact Fractions)
    assert mod_val == F(float.fromhex(capture["families_hex"][col][1])), \
        (col, mod_val)
    assert wid_val == F(float.fromhex(capture["families_hex"][col][0])), \
        (col, wid_val)
    return {"mod_lit": single_wrapped(mod_el),
            "width_lit": single_wrapped(wid_el),
            "mod_keep": mod_val == TEMPLATE_MOD,
            "width_keep": wid_val == TEMPLATE_WIDTH,
            "col_word": COL_WORDS[col]}


def entry_modules(tag):
    return {"amp": f"C1RouteAAmpPin2657P{tag}",
            "phase": f"C1RouteAPhasePin2658P{tag}",
            "table": f"C1RouteAComplexPanelTable2655P{tag}",
            "analytic": f"C1RouteAComplexPanelAnalytic2656P{tag}"}


def render_entry(row, col, degree):
    """Render the full entry tree in memory, in dependency order."""
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text()
    )["owner_capture"]
    params = P.entry_parameters(capture, row, col)
    cslots = column_slots(col, capture)
    prefix = f"ConnesWeilRH.Dev.OffDiagE{row:02d}_{col:02d}"
    outdir = ROOT / "ConnesWeilRH" / "Dev" / f"OffDiagE{row:02d}_{col:02d}"

    node_re = F(float.fromhex(capture["nodes_hex"][row][0]))
    node_im = F(float.fromhex(capture["nodes_hex"][row][1]))

    files = {}
    reports = {"tables": [], "analytic": [], "amp": [], "phase": [],
               "trueball": []}

    for k in range(190):
        tag = f"{k:03d}"
        src, rep = T.render_panel(k, params, degree, prefix)
        files[f"C1RouteAComplexPanelTable2655P{tag}.lean"] = src
        reports["tables"].append(rep)

    for k in range(190):
        tag = f"{k:03d}"
        src, rep = A.render_panel(k, prefix)
        files[f"C1RouteAComplexPanelAnalytic2656P{tag}.lean"] = src
        reports["analytic"].append(rep)

    vacuous = {r["panel"] for r in reports["analytic"]
               if F(r["var"]) >= 1}

    for k in range(190):
        tag = f"{k:03d}"
        src, rep = M.render_panel(k, params, vacuous, prefix)
        files[f"C1RouteAAmpPin2657P{tag}.lean"] = src
        reports["amp"].append(rep)

    for k in range(190):
        tag = f"{k:03d}"
        src, rep = H.render_panel(k, params["psi"], prefix)
        files[f"C1RouteAPhasePin2658P{tag}.lean"] = src
        reports["phase"].append(rep)

    return params, prefix, outdir, files, reports, vacuous, node_re, node_im, \
        cslots


def render_trueball(outdir, row, col, prefix, files, reports,
                    node_re, node_im, cslots):
    """Second stage: the trueball renderer reads the four family modules
    from the entry directory, so the first four families must be on disk
    (or staged) before this stage runs."""
    for k in range(190):
        tag = f"{k:03d}"
        ctx = {"row": row, "col": col, "prefix": prefix, "dev": str(outdir),
               "node_re_lit": spell(node_re), "node_im_lit": spell(node_im),
               "modules": entry_modules(tag)}
        ctx.update(cslots)
        src, _ = TP.render(k, entry=ctx)
        files[f"C1RouteAPanelTrueBall2662P{tag}.lean"] = src
        reports["trueball"].append({"panel": k, "tag": tag})
    return files


def umbrella_text(prefix, row, col):
    imports = "\n".join(
        f"import {prefix}.C1RouteA{fam}P{k:03d}"
        for fam in ("ComplexPanelTable2655", "ComplexPanelAnalytic2656",
                    "AmpPin2657", "PhasePin2658", "PanelTrueBall2662")
        for k in range(190))
    return f"""{imports}

namespace {prefix}

/-!
# Entry ({row}, {col}) five-family panel chain (record {RECORD})

Umbrella for the entry-scoped generation: 190 tables + 190 analytic
containments + 190 amplitude pins + 190 rotation pins + 190 true panel
balls.  Data and per-panel certificate layers only: no partition sum, no
entry containment, no producer GO.
-/

end {prefix}
"""


def main():
    args = sys.argv[1:]
    row = col = None
    degree = 55
    emit = False
    out_name = None
    for a in args:
        if a == "--emit":
            emit = True
        elif a.startswith("--row="):
            row = int(a.split("=", 1)[1])
        elif a.startswith("--col="):
            col = int(a.split("=", 1)[1])
        elif a.startswith("--degree="):
            degree = int(a.split("=", 1)[1])
        elif a.startswith("--out="):
            out_name = a.split("=", 1)[1]
        else:
            raise SystemExit(f"unknown argument {a}")
    if row is None or col is None or row == col:
        raise SystemExit("usage: gen_2664_entry.py --row=R --col=C "
                         "[--degree=D] [--out=NAME.json] [--emit]")
    out_name = out_name or f"2664_entry_{row}_{col}.json"

    params, prefix, outdir, files, reports, vacuous, node_re, node_im, \
        cslots = render_entry(row, col, degree)

    # trueball needs the four families on disk: stage them into the real
    # directory when emitting; in dry mode stage into a temp under outdir
    # is not possible without writing, so dry mode requires the files to
    # exist already OR --emit.  Keep the rule simple and explicit.
    if not emit:
        missing = [name for name in files if not (outdir / name).exists()]
        if missing:
            raise SystemExit(
                f"dry mode: {len(missing)} of {len(files)} files not yet "
                f"emitted ({missing[0]}...); run --emit first")
        render_trueball(outdir, row, col, prefix, files, reports,
                        node_re, node_im, cslots)
        drifted = [name for name in files
                   if (outdir / name).read_text(encoding="utf-8") != files[name]]
        umb = umbrella_text(prefix, row, col)
        umb_name = f"C1RouteAOffDiagEntry{RECORD}E{row:02d}_{col:02d}.lean"
        umb_ok = ((ROOT / "ConnesWeilRH" / "Dev" / umb_name).exists()
                  and (ROOT / "ConnesWeilRH" / "Dev" / umb_name).read_text(
                      encoding="utf-8") == umb)
        print(f"dry: {len(files) - len(drifted)}/{len(files)} byte-stable; "
              f"umbrella stable: {umb_ok}")
        if drifted:
            for name in drifted[:5]:
                print("DRIFT", name)
            return 1
        return 0 if umb_ok else 1

    # ---- emit mode: four families to disk, then trueball, then umbrella ----
    outdir.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (outdir / name).write_text(src, encoding="utf-8", newline="\n")
    # the trueball renderer reads the four family modules from outdir
    render_trueball(outdir, row, col, prefix, files, reports,
                    node_re, node_im, cslots)
    for name in [n for n in files if n.startswith("C1RouteAPanelTrueBall")]:
        (outdir / name).write_text(files[name], encoding="utf-8", newline="\n")
    umb_name = f"C1RouteAOffDiagEntry{RECORD}E{row:02d}_{col:02d}.lean"
    (ROOT / "ConnesWeilRH" / "Dev" / umb_name).write_text(
        umbrella_text(prefix, row, col), encoding="utf-8", newline="\n")

    scripts = {"gen_2664_entry.py": Path(__file__).resolve()}
    for mod in (P, T, A, M, H, TP):
        f = mod.__file__
        assert f is not None, mod
        scripts[Path(f).name] = Path(f)
    umb_text = umbrella_text(prefix, row, col)
    modules_sha256 = {name: hashlib.sha256(src.encode("utf-8")).hexdigest()
                      for name, src in sorted(files.items())}
    modules_sha256[umb_name] = hashlib.sha256(
        umb_text.encode("utf-8")).hexdigest()
    payload = {
        "record": RECORD,
        "purpose": "trial entry generation: full five-family per-panel "
                   "chain for one off-diagonal entry of the moment matrix",
        "entry": [row, col], "prefix": prefix, "degree": degree,
        "radius_exact": str(params["radius"]),
        "beta_exact": str(params["beta"]), "psi_exact": str(params["psi"]),
        "abs_beta_float": float(abs(params["beta"])),
        "vacuous_panels": sorted(vacuous),
        "panel_count": 190,
        "module_count": len(files) + 1,
        "umbrella_module": umb_name,
        "generator_sha256": {name: hashlib.sha256(p.read_bytes()).hexdigest()
                             for name, p in scripts.items()},
        "modules_sha256": modules_sha256,
        "byte_policy": "entry chains are regenerated deterministically and "
                       "byte-pinned by this manifest; one chain is ~160-212 MB "
                       "so the batch is not byte-committed (record 2664 byte "
                       "wall: 869 entries ~ 137-184 GB > 123 GB free disk and "
                       "~450x the repo pack)",
        "capture_sha256": hashlib.sha256(
            (ROOT / "results/2275_gap_owner_audit.json").read_bytes()
        ).hexdigest(),
        "tables": reports["tables"], "analytic": reports["analytic"],
        "amp": reports["amp"], "phase": reports["phase"],
        "lean_built": False, "membership_claimed": False,
        "producer_go": False, "rh_claim": False,
    }
    (ROOT / "results" / out_name).write_text(
        json.dumps(payload, indent=1) + "\n", encoding="utf-8", newline="\n")
    print(f"emitted {len(files)} modules + umbrella into {outdir.name}; "
          f"payload results/{out_name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())