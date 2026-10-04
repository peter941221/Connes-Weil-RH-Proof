"""Generate cell 2703 and an adjacent two-cell correction second-chord span."""
from fractions import Fraction as Q
import hashlib
import json
import re

import generate_node_exp_owner_2577 as owner
from generate_second_chord_cell_2575 import STEP, real, side_name
from generate_signed_cells_2558 import Cell, endpoint
from validate_adaptive_nodes_2542 import scalar_def
from format_lean_source_2553 import wrap_source

ROOT, DEV = owner.ROOT, owner.DEV
CELL = 2703
ASSEMBLY = "C1RouteACorrectionSecondChordCell2703_2579"
SPAN = "C1RouteACorrectionSecondChordSpan2702_2579"
AUDIT = SPAN + "Audit"


def fourth_module(sign):
    return Cell(CELL, sign).module("Fourth")


def render_fourth(sign):
    source = Cell(CELL, sign).render_fourth()
    for index in (CELL, CELL + 1):
        old_prefix, old_record, old_module = endpoint(index, sign)
        parent = owner.names(index, sign)
        source = source.replace(old_module, parent["module"])
        source = source.replace(old_prefix + "Position" + str(old_record),
                                parent["point"] + "Position2577")
    return wrap_source(source)


def correction_fourth(sign):
    source = (DEV / (fourth_module(sign) + ".lean")).read_text(encoding="utf-8")
    rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    total = Q(0)
    for index, row in enumerate(rows):
        box = row["ideal_correction_coefficient"]
        center = [(Q(box[part]["lower_exact"]) + Q(box[part]["upper_exact"])) / 2
                  for part in ("real", "imag")]
        upper = scalar_def(source, Cell(CELL, sign).prefix + f"FourthP{index:03d}Upper2558")
        total += (sum(abs(value) for value in center) + Q(1, 10**28)) * upper
    return total


def endpoint_upper(index, sign):
    naming = owner.names(index, sign, 2)
    source = (DEV / (naming["bounds"] + ".lean")).read_text(encoding="utf-8")
    return scalar_def(source, naming["signed"] + "Upper2577")


def replace_definition(source, name, value):
    marker = f"noncomputable def {name} : ℝ :="
    start = source.index(marker)
    end = source.index("\n\n", start)
    return source[:start] + marker + " " + real(value) + source[end:]


def assembly_source():
    source = (DEV / "C1RouteACorrectionSecondChordCell2702_2578.lean").read_text(encoding="utf-8")
    source = re.sub(r"(nodeJet2N|C1RouteANodeJet2N)0270([23])",
                    lambda match: match[1] + "0270" + str(int(match[2]) + 1), source)
    source = source.replace("batchC02702", "batchC02703").replace("C1RouteABatchC02702", "C1RouteABatchC02703")
    for sign in (-1, 1):
        side = side_name(sign)
        for old, index in ((f"batchN02702{side}Position2558", CELL),
                           (f"batchN02703{side}Position2558", CELL + 1)):
            source = source.replace(old, owner.names(index, sign)["point"] + "Position2577")
    source = source.replace("neighborRightPosition2557", owner.names(CELL, 1)["point"] + "Position2577")
    source = source.replace("import ConnesWeilRH.Dev.C1RouteANeighborRight2557\n", "")
    source = re.sub(r"\b270[23]\b", lambda match: str(int(match[0]) + 1), source)
    source = source.replace("2578", "2579").replace("Cell2702_2579", "Cell2703_2579")
    for sign in (-1, 1):
        prefix = f"nodeSecondChord{side_name(sign)}2579"
        fourth = correction_fourth(sign)
        upper = STEP / 2 * (endpoint_upper(CELL, sign) + endpoint_upper(CELL + 1, sign)) + fourth * STEP**3 / 12
        source = replace_definition(source, prefix + "FourthUpper", fourth)
        source = replace_definition(source, prefix + "Upper", upper)
    assert "02702" not in source and "2578" not in source
    return wrap_source(source)


def span_source():
    parts = [f"import ConnesWeilRH.Dev.{ASSEMBLY}\n",
             "import ConnesWeilRH.Dev.C1RouteACorrectionSecondChordCell2702_2578\n\n",
             "namespace ConnesWeilRH.Dev\n\nopen MeasureTheory\n\n"]
    for sign in (-1, 1):
        side = side_name(sign)
        sigma = "(-1/2)" if sign < 0 else "(1/2)"
        positions = [owner.names(index, sign, 2)["point"] + "Position2577" for index in (2702, 2703, 2704)]
        left, middle, right = positions
        parts.append(f"""
theorem nodeSecondChord{side}Span2579Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in {left}..{right},
      ‖iteratedDeriv 2 (weightedPhysical2539 {sigma} coefficients nodeModulation2541) position‖) ≤
        nodeSecondChord{side}2578Upper + nodeSecondChord{side}2579Upper := by
  have hcont : Continuous (fun position =>
      ‖iteratedDeriv 2 (weightedPhysical2539 {sigma} coefficients nodeModulation2541) position‖) :=
    (ContDiff.differentiable_iteratedDeriv' 2
      ((weightedPhysical2539_contDiff {sigma} coefficients nodeModulation2541).of_le
        (by decide))).continuous.norm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable {left} {middle})
    (hcont.intervalIntegrable {middle} {right})]
  exact add_le_add (nodeSecondChord{side}2578Integral_le coefficients herror)
    (nodeSecondChord{side}2579Integral_le coefficients herror)
""")
    parts.append("\nend ConnesWeilRH.Dev\n")
    return wrap_source("".join(parts))


def emit(module, source, outputs):
    path = DEV / (module + ".lean")
    if path.exists():
        assert path.read_bytes() == source.encode(), f"Refusing to overwrite differing source: {module}"
    else:
        path.write_text(source, encoding="utf-8", newline="\n")
    outputs[str(path.relative_to(ROOT))] = hashlib.sha256(source.encode()).hexdigest()


def main():
    outputs, readings = {}, []
    for sign in (-1, 1):
        naming, raw, active = owner.standalone(CELL + 1, sign, 2)
        parent = owner.names(CELL + 1, sign)
        parent_source = owner.owner_source(CELL + 1, sign, raw)
        emit(parent["module"], parent_source, outputs)
        emit(naming["module"], owner.shared_source(CELL + 1, sign, 2, raw, parent_source), outputs)
        bounds, upper, charge = owner.signed_source(CELL + 1, sign, raw)
        emit(naming["bounds"], bounds, outputs)
        emit(fourth_module(sign), render_fourth(sign), outputs)
        readings.append(dict(sign=sign, active=active, endpoint_upper=str(upper), rounding_charge=str(charge)))
    emit(ASSEMBLY, assembly_source(), outputs)
    emit(SPAN, span_source(), outputs)
    targets = []
    for sign in (-1, 1):
        for index in (CELL, CELL + 1):
            naming = owner.names(index, sign, 2)
            parent = owner.names(index, sign)
            targets += [parent["point"] + f"P{family:03d}BaseError2577" for family in range(30)]
            targets += [naming["point"] + f"P{family:03d}DerivativeError2577" for family in range(30)]
            targets += [naming["signed"] + "Upper_le2577", naming["point"] + "Grid2577"]
        targets += [Cell(CELL, sign).prefix + "FourthBound2558"]
        targets += [f"nodeSecondChord{side_name(sign)}2579" + suffix
                    for suffix in ("Fourth_bound", "Fourth_eq", "Summand_le", "ProductionSummand_le", "Integral_le")]
        targets += [f"nodeSecondChord{side_name(sign)}Span2579Integral_le"]
    audit = f"import ConnesWeilRH.Dev.{SPAN}\n\n" + "\n".join(
        "#print axioms ConnesWeilRH.Dev." + target for target in targets) + "\n"
    emit(AUDIT, audit, outputs)
    payload = dict(record=2579, cell=CELL, span_cells=[2702, 2703], new_node=2704,
                   generated_orders=[2], rows=readings, output_sha256=outputs, audit_targets=targets,
                   full_grid_certificate=False, exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    inputs = [owner.CAPTURE, ROOT / "results/2338_exact_interpolation_repair.json",
              DEV / "C1RouteACorrectionSecondChordCell2702_2578.lean",
              DEV / "C1RouteANodeJet2N02703MinusBounds2577.lean",
              DEV / "C1RouteANodeJet2N02703PlusBounds2577.lean"]
    inputs += [ROOT / "scripts" / name for name in (
        "generate_second_chord_span_2579.py", "generate_node_exp_owner_2577.py",
        "generate_signed_cells_2558.py", "generate_boundary_fourth_2550.py",
        "generate_boundary_jets_2548.py", "generate_signed_midpoint_2543.py",
        "generate_correction_pair_2570.py", "format_lean_source_2553.py")]
    payload["input_sha256"] = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in inputs}
    (ROOT / "results/2579_second_chord_generation.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("SECOND_CHORD_SPAN_GENERATED", len(outputs), len(targets), flush=True)


if __name__ == "__main__":
    main()
