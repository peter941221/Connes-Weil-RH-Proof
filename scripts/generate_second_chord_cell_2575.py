"""Generate a same-owner second-chord cell certificate at both signs.

The committed arbitrary-position/order jet renderer supplies endpoint order-2
leaves. The signed midpoint renderer is reused as an order-2 point renderer,
with the accepted correction-owner derivation and runtime-token guards.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

from generate_complex_exp_node_2541 import ROOT, CAPTURE, real
from generate_boundary_jets_2548 import render as render_jets
from generate_signed_cells_2558 import Cell
from generate_correction_pair_2570 import (
    CENTER_SWAPS, derive_generator, finalize_correction, rename)
from format_lean_source_2553 import wrap_source
from validate_adaptive_nodes_2542 import scalar_def

RECORD = 2575
CELL = 2700
RADIUS = Q(65536001, 10 ** 7)
STEP = 2 * RADIUS / 10240
ERROR = Q(1, 10 ** 28)
DEV = ROOT / "ConnesWeilRH/Dev"
ASSEMBLY = "C1RouteACorrectionSecondChordCell2700_2575"


def side_name(sign):
    assert sign in (-1, 1)
    return "Plus" if sign > 0 else "Minus"


def point_names(index, sign):
    stem = f"CorrSecondN{index:05d}{side_name(sign)}"
    prefix = stem[0].lower() + stem[1:]
    return dict(prefix=prefix, point=prefix + "Point", signed=prefix + "Signed",
                deriv="C1RouteA" + stem + "Derivatives2575",
                bounds="C1RouteA" + stem + "Bounds2575")


def regression():
    names = []
    for index, sign in ((2700, -1), (2701, -1), (2700, 1)):
        cell = Cell(index, sign)
        for part, render in (("Midpoint", cell.render_midpoint),
                             ("MidpointBounds", lambda: cell.render_midpoint_bounds()[0])):
            module = cell.module(part)
            assert render().encode() == (DEV / (module + ".lean")).read_bytes(), module
            names.append(module)
    return names


def render_point(index, sign):
    names = point_names(index, sign)
    raw, active = render_jets("Midpoint", grid_order=(Q(index), 2),
                              sigma=Q(sign, 2), paired=True)
    raw = wrap_source(rename(raw, "edgeMidpoint", 2548, names["point"], RECORD)
                      .replace(":= by cbv", ":= by decide +kernel"))
    input_source = rename(raw, names["point"], RECORD, "midpoint", 2543)
    derived = derive_generator(ROOT / "scripts/generate_signed_midpoint_2543.py", CENTER_SWAPS)
    bounds, upper, charge = derived["render"](source=input_source, sigma=Q(sign, 2))
    bounds = bounds.replace("C1RouteAMidpointDerivatives2543", names["deriv"])
    bounds = rename(bounds, "midpoint", 2543, names["point"], RECORD)
    bounds = rename(bounds, "signedMidpoint", 2543, names["signed"], RECORD)
    bounds = bounds.replace("weightedPhysical_second_midpoint_le2543",
                            names["prefix"] + "Physical2575")
    bounds = wrap_source(finalize_correction(bounds))
    assert "baseCoefficient" not in bounds
    expected_sign = "(-1/2)" if sign < 0 else "(1/2)"
    assert expected_sign in bounds
    assert ("(1/2)" if sign < 0 else "(-1/2)") not in bounds.replace(expected_sign, "SIGMA")
    position = scalar_def(raw, names["point"] + "Position2575")
    assert position == -RADIUS + index * STEP
    return names, raw, bounds, dict(index=index, sign=sign, position=str(position),
                                   active=active, upper=str(upper), rounding_charge=str(charge))


def fourth_price(sign):
    parent = f"batchC02700{side_name(sign)}Fourth"
    source = (DEV / f"C1RouteABatchC02700{side_name(sign)}Fourth2558.lean").read_text()
    rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    total = Q(0)
    for index, row in enumerate(rows):
        box = row["ideal_correction_coefficient"]
        center = [(Q(box[part]["lower_exact"]) + Q(box[part]["upper_exact"])) / 2
                  for part in ("real", "imag")]
        upper = scalar_def(source, parent + f"P{index:03d}Upper2558")
        total += (sum(abs(value) for value in center) + ERROR) * upper
    return total


def assembly_source(readings):
    imports = ["C1RouteACorrectionSecondChord2574"]
    imports += [point_names(index, sign)["bounds"]
                for sign in (-1, 1) for index in (CELL, CELL + 1)]
    imports += [f"C1RouteABatchC02700{side_name(sign)}Fourth2558" for sign in (-1, 1)]
    parts = ["\n".join("import ConnesWeilRH.Dev." + module for module in imports),
             "\n\nnamespace ConnesWeilRH.Dev\n\nopen scoped BigOperators\nopen MeasureTheory\n",
             "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n",
             "open ConnesWeilRH.Source.C1RouteAItem5Arithmetic\n\n"]
    cell_rows = []
    for sign in (-1, 1):
        side = side_name(sign)
        sigma = "(-1/2)" if sign < 0 else "(1/2)"
        prefix = f"corrSecondChord{side}2575"
        parent = f"batchC02700{side}Fourth"
        left_names = point_names(CELL, sign)
        right_names = point_names(CELL + 1, sign)
        left = left_names["point"] + "Position2575"
        right = right_names["point"] + "Position2575"
        left_upper = left_names["signed"] + "Upper2575"
        right_upper = right_names["signed"] + "Upper2575"
        fourth = fourth_price(sign)
        endpoints = [Q(row["upper"]) for row in readings if row["sign"] == sign]
        total = STEP / 2 * sum(endpoints) + fourth * STEP ** 3 / 12
        cell_rows.append(dict(sign=sign, fourth_upper=str(fourth),
                              endpoint_piece=str(STEP / 2 * sum(endpoints)),
                              remainder_piece=str(fourth * STEP ** 3 / 12),
                              cell_upper=str(total)))
        fourth_literals = ",\n      ".join(parent + f"P{index:03d}Upper2558" for index in range(30))
        parts.append(f"""
noncomputable def {prefix}FourthL1 : ℝ :=
  ∑ index : Fin 30, (|(correctionCoefficientCenter2570 index).re| +
    |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index) *
    {parent}Upper2558 index

noncomputable def {prefix}FourthUpper : ℝ := {real(fourth)}

noncomputable def {prefix}Upper : ℝ := {real(total)}

theorem {prefix}Fourth_bound :
    signedFourthCellUpper2574 {sigma} correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 {left} {right} ≤
        {prefix}FourthL1 := by
  have hleft : {left} = kernelN02700{side}Position2555 := by
    norm_num [{left}, kernelN02700{side}Position2555]
  have hright : {right} = kernelN02701{side}Position2555 := by
    norm_num [{right}, kernelN02701{side}Position2555]
  unfold signedFourthCellUpper2574 {prefix}FourthL1
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro index _
  have hnorm := Complex.norm_le_abs_re_add_abs_im (correctionCoefficientCenter2570 index)
  have hunit : weightedUnitFourthCellUpper2574 {sigma} (nodeModulation2541 index)
      (storedWidth index ^ 2) kernelN02700{side}Position2555
        kernelN02701{side}Position2555 ≤ {parent}Upper2558 index := by
    exact {parent}Bound2558 index
  have hnonneg := weightedUnitFourthCellUpper_nonneg2574 {sigma}
    (nodeModulation2541 index) (pow_pos (storedWidth_pos index) 2)
    (left := kernelN02700{side}Position2555) (right := kernelN02701{side}Position2555)
  have hcoefficient : ‖correctionCoefficientCenter2570 index‖ +
      correctionCoefficientError2570 index ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_le_add hnorm le_rfl
  have hcharge : 0 ≤ |(correctionCoefficientCenter2570 index).re| +
      |(correctionCoefficientCenter2570 index).im| + correctionCoefficientError2570 index :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num [correctionCoefficientError2570])
  exact mul_le_mul hcoefficient hunit hnonneg hcharge

theorem {prefix}Fourth_eq :
    {prefix}FourthL1 = {prefix}FourthUpper := by
  unfold {prefix}FourthL1
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
    correctionCoefficientError2570, {parent}Upper2558, {prefix}FourthUpper,
    {fourth_literals}]

theorem {prefix}Summand_le :
    {real(STEP)} / 2 * (signedJetUpper2539 2 {sigma} correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 {left} +
      signedJetUpper2539 2 {sigma} correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 {right}) +
    signedFourthCellUpper2574 {sigma} correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541 {left} {right} *
        {real(STEP)} ^ 3 / 12 ≤ {prefix}Upper := by
  calc
    _ ≤ {real(STEP)} / 2 * ({left_upper} + {right_upper}) +
        {prefix}FourthL1 * {real(STEP)} ^ 3 / 12 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (add_le_add {left_names['signed']}Upper_le2575
            {right_names['signed']}Upper_le2575) (by norm_num)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right {prefix}Fourth_bound (by norm_num)) (by norm_num)
    _ = {prefix}Upper := by
      rw [{prefix}Fourth_eq]
      norm_num [{left_upper}, {right_upper}, {prefix}FourthUpper, {prefix}Upper]


theorem {prefix}ProductionSummand_le :
    (2 * stripRadius2303 / 10240) / 2 *
      (signedJetUpper2539 2 {sigma} correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240)) +
       signedJetUpper2539 2 {sigma} correctionCoefficientCenter2570
        correctionCoefficientError2570 nodeModulation2541
          (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240))) +
    signedFourthCellUpper2574 {sigma} correctionCoefficientCenter2570
      correctionCoefficientError2570 nodeModulation2541
        (-stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240))
        (-stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240)) *
        (2 * stripRadius2303 / 10240) ^ 3 / 12 ≤ {prefix}Upper := by
  have hleft : -stripRadius2303 + 2700 * (2 * stripRadius2303 / 10240) = {left} := by
    norm_num [stripRadius2303, {left}]
  have hright : -stripRadius2303 + 2701 * (2 * stripRadius2303 / 10240) = {right} := by
    norm_num [stripRadius2303, {right}]
  have hstep : 2 * stripRadius2303 / 10240 = {real(STEP)} := by norm_num [stripRadius2303]
  rw [hleft, hright, hstep]
  exact {prefix}Summand_le

theorem {prefix}Integral_le (coefficients : Fin 30 → ℂ)
    (herror : ∀ index, ‖coefficients index - correctionCoefficientCenter2570 index‖ ≤
      correctionCoefficientError2570 index) :
    (∫ position in {left}..{right},
      ‖iteratedDeriv 2 (weightedPhysical2539 {sigma} coefficients nodeModulation2541) position‖) ≤
        {prefix}Upper := by
  have horder : {left} < {right} := by norm_num [{left}, {right}]
  have hwidth : {right} - {left} = {real(STEP)} := by norm_num [{left}, {right}]
  have h := weightedPhysical2539_second_norm_integral_le_chord2574 {sigma} coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541 herror horder
  rw [hwidth] at h
  exact h.trans {prefix}Summand_le
""")
    parts.append("\nend ConnesWeilRH.Dev\n")
    return wrap_source("".join(parts)), cell_rows


def main():
    regressions = regression()
    outputs = {}
    readings = []
    for sign in (-1, 1):
        for index in (CELL, CELL + 1):
            names, raw, bounds, reading = render_point(index, sign)
            outputs[names["deriv"]] = raw
            outputs[names["bounds"]] = bounds
            readings.append(reading)
    assembly, cell_rows = assembly_source(readings)
    outputs[ASSEMBLY] = assembly
    audit_names = []
    for sign in (-1, 1):
        for index in (CELL, CELL + 1):
            names = point_names(index, sign)
            audit_names += [names["point"] + f"P{family:03d}DerivativeError2575" for family in range(30)]
            audit_names.append(names["point"] + "Grid2575")
            audit_names += [names["signed"] + suffix + "2575" for suffix in
                            ("ExpError", "Sum_eq", "Charge", "Upper_le")]
            audit_names.append(names["prefix"] + "Physical2575")
        audit_names += [f"corrSecondChord{side_name(sign)}2575" + suffix
                        for suffix in ("Fourth_bound", "Fourth_eq", "Summand_le",
                                       "ProductionSummand_le", "Integral_le")]
    audit = "import ConnesWeilRH.Dev." + ASSEMBLY + "\n\n"
    audit += "\n".join("#print axioms ConnesWeilRH.Dev." + name for name in audit_names) + "\n"
    outputs[ASSEMBLY + "Audit"] = audit
    for module, source in outputs.items():
        (DEV / (module + ".lean")).write_text(source, encoding="utf-8", newline="\n")
    result = dict(record=2575, cell=CELL, status="SECOND_CHORD_CELL_GENERATED",
                  coefficient_owner="ideal_correction_coefficient", error=str(ERROR),
                  regression_modules=regressions, endpoint_rows=readings, cell_rows=cell_rows,
                  audit_targets=audit_names, modules=list(outputs),
                  generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  input_sha256={str(path.relative_to(ROOT)):
                                hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (CAPTURE, ROOT /
                                  "results/2338_exact_interpolation_repair.json")},
                  source_sha256={str((DEV / (module + ".lean")).relative_to(ROOT)):
                                 hashlib.sha256(source.encode()).hexdigest()
                                 for module, source in outputs.items()},
                  full_grid_certificate=False, exact_coefficient_membership=False,
                  producer_go=False, rh_claim=False)
    path = ROOT / "results/2575_second_chord_generation.json"
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(dict(status=result["status"], cells=cell_rows,
                         endpoints=readings, regressions=regressions)), flush=True)


if __name__ == "__main__":
    main()
