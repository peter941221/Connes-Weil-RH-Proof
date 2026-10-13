"""Generate the first new 2048-grid cell bridge (cell 1024, base M0).

The source artifact is record 2687.  This generator reuses the audited
analytic proof templates from records 2676-2678, but replaces the cell-local
right endpoint and all outward-rounded rectangles with the record-2687
cell-1024 values.  It emits only the phi/trigonometric family lemmas needed by
the actual-owner base-M0 bridge.
"""

from __future__ import annotations

import json
import re
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2687_repaired_owner_2048_grid_screen.json"
CALC = ROOT / "scripts/routea_cell4096_containment_2676.py"
FAMILY_TEMPLATE = ROOT / "ConnesWeilRH/Dev/C1RouteACellContainment2677Family0.lean"
OWNER_TEMPLATE = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2678.lean"
OUT = ROOT / "ConnesWeilRH/Dev"
SHARED = OUT / "C1RouteARepairedOwnerCell2688Shared.lean"

CELL_INDEX = 1024
CELL_RIGHT = "0x3f7a36e2eb1c4400"


def load_calc():
    import importlib.util
    spec = importlib.util.spec_from_file_location("routea_calc_2688", CALC)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CALC}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rat(value: Fraction) -> str:
    return f"(({value.numerator} : ℚ) / ({value.denominator} : ℚ) : ℝ)"


def interval_def(name: str, values: tuple[Fraction, Fraction]) -> str:
    return (
        f"noncomputable def {name} : RealInterval2429 :=\n"
        f"  {{ lo := {rat(values[0])}\n"
        f"    hi := {rat(values[1])} }}\n\n"
    )


def replace_interval(source: str, name: str, values: tuple[Fraction, Fraction]) -> str:
    pattern = re.compile(
        rf"noncomputable def {name} : RealInterval2429 :=.*?\n\n", re.DOTALL
    )
    updated, count = pattern.subn(interval_def(name, values), source, count=1)
    if count != 1:
        raise RuntimeError(f"missing interval definition {name}")
    return updated


def orient_positive(source: str, family: int) -> str:
    old = '''  have hangleEq : angle = -(|theta| * right) := by
    dsimp [angle]
    rw [abs_of_neg htheta]
    ring
  have hdelta : (0 - angle) ^ 2 / 8 ≤ delta := by
    rw [hangleEq]
    dsimp [delta]
    nlinarith [sq_nonneg (|theta| * right)]
  have hangleNeg : angle < 0 := mul_neg_of_neg_of_pos htheta hright
  have hxRight : x ≤ right := by simpa [right] using hx.2
  have hangleLo : angle ≤ theta * x := by
    dsimp [angle]
    exact mul_le_mul_of_nonpos_left hxRight htheta.le
  have hangleHi : theta * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    htheta.le hx.1
  have hcosHull := memCosEndpointHullOfBoxes2676
    (a := angle) (x := theta * x) (b := 0) (radius := delta)
    hangleNeg hangleLo hangleHi hcosLeft hcosRight hdelta
  have hsinHull := memSinEndpointHullOfBoxes2676
    (a := angle) (x := theta * x) (b := 0) (radius := delta)
    hangleNeg hangleLo hangleHi hsinLeft hsinRight hdelta'''
    new = '''  have hangleEq : angle = |theta| * right := by
    dsimp [angle]
    rw [abs_of_pos htheta]
  have hdelta : (angle - 0) ^ 2 / 8 ≤ delta := by
    rw [hangleEq]
    dsimp [delta]
    nlinarith [sq_nonneg (|theta| * right)]
  have hanglePos : 0 < angle := mul_pos htheta hright
  have hxRight : x ≤ right := by simpa [right] using hx.2
  have hangleLo : 0 ≤ theta * x := mul_nonneg htheta.le hx.1
  have hangleHi : theta * x ≤ angle := by
    dsimp [angle]
    exact mul_le_mul_of_nonneg_left hxRight htheta.le
  have hcosHull := memCosEndpointHullOfBoxes2676
    (a := 0) (x := theta * x) (b := angle) (radius := delta)
    hanglePos hangleLo hangleHi hcosRight hcosLeft hdelta
  have hsinHull := memSinEndpointHullOfBoxes2676
    (a := 0) (x := theta * x) (b := angle) (radius := delta)
    hanglePos hangleLo hangleHi hsinRight hsinLeft hdelta
  have hsinHullEq :
      endpointHullOfBoxes2676 sinRight sinEndpoint delta =
        endpointHullOfBoxes2676 sinEndpoint sinRight delta := by
    cases sinRight
    cases sinEndpoint
    simp [endpointHullOfBoxes2676, min_comm, max_comm]
  rw [hsinHullEq] at hsinHull'''
    if old not in source:
        raise RuntimeError(f"positive trig geometry block missing for family {family}")
    source = source.replace(old, new, 1)
    source = source.replace("have htheta : theta < 0", "have htheta : 0 < theta", 1)
    source = source.replace(
        "endpointHullOfBoxes2676 cosEndpoint cosRight delta",
        "endpointHullOfBoxes2676 cosRight cosEndpoint delta",
    )
    return source


def orient_zero(source: str, family: int) -> str:
    start = source.index(
        f"set_option maxRecDepth 10000 in\ntheorem record2688Family{family}TrigMem"
    )
    index_name = {5: "5", 6: "6", 7: "7"}.get(family, str(family))
    theorem = f'''theorem record2688Family{family}TrigMem {{x : ℝ}}
    (_hx : x ∈ Set.Icc 0 record2688CellRight) :
    record2688Family{family}CosRect.Mem
        (Real.cos (capturedModulations2584 {family} * x)) ∧
      record2688Family{family}SinRect.Mem
        (Real.sin (capturedModulations2584 {family} * x)) := by
  have hzero : capturedModulations2584 {family} = 0 := by
    norm_num [Matrix.cons_val_{index_name}, Matrix.cons_val_zero, capturedModulations2584]
  constructor
  · rw [hzero, zero_mul, Real.cos_zero]
    norm_num [record2688Family{family}CosRect, RealInterval2429.point, RealInterval2429.Mem]
  · rw [hzero, zero_mul, Real.sin_zero]
    norm_num [record2688Family{family}SinRect, RealInterval2429.point, RealInterval2429.Mem]
'''
    return source[:start] + theorem


def extract_family(source: str, family: int, boxes: dict[str, tuple[Fraction, Fraction]]) -> str:
    """Keep only phi/mid and trig proofs from the family-0 template."""
    source = source.replace("record2675CellRight", "record2688CellRight")
    for suffix, key in (("PhiRect", "phi"), ("CosRect", "cos"), ("SinRect", "sin")):
        source = replace_interval(source, f"record2677Family0{suffix}", boxes[key])

    start = source.index("noncomputable def record2677Family0PhiRect")
    stop_mid = source.index("noncomputable def record2677Family0BaseM0WideRect")
    prefix = source[start:stop_mid]
    trig_start = source.index(
        "set_option maxRecDepth 10000 in\ntheorem record2677Family0TrigMem"
    )
    trig_stop = source.index("\ntheorem record2677Family0BaseM0CellMem", trig_start)
    trig = source[trig_start:trig_stop]

    body = prefix + trig
    body = body.replace("record2677Family0", f"record2688Family{family}")
    for old, new in (
        ("storedWidth 0", f"storedWidth {family}"),
        ("capturedModulations2584 0", f"capturedModulations2584 {family}"),
    ):
        body = body.replace(old, new)
    if family in (2, 3):
        body = orient_positive(body, family)
    elif family in (5, 6, 7):
        body = orient_zero(body, family)
    # Family-specific matrix literals are needed by norm_num for indices >= 5.
    if family >= 5:
        body = body.replace(
            "import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
            "import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n"
            "import ConnesWeilRH.Dev.MatrixConsValFamily2637",
        )
    word = {1: "one", 2: "two", 3: "three", 4: "four"}.get(family, str(family))
    index_simp = (
        "Matrix.cons_val_zero, "
        if family == 0
        else f"Matrix.cons_val_{word}, Matrix.cons_val_zero, "
    )
    body = body.replace("norm_num [", f"norm_num [{index_simp}")
    imports = [
        "import ConnesWeilRH.Dev.C1RouteACellContainment2676",
        "import ConnesWeilRH.Dev.C1RouteACellContainment2677Aggregates",
        "import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
        "import ConnesWeilRH.Dev.C1RouteACorrectionCaptureParameters2584",
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2688Shared",
    ]
    if family >= 5:
        imports.append("import ConnesWeilRH.Dev.MatrixConsValFamily2637")
    return "\n".join(imports) + "\n\nnamespace ConnesWeilRH.Dev\n\n" + \
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n\n" + body + \
        "\nend ConnesWeilRH.Dev\n"


def dyadic_rect(rect: tuple[Fraction, Fraction, Fraction, Fraction]) -> tuple[int, ...]:
    scale = 1 << 160
    result = []
    for i, value in enumerate(rect):
        scaled = value * scale
        if i in (0, 2):
            result.append(scaled.numerator // scaled.denominator)
        else:
            result.append(-((-scaled.numerator) // scaled.denominator))
    return tuple(result)


def rect_literal(values: list[tuple[int, ...]]) -> str:
    lines = ["noncomputable def record2678BaseM0FamilyRects : Fin 30 → ComplexRect2427 :=", "  !["]
    for i, row in enumerate(values):
        suffix = "," if i < len(values) - 1 else "]"
        args = " ".join(f"(({v} : ℚ) / (2 : ℚ) ^ 160 : ℝ)" for v in row)
        lines.append(f"    ComplexRect2427.mk {args}{suffix}")
    return "\n".join(lines) + "\n\n"


def aggregate_defs(values: list[tuple[int, ...]]) -> str:
    totals = [sum(row[i] for row in values) for i in range(4)]
    names = [
        "record2678BaseM0AggregateReLo",
        "record2678BaseM0AggregateReHi",
        "record2678BaseM0AggregateImLo",
        "record2678BaseM0AggregateImHi",
    ]
    out = []
    for name, value in zip(names, totals):
        out += [f"def {name} : ℚ :=", f"  ({value} : ℚ) / (2 : ℚ) ^ 160"]
    return "\n".join(out) + "\n"


def build() -> None:
    calc = load_calc()
    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    row = artifact["cells_data"][CELL_INDEX]
    if row[0] != CELL_INDEX or row[1] != "0x0000000000000000" or row[2] != CELL_RIGHT:
        raise ValueError("record 2687 cell 1024 endpoint bits changed")

    # Use the exact binary64 midpoint owner from the repair artifact.
    repair = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())
    coeffs = []
    for item in repair["coefficient_rows"]:
        real = (Fraction(item["ideal_base_coefficient"]["real"]["lower_exact"]) +
                Fraction(item["ideal_base_coefficient"]["real"]["upper_exact"])) / 2
        imag = (Fraction(item["ideal_base_coefficient"]["imag"]["lower_exact"]) +
                Fraction(item["ideal_base_coefficient"]["imag"]["upper_exact"])) / 2
        coeffs.append(type("Coeff", (), {"real": float(real), "imag": float(imag)})())

    widths = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
    thetas = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
        "capturedModulations2584")
    right = calc.fraction_of_bits(int(CELL_RIGHT, 16))
    per_family = calc.build_chain([], coeffs, coeffs, right, thetas, widths, calc.exp_pins()[2:])
    base_rects = calc.channel_rects(per_family, coeffs)[0]
    base_dyadic = [dyadic_rect(rect) for rect in base_rects]
    exported = tuple(calc.fraction_of_bits(int(v, 16)) for v in row[5][0][:4])
    scale = 1 << 160
    aggregate = tuple(Fraction(sum(box[i] for box in base_dyadic), scale) for i in range(4))
    if not all((aggregate[0] > exported[0], aggregate[1] < exported[1],
                aggregate[2] > exported[2], aggregate[3] < exported[3])):
        raise ValueError("cell 1024 base_M0 analytic aggregate escapes artifact rectangle")

    SHARED.write_text(
        "import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674\n\n"
        "namespace ConnesWeilRH.Dev\n\n"
        f"def record2688CellRight : ℝ := binary64Value2674 {CELL_RIGHT}\n\n"
        "end ConnesWeilRH.Dev\n",
        encoding="utf-8",
        newline="\n",
    )

    family_template = FAMILY_TEMPLATE.read_text(encoding="utf-8")
    # All family proofs use the same geometry pattern; only interval literals and
    # Fin-index reductions change.
    for family, data in enumerate(per_family):
        boxes = {k: tuple(data[f"{k}_box"]) for k in ("phi", "cos", "sin")}
        body = extract_family(family_template, family, boxes)
        (OUT / f"C1RouteARepairedOwnerCell2688Family{family}.lean").write_text(
            body, encoding="utf-8", newline="\n")

    owner = OWNER_TEMPLATE.read_text(encoding="utf-8")
    owner = owner.replace(
        "import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674",
        "import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674\n"
        "import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2688Shared",
    )
    owner = re.sub(
        r"ConnesWeilRH\.Dev\.C1RouteACellContainment2677Family([0-9]+)",
        r"ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2688Family\1",
        owner,
    )
    owner = owner.replace("record2678Family", "record2688Family")
    owner = owner.replace("record2678", "record2688")
    owner = re.sub(r"record2677Family([0-9]+)", r"record2688Family\1", owner)
    owner = owner.replace("record2675CellRight", "record2688CellRight")
    # Replace only the base-M0 family rectangle definition and its aggregate
    # constants; the owner coefficient and proof structure are retained.
    start = owner.index("noncomputable def record2688BaseM0FamilyRects")
    stop = owner.index("def record2688BaseM0AggregateReLo", start)
    owner = owner[:start] + rect_literal(base_dyadic).replace("record2678", "record2688") + aggregate_defs(base_dyadic).replace("record2678", "record2688") + owner[stop + len("def record2688BaseM0AggregateReLo : ℚ :="):]
    # The previous splice leaves the old aggregate tail; replace its four defs
    # robustly by using the generated block once more.
    pattern = re.compile(r"def record2688BaseM0AggregateReLo : ℚ :=.*?noncomputable def record2688BaseM0Aggregate :", re.DOTALL)
    block = aggregate_defs(base_dyadic).replace("record2678", "record2688") + "noncomputable def record2688BaseM0Aggregate :"
    owner = pattern.sub(block, owner, count=1)
    # The owner template targets record 2675's exported rectangle. Use a new
    # cell-1024 rectangle with the artifact's four endpoint values.
    rect_args = " ".join(f"(binary64Value2674 {v} : ℝ)" for v in row[5][0][:4])
    cell_def = (
        "noncomputable def record2688BaseM0Rect : ComplexRect2427 :=\n"
        f"  ComplexRect2427.mk {rect_args}\n\n"
    )
    owner = owner.replace(
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n\n" + cell_def,
    )
    owner = owner.replace("record2675BaseM0Rect", "record2688BaseM0Rect")
    (OUT / "C1RouteARepairedOwnerCell2688BaseM0.lean").write_text(owner, encoding="utf-8", newline="\n")

    # A small cell consumer connects the new rectangle to the existing four-
    # channel API's base-M0 component.  The other three channels remain explicit
    # next-step obligations.
    norm_bits, charge_bits = row[5][0][4], row[5][0][5]
    consumer = f'''import ConnesWeilRH.Dev.C1RouteARepairedOwnerCellCharge2686
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2688BaseM0

namespace ConnesWeilRH.Dev

private theorem record2688WeightedNormIntervalIntegrable
    {{f : ℝ → ℂ}} {{a b sigma : ℝ}}
    (hf : Continuous f) :
    IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖f x‖)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.norm

private theorem record2688ExternalPhysicalContinuous :
    Continuous (externalPhysical2344 record2688BaseCoefficient capturedModulations2584) := by
  rw [externalPhysical2344_eq_correctedPhysical]
  exact (correctedPhysical_contDiff record2688BaseCoefficient capturedModulations2584).continuous

def record2688BaseM0Norm : ℝ := binary64Value2674 {norm_bits}
def record2688BaseM0Charge : ℝ := binary64Value2674 {charge_bits}

theorem record2688BaseM0CellContainedForIntegral {{x : ℝ}}
    (hx : x ∈ Set.Icc 0 record2688CellRight) :
    record2688BaseM0Rect.Mem
      (externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x) := by
  exact record2688BaseM0CellContained hx

theorem record2688BaseM0IntegralCharge :
    (∫ x in (0 : ℝ)..record2688CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) *
          ‖externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x‖)
      ≤ record2688BaseM0Charge := by
  have hbound :
      (∫ x in (0 : ℝ)..record2688CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) *
            ‖externalPhysical2344 record2688BaseCoefficient capturedModulations2584 x‖)
        ≤ (record2688CellRight - 0) * (1 * record2688BaseM0Norm) := by
    apply weightedNormIntegral_le_of_cellRectangle
      (a := 0) (b := record2688CellRight) (sigma := (-1 / 2 : ℝ))
      (weightBound := 1) (normBound := record2688BaseM0Norm)
      (rect := record2688BaseM0Rect)
      (by norm_num [record2688CellRight, binary64Value2674,
        binary64ExponentBits2674, binary64Significand2674,
        binary64FractionBits2674, binary64Sign2674])
      (fun x hx => record2688BaseM0CellContainedForIntegral hx)
      (ComplexRect2427.cornerNorm_le_of_sq_le (by
        norm_num [record2688BaseM0Norm, binary64Value2674,
          binary64ExponentBits2674, binary64Significand2674,
          binary64FractionBits2674, binary64Sign2674]) (by
        norm_num [record2688BaseM0Rect, record2688BaseM0Norm,
          ComplexRect2427.cornerNormSq, binary64Value2674,
          binary64ExponentBits2674, binary64Significand2674,
          binary64FractionBits2674, binary64Sign2674]))
      (by norm_num)
      (fun x hx => by
        have harg : ((-1 / 2 : ℝ) * x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.1
        calc
          Real.exp ((-1 / 2 : ℝ) * x) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr harg
          _ = 1 := Real.exp_zero)
      (record2688WeightedNormIntervalIntegrable
        (a := 0) (b := record2688CellRight) (sigma := (-1 / 2 : ℝ))
        (f := externalPhysical2344 record2688BaseCoefficient capturedModulations2584)
        record2688ExternalPhysicalContinuous)
  calc
    _ ≤ (record2688CellRight - 0) * (1 * record2688BaseM0Norm) := hbound
    _ ≤ record2688BaseM0Charge := by
      norm_num [record2688CellRight, record2688BaseM0Norm, record2688BaseM0Charge,
        binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
        binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
'''
    (OUT / "C1RouteARepairedOwnerCell2688BaseM0Consumer.lean").write_text(consumer, encoding="utf-8", newline="\n")

    print("generated cell 1024 base-M0 bridge", len(base_dyadic), "families")


if __name__ == "__main__":
    build()
