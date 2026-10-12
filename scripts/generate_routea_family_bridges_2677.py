"""Generate family-specific base-M0 cell bridges for record 2677."""

from __future__ import annotations

import json
import re
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCREEN = ROOT / "results/2677_cell4096_coefficient_enclosure_screen.json"
TEMPLATE = ROOT / "ConnesWeilRH/Dev/C1RouteACellContainment2677Family0.lean"


def render_interval(name: str, values: list[str]) -> str:
    lower, upper = values
    ln, ld = lower.split("/") if "/" in lower else (lower, "1")
    un, ud = upper.split("/") if "/" in upper else (upper, "1")
    return (
        f"noncomputable def {name} : RealInterval2429 :=\n"
        f"  {{ lo := (({ln} : ℚ) / ({ld} : ℚ) : ℝ)\n"
        f"    hi := (({un} : ℚ) / ({ud} : ℚ) : ℝ) }}"
    )


def replace_interval(source: str, name: str, values: list[str]) -> str:
    pattern = re.compile(
        rf"noncomputable def {name} : RealInterval2429 :=.*?\n\n", re.DOTALL
    )
    source, count = pattern.subn(render_interval(name, values) + "\n\n", source, 1)
    if count != 1:
        raise RuntimeError(f"missing interval {name}")
    return source


def orient_positive(source: str, index: int) -> str:
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
        raise RuntimeError(f"negative geometry block missing for family {index}")
    source = source.replace(old, new, 1)
    source = source.replace("have htheta : theta < 0", "have htheta : 0 < theta", 1)
    source = source.replace(
        "endpointHullOfBoxes2676 cosEndpoint cosRight delta",
        "endpointHullOfBoxes2676 cosRight cosEndpoint delta",
    )
    return source


def orient_zero(source: str, index: int) -> str:
    start = source.index(f"set_option maxRecDepth 10000 in\ntheorem record2677Family{index}TrigMem")
    end = source.index(f"\ntheorem record2677Family{index}BaseM0CellMem", start)
    word = {1: "one", 2: "two", 3: "three", 4: "four"}.get(index, str(index))
    theorem = f'''set_option maxRecDepth 10000 in
theorem record2677Family{index}TrigMem {{x : ℝ}}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    record2677Family{index}CosRect.Mem
        (Real.cos (capturedModulations2584 {index} * x)) ∧
      record2677Family{index}SinRect.Mem
        (Real.sin (capturedModulations2584 {index} * x)) := by
  have hzero : capturedModulations2584 {index} = 0 := by
    norm_num [Matrix.cons_val_{word}, Matrix.cons_val_zero, capturedModulations2584]
  constructor
  · rw [hzero, zero_mul, Real.cos_zero]
    norm_num [record2677Family{index}CosRect, RealInterval2429.point, RealInterval2429.Mem]
  · rw [hzero, zero_mul, Real.sin_zero]
    norm_num [record2677Family{index}SinRect, RealInterval2429.point, RealInterval2429.Mem]
'''
    return source[:start] + theorem + source[end:]


def main() -> None:
    report = json.loads(SCREEN.read_text(encoding="utf-8"))
    template = TEMPLATE.read_text(encoding="utf-8")
    for family in report["family_inputs"]:
        index = family["index"]
        if index == 0:
            continue
        source = template.replace("Family0", f"Family{index}")
        for old, new in (
            ("storedWidth 0", f"storedWidth {index}"),
            ("baseCoefficientBox2540 0", f"baseCoefficientBox2540 {index}"),
            ("baseCoefficientCenter2540 0", f"baseCoefficientCenter2540 {index}"),
            ("baseCoefficientCenter_mem2540 0", f"baseCoefficientCenter_mem2540 {index}"),
            ("capturedModulations2584 0", f"capturedModulations2584 {index}"),
            ("record2677BaseM0FamilyRects 0", f"record2677BaseM0FamilyRects {index}"),
        ):
            source = source.replace(old, new)
        # The template's numeric interval literals belong to family 0.  Copy
        # the screened, outward-rounded literals for each target family before
        # changing the proof orientation; otherwise a positive modulation is
        # paired with family 0's negative sine box and the generated theorem
        # correctly reduces to False.
        for suffix, key in (
            ("PhiRect", "phi_interval_exact"),
            ("CosRect", "cos_interval_exact"),
            ("SinRect", "sin_interval_exact"),
        ):
            source = replace_interval(
                source,
                f"record2677Family{index}{suffix}",
                list(family[key]),
            )
        modulation = Fraction(family["modulation_exact"])
        if modulation > 0:
            source = orient_positive(source, index)
        elif modulation == 0:
            source = orient_zero(source, index)
        word = {1: "one", 2: "two", 3: "three", 4: "four"}.get(index, str(index))
        imports = source.split("\n")
        if index >= 5:
            last = max(i for i, line in enumerate(imports) if line.startswith("import "))
            imports.insert(last + 1, "import ConnesWeilRH.Dev.MatrixConsValFamily2637")
        source = "\n".join(imports).replace(
            "norm_num [", f"norm_num [Matrix.cons_val_{word}, Matrix.cons_val_zero, "
        )
        source = source.replace(
            f"record2677Family{index}PhiRect.lo = loBase * pLo",
            f"record2677Family{index}PhiRect.lo ≤ loBase * pLo",
        )
        source = source.replace(
            f"_ = record2677Family{index}PhiRect.hi := by",
            f"_ ≤ record2677Family{index}PhiRect.hi := by",
        )
        source = source.split(
            "set_option maxRecDepth 10000 in\ntheorem record2677BaseM0AggregateSubset",
            1,
        )[0] + "end ConnesWeilRH.Dev\n"
        path = ROOT / f"ConnesWeilRH/Dev/C1RouteACellContainment2677Family{index}.lean"
        audit = ROOT / f"ConnesWeilRH/Dev/C1RouteACellContainment2677Family{index}Audit.lean"
        names = [
            f"record2677Family{index}BaseM0Mem", f"record2677Family{index}BaseM0CenterMem",
            f"record2677Family{index}PhiMem", f"record2677Family{index}TrigMem",
            f"record2677Family{index}BaseM0CellMem", f"record2677Family{index}BaseM0Subset",
            f"record2677Family{index}BaseM0CellRectMem",
        ]
        audit_text = "\n".join([
            f"import ConnesWeilRH.Dev.C1RouteACellContainment2677Family{index}", "",
            "namespace ConnesWeilRH.Dev", "", *(f"#print axioms {n}" for n in names),
            "", "end ConnesWeilRH.Dev", "",
        ])
        path.write_text(source, encoding="utf-8", newline="\n")
        audit.write_text(audit_text, encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
