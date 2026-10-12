"""Generate the remaining repaired-owner base-D2 family bridges."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "ConnesWeilRH/Dev/C1RouteARepairedOwnerBaseD22681.lean"
OUT = ROOT / "ConnesWeilRH/Dev"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def get_factor_boxes() -> list[list[int]]:
    screen_path = ROOT / "results/2676_cell4096_containment_screen.json"
    screen = json.loads(screen_path.read_text(encoding="utf-8"))
    if screen.get("status") != "CELL4096_CONTAINMENT_SCREEN_PASS":
        raise RuntimeError("record 2676 screen is not passing")
    price = json.loads(
        (ROOT / "results/2675_repaired_owner_cell_price_certificate.json")
        .read_text(encoding="utf-8")
    )
    strip = load("strip2682", ROOT / "scripts/routea_corrected_strip_envelope_2303.py")
    calc = load("calc2682", ROOT / "scripts/routea_cell4096_containment_2676.py")
    families, base, correction, _ = strip.load_owner()
    right = calc.fraction_of_bits(
        int(price["cell"]["cell_endpoints"]["x_hi"]["bits"], 16)
    )
    width = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth"
    )
    theta = calc.parse_fin30_rationals(
        ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
        "capturedModulations2584",
    )
    rows = calc.build_chain(
        families, base, correction, right, theta, width, calc.exp_pins()[2:]
    )
    return [calc.dyadic_outer(row["factor_rect"]) for row in rows]


def replace_factor(source: str, family: int, values: list[int]) -> str:
    start = source.index("noncomputable def record2681Family0D2FactorRect")
    end = source.index("\n\nset_option maxRecDepth", start)
    fields = "\n".join(
        f"    {key} := (({value} : ℚ) / (2 : ℚ) ^ 160 : ℝ)"
        for key, value in zip(("reLo", "reHi", "imLo", "imHi"), values)
    )
    definition = (
        f"noncomputable def record2681Family{family}D2FactorRect : ComplexRect2427 :=\n"
        f"  {{\n{fields}\n  }}"
    )
    return source[:start] + definition + source[end:]


def replace_sign(source: str, family: int, sign: str) -> str:
    old_hth = "have htheta : theta < 0 := by\n    norm_num [theta, capturedModulations2584]"
    hth = {
        "negative": old_hth,
        "positive": "have htheta : 0 < theta := by\n    norm_num [theta, capturedModulations2584]",
        "zero": "have htheta : theta = 0 := by\n    norm_num [theta, capturedModulations2584]",
    }[sign]
    source = source.replace(old_hth, hth, 1)
    if sign != "negative":
        old = """  have himLower : 0 ≤ 2 * theta * familyLogFirst2345 radius x := by
    have hprod : 0 ≤ theta * familyLogFirst2345 radius x :=
      mul_nonneg_of_nonpos_of_nonpos htheta.le hfirstNonpos
    nlinarith
  have himUpper : 2 * theta * familyLogFirst2345 radius x ≤
      -2 * theta * firstBound := by
    nlinarith [mul_le_mul_of_nonpos_left hfirstLower (by linarith : 2 * theta ≤ 0)]
"""
        if sign == "positive":
            new = """  have himLower : -2 * theta * firstBound ≤
      2 * theta * familyLogFirst2345 radius x := by
    have hprod := mul_le_mul_of_nonneg_left hfirstLower
      (by positivity : 0 ≤ 2 * theta)
    nlinarith
  have himUpper : 2 * theta * familyLogFirst2345 radius x ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * theta)
      hfirstNonpos
"""
        else:
            new = """  have himLower : 0 ≤ 2 * theta * familyLogFirst2345 radius x := by
    rw [htheta]
    norm_num
  have himUpper : 2 * theta * familyLogFirst2345 radius x ≤ 0 := by
    rw [htheta]
    norm_num
"""
        if old not in source:
            raise RuntimeError(f"imaginary sign template missing for {family}")
        source = source.replace(old, new, 1)
        old_hi = """  have hrectImHi : -2 * theta * firstBound ≤
      record2681Family{family}D2FactorRect.imHi := by
    norm_num [record2681Family{family}D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
""".format(family=family)
        hhi = """  have hrectImHi : 0 ≤
      record2681Family{family}D2FactorRect.imHi := by
    norm_num [record2681Family{family}D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
""".format(family=family)
        if old_hi not in source:
            raise RuntimeError(f"imaginary upper rectangle template missing for {family}")
        source = source.replace(old_hi, hhi, 1)
    lower_expr = (
        "0" if sign in ("negative", "zero") else "-2 * theta * firstBound"
    )
    hlow = f"""  have hrectImLo : record2681Family{family}D2FactorRect.imLo ≤
      {lower_expr} := by
    norm_num [record2681Family{family}D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
"""
    source = source.replace("  have hre :\n", hlow + "  have hre :\n", 1)
    source = source.replace(
        "  · exact himLower\n  · exact himUpper.trans hrectImHi",
        "  · exact hrectImLo.trans himLower\n  · exact himUpper.trans hrectImHi",
        1,
    )
    return source


def render(template: str, family: int, factor: list[int], sign: str) -> str:
    source = replace_factor(template, family, factor)
    source = source.replace("Family0", f"Family{family}")
    source = source.replace("record2681Family0D2FactorRect", f"record2681Family{family}D2FactorRect")
    for old, new in (
        ("storedWidth 0", f"storedWidth {family}"),
        ("record2678BaseCoefficient 0", f"record2678BaseCoefficient {family}"),
        ("capturedModulations2584 0", f"capturedModulations2584 {family}"),
        ("record2676BaseD2FamilyRects 0", f"record2676BaseD2FamilyRects {family}"),
    ):
        source = source.replace(old, new)
    source = replace_sign(source, family, sign)
    names = {0: "zero", 1: "one", 2: "two", 3: "three", 4: "four"}
    index_name = names.get(family, str(family))
    if family >= 5:
        lines = source.splitlines()
        last = max(i for i, line in enumerate(lines) if line.startswith("import "))
        lines.insert(last + 1, "import ConnesWeilRH.Dev.MatrixConsValFamily2637")
        source = "\n".join(lines)
    return source.replace(
        "norm_num [", f"norm_num [Matrix.cons_val_{index_name}, Matrix.cons_val_zero, "
    )


def main() -> None:
    template = TEMPLATE.read_text(encoding="utf-8")
    factors = get_factor_boxes()
    positive, zero = {2, 3}, {5, 6, 7}
    for family in range(1, 30):
        sign = "zero" if family in zero else ("positive" if family in positive else "negative")
        name = f"C1RouteARepairedOwnerBaseD22682Family{family}"
        (OUT / f"{name}.lean").write_text(
            render(template, family, factors[family], sign), encoding="utf-8", newline="\n"
        )
        (OUT / f"{name}Audit.lean").write_text(
            f"import ConnesWeilRH.Dev.{name}\n\nnamespace ConnesWeilRH.Dev\n\n"
            f"#print axioms record2681Family{family}D2FactorMem\n"
            f"#print axioms record2681Family{family}BaseD2CellRectMem\n\n"
            "end ConnesWeilRH.Dev\n",
            encoding="utf-8",
            newline="\n",
        )
    print("generated repaired-owner base-D2 families 1..29")


if __name__ == "__main__":
    main()
