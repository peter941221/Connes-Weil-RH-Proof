"""Generate staged phase boxes for Route A cell 16923, families 10..14."""

from __future__ import annotations

import math
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, getcontext
from fractions import Fraction
from pathlib import Path

import routea_concrete_owner_taylor6_3204 as concrete

ROOT = Path(__file__).resolve().parents[1]
MIDPOINT = Fraction(-466157575113, 409600000000)
DENOMINATOR = 10**18


def interval_mul(left: tuple[Decimal, Decimal], right: tuple[Decimal, Decimal]):
    values = [
        left[0] * right[0],
        left[0] * right[1],
        left[1] * right[0],
        left[1] * right[1],
    ]
    return min(values), max(values)


def outward(value: Decimal, rounding) -> int:
    scaled = value * DENOMINATOR
    return int(scaled.to_integral_value(rounding=rounding))


def box_expr(box) -> str:
    re_lo, re_hi, im_lo, im_hi = box
    return (
        "{ reLo := %d / %d, reHi := %d / %d, imLo := %d / %d, imHi := %d / %d }"
        % (re_lo, DENOMINATOR, re_hi, DENOMINATOR,
           im_lo, DENOMINATOR, im_hi, DENOMINATOR)
    )


def family_boxes(theta: float) -> list[tuple[int, int, int, int]]:
    angle = theta * float(MIDPOINT) / 512.0
    real = Decimal(str(math.cos(angle)))
    imag = Decimal(str(math.sin(angle)))
    margin = Decimal("1e-15")
    current = (
        (real - margin, real + margin),
        (imag - margin, imag + margin),
    )
    boxes = []
    for _ in range(10):
        boxes.append(
            (
                outward(current[0][0], ROUND_FLOOR),
                outward(current[0][1], ROUND_CEILING),
                outward(current[1][0], ROUND_FLOOR),
                outward(current[1][1], ROUND_CEILING),
            )
        )
        real_square = interval_mul(current[0], current[0])
        imag_square = interval_mul(current[1], current[1])
        current = (
            (real_square[0] - imag_square[1] - margin,
             real_square[1] - imag_square[0] + margin),
            (Decimal(2) * interval_mul(current[0], current[1])[0] - margin,
             Decimal(2) * interval_mul(current[0], current[1])[1] + margin),
        )
    return boxes


def source() -> str:
    getcontext().prec = 80
    families = concrete.load_owner_families()
    chunks = [
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218",
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerStagedPhasePower3251",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
        "",
    ]
    for family in range(10, 15):
        name = f"record2680Cell16923Family{family}TightStageBox3268"
        boxes = family_boxes(float(families[family]["theta"]))
        chunks.append(f"noncomputable def {name} (stage : ℕ) : ComplexRect2427 :=")
        chunks.append("  match stage with")
        for stage, box in enumerate(boxes):
            suffix = "" if stage < 9 else ""
            chunks.append(f"  | {stage} => {box_expr(box)}")
        chunks.append(f"  | _ => {box_expr(boxes[-1])}")
        chunks.append("")

    for family in range(10, 15):
        name = f"record2680Cell16923Family{family}TightStageBox3268"
        chunks.extend([
            f"theorem record2680_cell16923_family{family}_tight_base_mem3268 :",
            f"    ({name} 0).Mem",
            "      (Complex.exp (((capturedModulations2584 %d *" % family,
            "        record2680Center3212 16923 / 512 : ℝ) : ℂ) * Complex.I)) := by",
            "  have hscaled :",
            "      |(capturedModulations2584 %d * record2680Center3212 16923) / 512| ≤ 1 := by" % family,
            "    norm_num [capturedModulations2584, record2680Center3212,",
            "      record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,",
            f"      Matrix.cons_val_four, Matrix.cons_val_{family}, Fin.ext_iff]",
            "  have hphase := phaseRect_mem3218 hscaled",
            "  refine rectSubset2676",
            f"    (inner := phaseRect3218 (capturedModulations2584 {family} * record2680Center3212 16923)) ?_ ?_ ?_ ?_ hphase",
            "  all_goals",
            f"    norm_num [{name}, phaseRect3218, phaseTaylorError3218,",
            "      reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ,",
            "      capturedModulations2584, record2680Center3212, record2680Grid3212,",
            "      diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four,",
            f"      Matrix.cons_val_{family}, Fin.ext_iff, binary64Value2674,",
            "      binary64ExponentBits2674, binary64Significand2674,",
            "      binary64FractionBits2674, binary64Sign2674]",
            "",
            "set_option maxRecDepth 100000 in",
            f"theorem record2680_cell16923_family{family}_tight_step_mem3268",
            "    {stage : ℕ} (hstage : stage < 9) {w : ℂ}",
            f"    (hw : ({name} stage).Mem w) :",
            f"    ({name} (stage + 1)).Mem (w * w) := by",
            "  have hmul := ComplexRect2427.mem_mul hw hw",
            "  refine rectSubset2676",
            f"    (inner := ({name} stage).mul ({name} stage)) ?_ ?_ ?_ ?_ hmul",
            "  all_goals",
            "    interval_cases stage <;>",
            f"      norm_num [{name}, ComplexRect2427.mul, RealInterval2429.mul,",
            "        RealInterval2429.add, RealInterval2429.sub]",
            "",
            f"theorem record2680_cell16923_family{family}_tight_phase_box_mem3268 :",
            f"    ({name} 9).Mem",
            "      (Complex.exp (((capturedModulations2584 %d *" % family,
            "        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by",
            f"  have hstage := complexRectPowSq_staged_mem_of_bound3251",
            f"    record2680_cell16923_family{family}_tight_base_mem3268",
            f"    (fun stage hstage w hw => record2680_cell16923_family{family}_tight_step_mem3268 hstage hw)",
            "  rw [complex_phase_eq_pow512_3218]",
            "  exact hstage",
            "",
        ])
    chunks.extend(["end ConnesWeilRH.Dev", ""])
    return "\n".join(chunks)


def main() -> None:
    output = ROOT / "ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268.lean"
    output.write_text(source(), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
