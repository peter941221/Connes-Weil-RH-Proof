"""Generate staged phase boxes for the remaining 16923 owner families."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from generate_routea_phase_boxes_16923_3268 import box_expr, concrete, family_boxes  # noqa: E402

FAMILIES = list(range(10)) + list(range(15, 30))


def matrix_index_name(family: int) -> str:
    return {
        0: "zero",
        1: "one",
        2: "two",
        3: "three",
        4: "four",
    }.get(family, str(family))


def source() -> str:
    owner_families = concrete.load_owner_families()
    chunks = [
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218",
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerStagedPhasePower3251",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
        "",
    ]
    for family in FAMILIES:
        name = f"record2680Cell16923Family{family}TightStageBox3269"
        boxes = family_boxes(float(owner_families[family]["theta"]))
        chunks.extend([
            f"noncomputable def {name} (stage : ℕ) : ComplexRect2427 :=",
            "  match stage with",
        ])
        for stage, box in enumerate(boxes):
            chunks.append(f"  | {stage} => {box_expr(box)}")
        chunks.extend([
            f"  | _ => {box_expr(boxes[-1])}",
            "",
        ])

    for family in FAMILIES:
        name = f"record2680Cell16923Family{family}TightStageBox3269"
        index_name = matrix_index_name(family)
        chunks.extend([
            f"theorem record2680_cell16923_family{family}_tight_base_mem3269 :",
            f"    ({name} 0).Mem",
            f"      (Complex.exp (((capturedModulations2584 {family} *",
            "        record2680Center3212 16923 / 512 : ℝ) : ℂ) * Complex.I)) := by",
            "  have hscaled :",
            f"      |(capturedModulations2584 {family} * record2680Center3212 16923) / 512| ≤ 1 := by",
            "    norm_num [capturedModulations2584, record2680Center3212,",
            "      record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,",
            f"      Matrix.cons_val_four, Matrix.cons_val_{index_name}, Fin.ext_iff]",
            "  have hphase := phaseRect_mem3218 hscaled",
            "  refine rectSubset2676",
            f"    (inner := phaseRect3218 (capturedModulations2584 {family} * record2680Center3212 16923)) ?_ ?_ ?_ ?_ hphase",
            "  all_goals",
            f"    norm_num [{name}, phaseRect3218, phaseTaylorError3218,",
            "      reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ,",
            "      capturedModulations2584, record2680Center3212, record2680Grid3212,",
            "      diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four,",
            f"      Matrix.cons_val_{index_name}, Fin.ext_iff, binary64Value2674,",
            "      binary64ExponentBits2674, binary64Significand2674,",
            "      binary64FractionBits2674, binary64Sign2674]",
            "",
            "set_option maxRecDepth 100000 in",
            f"theorem record2680_cell16923_family{family}_tight_step_mem3269",
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
            f"theorem record2680_cell16923_family{family}_tight_phase_box_mem3269 :",
            f"    ({name} 9).Mem",
            f"      (Complex.exp (((capturedModulations2584 {family} *",
            "        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by",
            f"  have hstage := complexRectPowSq_staged_mem_of_bound3251",
            f"    record2680_cell16923_family{family}_tight_base_mem3269",
            f"    (fun stage hstage w hw => record2680_cell16923_family{family}_tight_step_mem3269 hstage hw)",
            "  rw [complex_phase_eq_pow512_3218]",
            "  exact hstage",
            "",
        ])
    chunks.append("end ConnesWeilRH.Dev")
    return "\n".join(chunks) + "\n"


def main() -> None:
    output = ROOT / "ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseFamiliesRemaining16923TightStaged3269.lean"
    output.write_text(source(), encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
