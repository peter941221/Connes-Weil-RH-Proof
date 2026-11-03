"""Generate owner coefficient-phase block rectangles at cell 16923."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCKS = [(0, 4), (5, 9), (10, 14), (15, 19), (20, 24), (25, 29)]


def family_module(family: int) -> str:
    return "3268" if 10 <= family <= 14 else "3269"


def family_box(family: int) -> str:
    return f"record2680Cell16923Family{family}TightStageBox{family_module(family)} 9"


def family_rect(family: int) -> str:
    return f"record2680Cell16923Family{family}CoeffPhaseRect3270"


def family_mem(family: int) -> str:
    return f"record2680_cell16923_family{family}_tight_phase_box_mem{family_module(family)}"


def sum_expr(first: int, last: int) -> str:
    expression = family_rect(first)
    for family in range(first + 1, last + 1):
        expression = f"({expression}.add\n      {family_rect(family)})"
    return expression


def mem_proof(first: int, last: int) -> list[str]:
    lines = ["  apply ComplexRect2427.mem_add"]
    if last - first == 1:
        return lines + [f"  · exact {family_mem(first)}", f"  · exact {family_mem(last)}"]
    lines = ["  apply ComplexRect2427.mem_add", "  · apply ComplexRect2427.mem_add"]
    # The generated nesting is left-associated: (((f0 + f1) + f2) + ...).
    current = first
    for family in range(first + 1, last):
        if family == first + 1:
            lines.append(f"    · exact {family_mem(first)}")
            lines.append(f"    · exact {family_mem(family)}")
        else:
            break
    lines = ["  apply ComplexRect2427.mem_add"]
    nested = "  "
    # Use a simple explicit proof tree matching left-associated additions.
    def tree(lo: int, hi: int, indent: str) -> list[str]:
        if lo == hi:
            return [f"{indent}exact {family_mem(lo)}"]
        return [
            f"{indent}apply ComplexRect2427.mem_add",
            *tree(lo, hi - 1, indent + "  "),
            *tree(hi, hi, indent + "  "),
        ]
    return tree(first, last, "  ")


def source() -> str:
    chunks = [
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268",
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamiliesRemaining16923TightStaged3269",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit",
        "",
    ]
    for family in range(30):
        chunks.extend([
            f"noncomputable def {family_rect(family)} : ComplexRect2427 :=",
            f"  (ComplexRect2427.point (record2680CorrectionCoefficient {family})).mul",
            f"    ({family_box(family)})",
            "",
            f"theorem record2680_cell16923_family{family}_coeff_phase_rect_mem3270 :",
            f"    {family_rect(family)}.Mem",
            f"      (record2680CorrectionCoefficient {family} *",
            f"        Complex.exp (((capturedModulations2584 {family} *",
            "          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by",
            "  exact ComplexRect2427.mem_mul",
            "    (ComplexRect2427.point_mem _)",
            f"    {family_mem(family)}",
            "",
        ])
    for first, last in BLOCKS:
        block_name = f"record2680Cell16923CoeffPhaseBlock{first}to{last}Rect3270"
        chunks.extend([
            f"noncomputable def {block_name} : ComplexRect2427 :=",
            f"  {sum_expr(first, last)}",
            "",
        ])
    chunks.append("end ConnesWeilRH.Dev")
    return "\n".join(chunks) + "\n"


if __name__ == "__main__":
    output = ROOT / "ConnesWeilRH/Dev/C1RouteAConcreteOwnerCell16923CoeffPhaseBlocks3270.lean"
    output.write_text(source(), encoding="utf-8")
    print(output)
