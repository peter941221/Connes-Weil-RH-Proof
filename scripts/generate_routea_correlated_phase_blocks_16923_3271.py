"""Generate correlated same-frequency phase block rectangles at cell 16923."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCKS = [(0, 4), (5, 9), (10, 14), (15, 19), (20, 24), (25, 29)]
GROUPS = [[0, 1, 4], [2, 3], [5, 6, 7], [8], [9], [10], [11], [12], [13], [14],
          [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26],
          [27], [28], [29]]

def module(f):
    return "3268" if 10 <= f <= 14 else "3269"

def box(f):
    return f"record2680Cell16923Family{f}TightStageBox{module(f)} 9"

def mem(f):
    return f"record2680_cell16923_family{f}_tight_phase_box_mem{module(f)}"

def csum(g):
    s = f"record2680CorrectionCoefficient {g[0]}"
    for f in g[1:]:
        s = f"({s} + record2680CorrectionCoefficient {f})"
    return s

def gname(first, g):
    return f"record2680Cell16923Block{first}Group{g[0]}to{g[-1]}Rect3271"

def gmname(first, g):
    return f"record2680_cell16923_block{first}_group{g[0]}to{g[-1]}_mem3271"

def bname(first, last):
    return f"record2680Cell16923CorrelatedPhaseBlock{first}to{last}Rect3271"

def add_expr(names):
    s = names[0]
    for n in names[1:]:
        s = f"({s}.add\n      {n})"
    return s

def branch(first, groups, indent):
    if len(groups) == 1:
        return [f"{indent}· exact {gmname(first, groups[0])}"]
    return [
        f"{indent}· apply ComplexRect2427.mem_add",
        *branch(first, groups[:-1], indent + "  "),
        *branch(first, groups[-1:], indent + "  "),
    ]


def tree(first, groups):
    if len(groups) == 1:
        return [f"  exact {gmname(first, groups[0])}"]
    return ["  apply ComplexRect2427.mem_add", *branch(first, groups[:-1], "  "),
            *branch(first, groups[-1:], "  ")]

def source():
    out = [
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell16923CoeffPhaseBlocks3270",
        "", "namespace ConnesWeilRH.Dev", "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit", ""]
    for first, last in BLOCKS:
        groups = [g for g in GROUPS if any(first <= f <= last for f in g)]
        for g in groups:
            coeff = csum(g)
            if g == [5, 6, 7]:
                phase = "ComplexRect2427.point 1"
                target = ("(Complex.exp (((capturedModulations2584 5 *\n"
                          "        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))")
                proof = [
                    "  have hphase : (ComplexRect2427.point (1 : ℂ)).Mem",
                    "      (Complex.exp (((capturedModulations2584 5 *",
                    "        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by",
                    "    simpa [capturedModulations2584, Matrix.cons_val_zero,",
                    "      Matrix.cons_val_four, Matrix.cons_val_5, Fin.ext_iff]",
                    "      using (ComplexRect2427.point_mem (1 : ℂ))",
                    "  exact ComplexRect2427.mem_mul",
                    "    (ComplexRect2427.point_mem _) hphase",
                ]
            else:
                f = g[0]
                phase = box(f)
                target = (f"(Complex.exp (((capturedModulations2584 {f} *\n"
                          "        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))")
                proof = ["  exact ComplexRect2427.mem_mul",
                         "    (ComplexRect2427.point_mem _)", f"    {mem(f)}"]
            out += [
                f"noncomputable def {gname(first, g)} : ComplexRect2427 :=",
                f"  (ComplexRect2427.point ({coeff})).mul", f"    ({phase})", "",
                f"theorem {gmname(first, g)} :", f"    {gname(first, g)}.Mem",
                f"      ({coeff} *", f"        {target}) := by", *proof, ""]
        names = [gname(first, g) for g in groups]
        terms = [f"({csum(g)} *\n        (Complex.exp (((capturedModulations2584 {g[0]} *\n"
                       "          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))"
                 for g in groups]
        out += [f"noncomputable def {bname(first, last)} : ComplexRect2427 :=",
                f"  {add_expr(names)}", "",
                f"theorem record2680_cell16923_correlated_phase_block{first}to{last}_mem3271 :",
                f"    {bname(first, last)}.Mem", f"      ({' + '.join(terms)}) := by",
                *tree(first, groups), ""]
    out.append("end ConnesWeilRH.Dev")
    return "\n".join(out) + "\n"

if __name__ == "__main__":
    output = ROOT / "ConnesWeilRH/Dev/C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271.lean"
    output.write_text(source(), encoding="utf-8")
    print(output)
