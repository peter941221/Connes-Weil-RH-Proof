"""Generate bump-aware correlated phase rectangles at cell 16923."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BLOCKS = [(0, 4), (5, 9), (10, 14), (15, 19), (20, 24), (25, 29)]
GROUPS = [[0, 1, 4], [2, 3], [5, 6, 7], [8], [9], [10], [11], [12], [13], [14],
          [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26],
          [27], [28], [29]]

def module(f): return "3268" if 10 <= f <= 14 else "3269"
def phase(f): return f"record2680Cell16923Family{f}TightStageBox{module(f)} 9"
def pmem(f): return f"record2680_cell16923_family{f}_tight_phase_box_mem{module(f)}"
def bump(f): return f"record2680Cell16923Family{f}BumpRect3272"
def bmem(f): return f"record2680_cell16923_family{f}_bump_mem3272"
def cbump(f): return f"record2680Cell16923Family{f}CoeffBumpRect3272"
def cbmem(f): return f"record2680_cell16923_family{f}_coeff_bump_mem3272"
def base(first,g): return f"record2680Cell16923BumpBase{first}_{g[0]}to{g[-1]}Rect3272"
def gname(first,g): return f"record2680Cell16923BumpCorrelatedGroup{first}_{g[0]}to{g[-1]}Rect3272"
def gm(first,g): return f"record2680_cell16923_bump_correlated_group{first}_{g[0]}to{g[-1]}_mem3272"
def block(first,last): return f"record2680Cell16923BumpCorrelatedBlock{first}to{last}Rect3272"
def add(names):
    s = names[0]
    for n in names[1:]: s = f"({s}.add\n      {n})"
    return s
def groups(first,last): return [g for g in GROUPS if any(first <= f <= last for f in g)]
def branch(names, indent):
    if len(names) == 1: return [f"{indent}· exact {names[0]}"]
    return [f"{indent}· apply ComplexRect2427.mem_add",
            *branch(names[:-1], indent + "  "), *branch(names[-1:], indent + "  ")]
def tree(names):
    if len(names) == 1: return [f"  exact {names[0]}"]
    return ["  apply ComplexRect2427.mem_add", *branch(names[:-1], "  "),
            *branch(names[-1:], "  ")]

def bump_term(f):
    return (f"(record2680CorrectionCoefficient {f} * "
            f"(widthBump (storedWidth {f} ^ 2) "
            "(record2680Center3212 16923) : ℂ))")

def sum_terms(fs):
    s = bump_term(fs[0])
    for f in fs[1:]: s = f"({s} + {bump_term(f)})"
    return s

def phase_term(f):
    return (f"(Complex.exp (((capturedModulations2584 {f} * "
            "record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))")

def source():
    out = [
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell16923Value3242",
        "import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCorrelatedPhaseBlocks3271",
        "", "namespace ConnesWeilRH.Dev", "",
        "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit", ""]
    for f in range(30):
        out += [f"noncomputable def {bump(f)} : ComplexRect2427 :=",
                f"  {{ reLo := (record2680Cell16923BumpInterval3242 {f}).lo,",
                f"    reHi := (record2680Cell16923BumpInterval3242 {f}).hi,",
                "    imLo := 0, imHi := 0 }", "",
                f"theorem {bmem(f)} : ({bump(f)}).Mem",
                f"    (widthBump (storedWidth {f} ^ 2)",
                "      (record2680Center3212 16923) : ℂ) := by",
                f"  have h := record2680_cell16923_bump_mem3242 (family := {f})",
                "  exact ⟨h.1, h.2, by rfl, by rfl⟩", "",
                f"noncomputable def {cbump(f)} : ComplexRect2427 :=",
                f"  (ComplexRect2427.point (record2680CorrectionCoefficient {f})).mul",
                f"    ({bump(f)})", "",
                f"theorem {cbmem(f)} : ({cbump(f)}).Mem",
                f"    (record2680CorrectionCoefficient {f} *",
                f"      (widthBump (storedWidth {f} ^ 2)",
                "        (record2680Center3212 16923) : ℂ)) := by",
                "  exact ComplexRect2427.mem_mul",
                "    (ComplexRect2427.point_mem _)", f"    {bmem(f)}", ""]
    for first,last in BLOCKS:
        for g in groups(first,last):
            out += [f"noncomputable def {base(first,g)} : ComplexRect2427 :=",
                    f"  {add([cbump(f) for f in g])}", "",
                    f"noncomputable def {gname(first,g)} : ComplexRect2427 :="]
            ph = "ComplexRect2427.point 1" if g == [5,6,7] else phase(g[0])
            pterm = "(1 : ℂ)" if g == [5,6,7] else phase_term(g[0])
            out += [f"  ({base(first,g)}).mul", f"    ({ph})", "",
                    f"theorem {gm(first,g)} : ({gname(first,g)}).Mem",
                    f"    ({sum_terms(g)} * {pterm}) := by",
                    "  apply ComplexRect2427.mem_mul", "  ·"]
            out += [x.replace("  ", "    ", 1) for x in tree([cbmem(f) for f in g])]
            if g == [5,6,7]:
                out += ["  · exact ComplexRect2427.point_mem _", ""]
            else:
                out += [f"  · exact {pmem(g[0])}", ""]
        gs = groups(first,last)
        block_terms = []
        for g in gs:
            pterm = "(1 : ℂ)" if g == [5,6,7] else phase_term(g[0])
            block_terms.append(f"({sum_terms(g)} * {pterm})")
        out += [f"noncomputable def {block(first,last)} : ComplexRect2427 :=",
                f"  {add([gname(first,g) for g in gs])}", "",
                f"theorem record2680_cell16923_bump_correlated_block{first}to{last}_mem3272 :",
                f"    ({block(first,last)}).Mem",
                f"      ({' + '.join(block_terms)}) := by"]
        out += tree([gm(first,g) for g in gs]) + [""]
    out += ["end ConnesWeilRH.Dev", ""]
    return "\n".join(out)

if __name__ == "__main__":
    output = ROOT / "ConnesWeilRH/Dev/C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272.lean"
    output.write_text(source(), encoding="utf-8")
    print(output)
