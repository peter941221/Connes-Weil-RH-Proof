"""Generate both signs on the two cells meeting the production grid origin."""
import json
from fractions import Fraction as Q
from generate_signed_cells_2558 import ROOT,Cell,render_endpoint,render_value,write,read
from generate_complex_exp_node_2541 import real
from format_lean_source_2553 import wrap_source
from validate_adaptive_nodes_2542 import scalar_def


CASES = tuple(Cell(index,sign,2559) for sign in (1,-1) for index in (5119,5120))


def render_segment():
    parts = ["\n".join("import ConnesWeilRH.Dev."+cell.module("Integral") for cell in CASES),
             "\n\nnamespace ConnesWeilRH.Dev\n\nopen scoped BigOperators\n\n"]
    totals = {}
    for sign,name in ((1,"Plus"),(-1,"Minus")):
        sigma = "(1/2)" if sign > 0 else "(-1/2)"
        left,right = (Cell(index,sign,2559) for index in (5119,5120))
        total = sum(scalar_def(read(cell.module("Integral")),cell.prefix+"CellIntegralUpper2559")
                    for cell in (left,right))
        totals[sign] = total
        positions = [f"batchN{index:05d}{name}Position2559" for index in (5119,5120,5121)]
        neg_fix = ""
        if sign < 0:
            neg_fix = "  have hs : (-1 : ℝ) / 2 = -(1 / 2) := by norm_num\n  rw [hs] at hleft hright ⊢\n"
        parts.append(f"""theorem central{name}IntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in {positions[0]}..{positions[2]},
      ‖weightedPhysical2539 {sigma} coefficients nodeModulation2541 x‖) ≤ {real(total)} := by
  let a : ℕ → ℝ := fun i => if i = 0 then {positions[0]}
    else if i = 1 then {positions[1]} else {positions[2]}
  have hcont :=
    (weightedPhysical2539_contDiff {sigma} coefficients nodeModulation2541).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖weightedPhysical2539 {sigma} coefficients nodeModulation2541 x‖)
    (μ := MeasureTheory.volume) (a := a) (n := 2)
    (fun i _ => hcont.intervalIntegrable (a i) (a (i+1)))
  have hleft := {left.prefix}CellIntegralBound2559 coefficients hcoeff
  have hright := {right.prefix}CellIntegralBound2559 coefficients hcoeff
  norm_num [Finset.sum_range_succ, a] at hsum
{neg_fix}  rw [← hsum]
  have h := add_le_add hleft hright
  norm_num [{left.prefix}CellIntegralUpper2559, {right.prefix}CellIntegralUpper2559] at h ⊢
  exact h

""")
    parts.append(f"""theorem centralBothSignsIntegralBound2559 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤
      baseCoefficientError2540 i) :
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) +
    (∫ x in batchN05119PlusPosition2559..batchN05121PlusPosition2559,
      ‖weightedPhysical2539 (-1/2) coefficients nodeModulation2541 x‖) ≤ {real(sum(totals.values()))} := by
  have hp := centralPlusIntegralBound2559 coefficients hcoeff
  have hn := centralMinusIntegralBound2559 coefficients hcoeff
  have hl : batchN05119MinusPosition2559 = batchN05119PlusPosition2559 := by
    norm_num [batchN05119MinusPosition2559, batchN05119PlusPosition2559]
  have hr : batchN05121MinusPosition2559 = batchN05121PlusPosition2559 := by
    norm_num [batchN05121MinusPosition2559, batchN05121PlusPosition2559]
  rw [hl, hr] at hn
  have h := add_le_add hp hn
  convert h using 1
  norm_num

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.centralPlusIntegralBound2559
#print axioms ConnesWeilRH.Dev.centralMinusIntegralBound2559
#print axioms ConnesWeilRH.Dev.centralBothSignsIntegralBound2559
""")
    return wrap_source("".join(parts))


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--segment-only",action="store_true")
    args = parser.parse_args()
    if args.segment_only:
        write("C1RouteACentralSegment2559",render_segment())
        raise SystemExit(0)
    for sign in (1,-1):
        for index in (5119,5120,5121):
            module,source = render_endpoint(index,sign,2559)
            write(module,source)
            module,source,_ = render_value(index,sign,2559)
            write(module,source)
    reports = []
    for cell in CASES:
        write(cell.module("Midpoint"),cell.render_midpoint())
        for side in ("Left","Right"):
            write(cell.module(side+"Bounds"),cell.render_norm(side))
        write(cell.module("MidpointBounds"),cell.render_midpoint_bounds()[0])
        write(cell.module("Fourth"),cell.render_fourth())
        write(cell.module("Assembly"),cell.render_assembly())
        source,info = cell.render_integral()
        write(cell.module("Integral"),source)
        reports.append(dict(index=cell.index,sign=cell.sign,**info))
        print(reports[-1],flush=True)
    (ROOT/"results/2559_central_cell_inputs.json").write_text(json.dumps(reports,indent=2)+"\n")
    write("C1RouteACentralSegment2559",render_segment())
