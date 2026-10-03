"""Assemble the same-owner cell-5440 numerical integral certificate."""
from fractions import Fraction as Q
import json
import textwrap

from generate_complex_exp_node_2541 import ROOT, real
from generate_adaptive_nodes_2542 import render as render_node
from validate_adaptive_nodes_2542 import scalar_def


def render(*, cell_index=5440, sources=None, midpoint_upper=Q(997840737,400000),
           left_upper=Q(721605217,1250000000), right_node=None, sigma=Q(1,2)):
    assert sigma in (Q(1,2),Q(-1,2))
    right_source,right_info = render_node(cell_index+1,1 if sigma > 0 else -1) if right_node is None else right_node
    h = Q(65536001,51200000000)
    left = (ROOT/"ConnesWeilRH/Dev/C1RouteAEndpointLeftNorms2544.lean").read_text()
    right = (ROOT/"ConnesWeilRH/Dev/C1RouteAEndpointRightNorms2544.lean").read_text()
    fourth = (ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean").read_text()
    if sources is not None:
        left,right,fourth = sources
    coeffs = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    def ceilq(v,scale=10**6):
        return Q(-((-v.numerator*scale)//v.denominator),scale)
    parts = ["""import ConnesWeilRH.Dev.C1RouteAFourthEnvelope2545
import ConnesWeilRH.Dev.C1RouteACellRight2546
import ConnesWeilRH.Dev.C1RouteAAdaptiveN05440Plus2542

namespace ConnesWeilRH.Dev

open scoped BigOperators

"""]
    uppers = []
    for i,row in enumerate(coeffs):
        c = [(Q(row["ideal_base_coefficient"][p]["lower_exact"])+
              Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2 for p in ("real","imag")]
        cm = sum(abs(v) for v in c)+Q(1,10**30)
        term = max(scalar_def(left,f"endpointLeftP{i:03d}NormUpper2544"),
                   scalar_def(right,f"endpointRightP{i:03d}NormUpper2544")) + h/2*scalar_def(fourth,f"fourthP{i:03d}Upper2545")
        upper = ceilq(cm*term)
        uppers.append(upper)
        p = f"cellP{i:03d}"
        parts.append(f"""noncomputable def {p}Charge2546 : ℝ := {real(upper)}

theorem {p}ChargeBound2546 :
    (‖baseCoefficientCenter2540 ⟨{i}, by omega⟩‖ + baseCoefficientError2540 ⟨{i}, by omega⟩) *
      thirdCellTerm2544 ⟨{i}, by omega⟩ ≤ {p}Charge2546 := by
  have hc : ‖baseCoefficientCenter2540 ⟨{i}, by omega⟩‖ +
      baseCoefficientError2540 ⟨{i}, by omega⟩ ≤ {real(cm)} := by
    have h := Complex.norm_le_abs_re_add_abs_im (baseCoefficientCenter2540 ⟨{i}, by omega⟩)
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, baseCoefficientError2540] at *
    linarith
  have ht : thirdCellTerm2544 ⟨{i}, by omega⟩ ≤ {real(term)} := by
    unfold thirdCellTerm2544
    have h := fourthP{i:03d}Bound2545
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP{i:03d}NormUpper2544, endpointRightP{i:03d}NormUpper2544,
      fourthP{i:03d}Upper2545, endpointLeftPosition2544, endpointRightPosition2544] at *
    linarith
  have hc0 : 0 ≤ ‖baseCoefficientCenter2540 ⟨{i}, by omega⟩‖ +
      baseCoefficientError2540 ⟨{i}, by omega⟩ :=
    add_nonneg (norm_nonneg _) (by norm_num [baseCoefficientError2540])
  apply ((mul_le_mul_of_nonneg_left ht hc0).trans
    (mul_le_mul_of_nonneg_right hc (by norm_num))).trans
  norm_num [{p}Charge2546]

""")
    total = sum(uppers)
    curvature = ceilq(midpoint_upper+total*h/2)
    right_upper = Q(right_info["upper"])
    integral = ceilq(h/2*(left_upper+right_upper)+curvature*h**3/12,10**12)
    parts.append("noncomputable def cellCharge2546 (i : Fin 30) : ℝ :=\n  match i.val with\n")
    parts.extend(f"  | {i} => cellP{i:03d}Charge2546\n" for i in range(30))
    parts.append("  | _ => 0\n\n")
    parts.append("theorem cellChargeBound2546 (i : Fin 30) :\n"
                 "    (‖baseCoefficientCenter2540 i‖ + baseCoefficientError2540 i) *\n"
                 "      thirdCellTerm2544 i ≤ cellCharge2546 i := by\n  fin_cases i\n")
    parts.extend(f"  · exact cellP{i:03d}ChargeBound2546\n" for i in range(30))
    defs = ", ".join(f"cellP{i:03d}Charge2546" for i in range(30))
    parts.append(f"""
noncomputable def cellThirdUpper2546 : ℝ := {real(total)}

noncomputable def cellCurvatureUpper2546 : ℝ := {real(curvature)}

noncomputable def cellIntegralUpper2546 : ℝ := {real(integral)}

theorem cellThirdBound2546 : thirdAggregateUpper2544 ≤ cellThirdUpper2546 := by
  have h : thirdAggregateUpper2544 ≤ ∑ i : Fin 30, cellCharge2546 i :=
    Finset.sum_le_sum (fun i _ => cellChargeBound2546 i)
  apply h.trans
  rw [sum30_chain2541]
  norm_num [cellCharge2546, cellThirdUpper2546, {defs}]

theorem cellCurvatureBound2546 :
    signedCurvatureUpper2539 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 endpointLeftPosition2544 endpointRightPosition2544 ≤
        cellCurvatureUpper2546 := by
  have h := curvature_after_endpoints2544
  have ht := cellThirdBound2546
  norm_num [signedMidpointUpper2543, cellThirdUpper2546, cellCurvatureUpper2546,
    endpointLeftPosition2544, endpointRightPosition2544] at *
  linarith

theorem cellIntegralBound2546 (coefficients : Fin 30 → ℂ)
    (hcoeff : ∀ i, ‖coefficients i - baseCoefficientCenter2540 i‖ ≤ baseCoefficientError2540 i) :
    (∫ x in endpointLeftPosition2544..endpointRightPosition2544,
      ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 x‖) ≤
        cellIntegralUpper2546 := by
  have h := weightedPhysical2539_norm_integral_le_signed_cell (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541 hcoeff
    (a := endpointLeftPosition2544) (b := endpointRightPosition2544)
    (by norm_num [endpointLeftPosition2544, endpointRightPosition2544])
  have hl := adaptiveN05440PlusSigned_le2542
  have hr := adaptiveN05441PlusSigned_le2542
  have hc := cellCurvatureBound2546
  have hleft : adaptiveN05440PlusPosition2542 = endpointLeftPosition2544 := by
    norm_num [adaptiveN05440PlusPosition2542, endpointLeftPosition2544]
  have hright : adaptiveN05441PlusPosition2542 = endpointRightPosition2544 := by
    norm_num [adaptiveN05441PlusPosition2542, endpointRightPosition2544]
  rw [hleft] at hl
  rw [hright] at hr
  norm_num [endpointLeftPosition2544, endpointRightPosition2544, adaptiveN05440PlusUpper2542,
    adaptiveN05441PlusUpper2542, cellCurvatureUpper2546, cellIntegralUpper2546] at *
  linarith

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.cellChargeBound2546
#print axioms ConnesWeilRH.Dev.cellThirdBound2546
#print axioms ConnesWeilRH.Dev.cellCurvatureBound2546
#print axioms ConnesWeilRH.Dev.cellIntegralBound2546
""")
    lines = []
    output = "".join(parts)
    if sigma < 0:
        output = output.replace("(1/2)","(-1/2)")
    for line in output.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n",right_source,dict(third=str(total),curvature=str(curvature),
                                                  integral=str(integral),right=right_info)


if __name__ == "__main__":
    source,right,info = render()
    (ROOT/"ConnesWeilRH/Dev/C1RouteACellIntegral2546.lean").write_text(source,encoding="utf-8",newline="\n")
    (ROOT/"ConnesWeilRH/Dev/C1RouteACellRight2546.lean").write_text(right,encoding="utf-8",newline="\n")
    print("CELL_INTEGRAL_GENERATED",info,flush=True)
