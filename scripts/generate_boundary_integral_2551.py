"""Assemble the complete support-crossing cell2700 numerical integral."""
from fractions import Fraction as Q
import re

from generate_complex_exp_node_2541 import ROOT
from generate_adaptive_nodes_2542 import render as node
from generate_cell_integral_2546 import render as template
from generate_boundary_bounds_2549 import wrap
from validate_boundary_bounds_2549 import normalize_norm


def render():
    left_node,left_info = node(2700,1)
    left,right = (normalize_norm((ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{s}Bounds2549.lean").read_text(),s)
                  for s in ("Left","Right"))
    fourth = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryFourth2550.lean").read_text()
    fourth = re.sub(r"\bedgeFourth(P\d{3}\w*)2550\b",lambda m:"fourth"+m[1]+"2545",fourth)
    fourth = re.sub(r":\s*([ℝℚ])",r": \1",fourth)
    source,right_node,info = template(cell_index=2700,sources=(left,right,fourth),
                                    midpoint_upper=Q(8777,50000000),left_upper=Q(left_info["upper"]))
    for i in range(30):
        replacement = f"""    unfold thirdCellTerm2544
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP{i:03d}NormUpper2544, endpointRightP{i:03d}NormUpper2544,
      edgeFourthUpper2550, fourthP{i:03d}Upper2545,
      endpointLeftPosition2544, endpointRightPosition2544]
"""
        pattern = r"    unfold thirdCellTerm2544\n    have h := fourthP"+f"{i:03d}"+r"Bound2545\n.*?    linarith\n"
        source,count = re.subn(pattern,replacement,source,count=1,flags=re.S)
        assert count == 1
    mapping = {
        "C1RouteAFourthEnvelope2545":"C1RouteABoundaryAssembly2550",
        "C1RouteACellRight2546":"C1RouteABoundaryValueRight2551",
        "C1RouteAAdaptiveN05440Plus2542":"C1RouteABoundaryValueLeft2551",
        "thirdCellTerm2544":"edgeThirdCell2550",
        "thirdAggregateUpper2544":"edgeThirdAggregate2550",
        "curvature_after_endpoints2544":"edgeCurvature_bound2550",
        "signedMidpointUpper2543":"edgeSignedMidpointUpper2549",
        "adaptiveN05440Plus":"adaptiveN02700Plus",
        "adaptiveN05441Plus":"adaptiveN02701Plus",
    }
    for old,new in mapping.items():
        source = source.replace(old,new)
    source = re.sub(r"\bendpoint(Left|Right)(\w*)2544\b",
                    lambda m:"edge"+m[1]+m[2]+("2548" if m[2]=="Position" else "2549"),source)
    source = re.sub(r"\bfourth(P\d{3}\w*)2545\b",lambda m:"edgeFourth"+m[1]+"2550",source)
    source = re.sub(r"\bcell(\w*)2546\b",lambda m:"boundaryCell"+m[1]+"2551",source)
    return wrap(source),left_node,right_node,dict(**info,left=left_info)


if __name__ == "__main__":
    assert template()[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteACellIntegral2546.lean").read_text()
    source,left,right,info = render()
    for name,data in (("Integral",source),("ValueLeft",left),("ValueRight",right)):
        (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{name}2551.lean").write_text(data,encoding="utf-8",newline="\n")
    print("BOUNDARY_INTEGRAL_GENERATED",info,flush=True)
