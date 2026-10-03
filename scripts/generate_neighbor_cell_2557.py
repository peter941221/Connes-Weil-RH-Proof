"""Build cell2701 next to the accepted cell2700, retaining shared node2701."""
from fractions import Fraction as Q
import re

from generate_complex_exp_node_2541 import ROOT
from generate_boundary_jets_2548 import render as jet_template
from format_lean_source_2553 import wrap_source
from generate_endpoint_norms_2544 import render as norm_template
from generate_signed_midpoint_2543 import render as midpoint_template
from generate_boundary_fourth_2550 import render as fourth_template
from generate_adaptive_nodes_2542 import render as value_template
from generate_cell_integral_2546 import render as integral_template
from validate_adaptive_nodes_2542 import check as check_value


def render_value():
    source,info = value_template(2702,1,shared_node=True,shared_owner=owner("Right"))
    parent = (ROOT/"ConnesWeilRH/Dev/C1RouteANeighborRight2557.lean").read_text(encoding="utf-8")
    check_value(source,2702,1,shared_source=parent,shared_prefix="neighborRight",shared_record=2557)
    source = re.sub(r"\badaptiveN02702Plus(\w*)2542\b",lambda m:"neighborValueRight"+m[1]+"2557",source)
    assert source.count("BaseError2557") == 30 and "compactExp" not in source
    return wrap_source(source),info


def render_integral():
    norms = []
    for side in ("Left","Right"):
        source = render_norm(side)
        source = re.sub(r"\bneighbor"+side+r"(\w*)2557\b",lambda m:"endpoint"+side+m[1]+"2544",source)
        norms.append(re.sub(r":\s*([ℝℚ])",r": \1",source))
    fourth = re.sub(r"\bneighborFourth(P\d{3}\w*)2557\b",lambda m:"fourth"+m[1]+"2545",render_fourth()[0])
    fourth = re.sub(r":\s*([ℝℚ])",r": \1",fourth)
    value,vi = render_value()
    source,_,info = integral_template(cell_index=2701,sources=(*norms,fourth),
        midpoint_upper=render_midpoint()[1],left_upper=Q(873,10**10),right_node=(value,vi))
    for i in range(30):
        replacement = f"""    unfold thirdCellTerm2544
    norm_num [endpointLeftNormUpper2544, endpointRightNormUpper2544,
      endpointLeftP{i:03d}NormUpper2544, endpointRightP{i:03d}NormUpper2544,
      neighborFourthUpper2557, fourthP{i:03d}Upper2545,
      endpointLeftPosition2544, endpointRightPosition2544]
"""
        pattern = r"    unfold thirdCellTerm2544\n    have h := fourthP"+f"{i:03d}"+r"Bound2545\n.*?    linarith\n"
        source,count = re.subn(pattern,replacement,source,count=1,flags=re.S)
        assert count == 1
    for old,new in {
        "C1RouteAFourthEnvelope2545":"C1RouteANeighborAssembly2557",
        "C1RouteACellRight2546":"C1RouteANeighborValueRight2557",
        "C1RouteAAdaptiveN05440Plus2542":"C1RouteASharedN02701Plus2556",
        "thirdCellTerm2544":"neighborThirdCell2557",
        "thirdAggregateUpper2544":"neighborThirdAggregate2557",
        "curvature_after_endpoints2544":"neighborCurvature_bound2557",
        "signedMidpointUpper2543":"neighborSignedMidpointUpper2557",
        "endpointLeftPosition2544":"kernelN02701PlusPosition2555",
        "endpointRightPosition2544":"neighborRightPosition2557",
    }.items():
        source = source.replace(old,new)
    for old,new,record in (("adaptiveN05440Plus","sharedN02701Plus",2556),
                           ("adaptiveN05441Plus","neighborValueRight",2557)):
        source = re.sub(r"\b"+old+r"(\w*)2542\b",lambda m:new+m[1]+str(record),source)
    source = re.sub(r"\bendpoint(Left|Right)(\w*)2544\b",lambda m:"neighbor"+m[1]+m[2]+"2557",source)
    source = re.sub(r"\bfourth(P\d{3}\w*)2545\b",lambda m:"neighborFourth"+m[1]+"2557",source)
    source = re.sub(r"\bcell(\w*)2546\b",lambda m:"neighborCell"+m[1]+"2557",source)
    return wrap_source(source),value,info


def owner(side):
    if side == "Left":
        return "kernelN02701Plus",2555,"C1RouteAKernelN02701Plus2555"
    return "neighbor"+side,2557,"C1RouteANeighbor"+side+"2557"


def render_norm(side):
    prefix,record,module = owner(side)
    source = (ROOT/f"ConnesWeilRH/Dev/{module}.lean").read_text(encoding="utf-8")
    normalized = re.sub(r"\b"+prefix+r"(\w*)"+str(record)+r"\b",lambda m:"endpoint"+side+m[1]+"2544",source)
    out = norm_template(side,30,source=normalized,bits=160)
    out = out.replace("C1RouteAEndpoint"+side+"Third2544",module)
    def rename(m):
        suffix = m[1]
        if suffix == "Position" or re.fullmatch(r"P\d{3}(Factor|Center|Error|DerivativeError)",suffix):
            return prefix+suffix+str(record)
        return "neighbor"+side+suffix+"2557"
    return wrap_source(re.sub(r"\bendpoint"+side+r"(\w*)2544\b",rename,out))


def render_midpoint():
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteANeighborMidpoint2557.lean").read_text(encoding="utf-8")
    normalized = re.sub(r"\bneighborMidpoint(\w*)2557\b",lambda m:"midpoint"+m[1]+"2543",source)
    out,upper,charge = midpoint_template(source=normalized)
    out = out.replace("C1RouteAMidpointDerivatives2543","C1RouteANeighborMidpoint2557")
    out = re.sub(r"\bmidpoint(\w*)2543\b",lambda m:"neighborMidpoint"+m[1]+"2557",out)
    out = re.sub(r"\bsignedMidpoint(\w*)2543\b",lambda m:"neighborSignedMidpoint"+m[1]+"2557",out)
    out = out.replace("weightedPhysical_second_midpoint_le2543","neighborPhysicalSecond2557")
    return wrap_source(out),upper,charge


def render_fourth():
    source,rows = fourth_template(cell_index=2701)
    source = source.replace("C1RouteABoundaryLeft2548","C1RouteAKernelN02701Plus2555")
    source = source.replace("C1RouteABoundaryRight2548","C1RouteANeighborRight2557")
    source = source.replace("edgeLeftPosition2548","kernelN02701PlusPosition2555")
    source = source.replace("edgeRightPosition2548","neighborRightPosition2557")
    source = re.sub(r"\bedgeFourth(\w*)2550\b",lambda m:"neighborFourth"+m[1]+"2557",source)
    source = source.replace(":= by cbv",":= by decide +kernel")
    return wrap_source(source),rows


def render_assembly():
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryAssembly2550.lean").read_text(encoding="utf-8")
    for old,new in (("C1RouteABoundaryFourth2550","C1RouteANeighborFourth2557"),
                    ("C1RouteABoundaryLeftBounds2549","C1RouteANeighborLeftBounds2557"),
                    ("C1RouteABoundaryRightBounds2549","C1RouteANeighborRightBounds2557"),
                    ("C1RouteABoundaryMidpointBounds2549","C1RouteANeighborMidpointBounds2557"),
                    ("edgeLeftPosition2548","kernelN02701PlusPosition2555")):
        source = source.replace(old,new)
    source = re.sub(r"\bedge(\w*)25(?:48|49|50)\b",lambda m:"neighbor"+m[1]+"2557",source)
    return wrap_source(source)


def render_jet(side):
    grid,order = {"Right":(Q(2702),3),"Midpoint":(Q(5403,2),2)}[side]
    source,active = jet_template(side,grid_order=(grid,order),paired=True)
    source = source.replace(":= by cbv",":= by decide +kernel")
    source = re.sub(r"\bedge"+side+r"(\w*)2548\b",lambda m:"neighbor"+side+m[1]+"2557",source)
    return wrap_source(source),active


def write(name,source):
    (ROOT/f"ConnesWeilRH/Dev/C1RouteANeighbor{name}2557.lean").write_text(source,encoding="utf-8",newline="\n")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--assembly",action="store_true")
    args = parser.parse_args()
    for side in ("Right","Midpoint"):
        source,active = render_jet(side)
        write(side,source)
        print(side,"active",len(active),flush=True)
    if args.assembly:
        assert fourth_template()[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryFourth2550.lean").read_text(encoding="utf-8")
        for side in ("Left","Right"):
            write(side+"Bounds",render_norm(side))
        source,upper,charge = render_midpoint()
        write("MidpointBounds",source)
        print("midpoint upper",upper,"charge",float(charge),flush=True)
        source,rows = render_fourth()
        write("Fourth",source)
        write("Assembly",render_assembly())
        source,value,info = render_integral()
        write("ValueRight",value)
        write("Integral",source)
        print("neighbor integral",info,flush=True)
