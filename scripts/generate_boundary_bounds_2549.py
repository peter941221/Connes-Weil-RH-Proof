"""Reuse accepted assembly templates on the certified cell2700 jets."""
import argparse
import re
import textwrap

from generate_complex_exp_node_2541 import ROOT
from generate_endpoint_norms_2544 import render as norm_template
from generate_signed_midpoint_2543 import render as signed_template


def wrap(source):
    lines = []
    for line in source.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                  break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n"


def render_norm(side):
    source = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}2548.lean").read_text()
    normalized = re.sub(r"\bedge"+side+r"(\w*)2548\b",lambda m:"endpoint"+side+m[1]+"2544",source)
    out = norm_template(side,30,source=normalized,bits=160)
    out = out.replace(f"C1RouteAEndpoint{side}Third2544",f"C1RouteABoundary{side}2548")
    def rename(m):
        suffix = m[1]
        record = 2548 if suffix == "Position" or re.fullmatch(r"P\d{3}(Factor|Center|Error|DerivativeError)",suffix) else 2549
        return "edge"+side+suffix+str(record)
    out = re.sub(r"\bendpoint"+side+r"(\w*)2544\b",rename,out)
    return wrap(out)


def render_midpoint():
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryMidpoint2548.lean").read_text()
    normalized = re.sub(r"\bedgeMidpoint(\w*)2548\b",lambda m:"midpoint"+m[1]+"2543",source)
    out,upper,charge = signed_template(source=normalized)
    out = out.replace("C1RouteAMidpointDerivatives2543","C1RouteABoundaryMidpoint2548")
    def rename(m):
        suffix = m[1]
        record = 2548 if suffix == "Position" or re.fullmatch(r"P\d{3}(Factor|Center|Error|DerivativeError)",suffix) else 2549
        return "edgeMidpoint"+suffix+str(record)
    out = re.sub(r"\bmidpoint(\w*)2543\b",rename,out)
    out = re.sub(r"\bsignedMidpoint(\w*)2543\b",lambda m:"edgeSignedMidpoint"+m[1]+"2549",out)
    out = out.replace("weightedPhysical_second_midpoint_le2543","weightedPhysical_edge_midpoint_le2549")
    return wrap(out),upper,charge


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--side",choices=("Left","Right","Midpoint"),required=True)
    args = parser.parse_args()
    # A template extension must preserve its original accepted artifacts.
    assert signed_template()[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteASignedMidpoint2543.lean").read_text()
    for side in ("Left","Right"):
        assert norm_template(side,30) == (ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Norms2544.lean").read_text()
    if args.side == "Midpoint":
        source,upper,charge = render_midpoint()
        print("EDGE_MIDPOINT",str(upper),"charge",float(charge),flush=True)
    else:
        source = render_norm(args.side)
    (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{args.side}Bounds2549.lean").write_text(source,encoding="utf-8",newline="\n")
    print("BOUNDARY_BOUNDS_GENERATED",args.side,flush=True)
