"""Generate actual third derivatives at the two endpoints of cell 5440."""
import argparse
import re
import textwrap

from generate_complex_exp_node_2541 import ROOT
from generate_midpoint_derivatives_2543 import render as render_derivatives


def render(side, count=30):
    index = {"Left":5440,"Right":5441}[side]
    source = render_derivatives(count,order=3,grid_index=index)
    renamed = re.sub(r"\bmidpoint(\w*)2543\b",
                     lambda m: "endpoint"+side+m[1]+"2544",source)
    lines = []
    for line in renamed.splitlines():
        indent = len(line)-len(line.lstrip())
        lines.extend(textwrap.wrap(line,width=98,subsequent_indent=" "*(indent+4),
                                   break_long_words=False,break_on_hyphens=False) or [""])
    return "\n".join(lines)+"\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--side",choices=("Left","Right"),required=True)
    parser.add_argument("--count",type=int,choices=range(1,31),default=30)
    args = parser.parse_args()
    # The extended shared generator must preserve the accepted midpoint file.
    prior = ROOT/"ConnesWeilRH/Dev/C1RouteAMidpointDerivatives2543.lean"
    assert prior.read_text() == render_derivatives(30), "prior midpoint generation changed"
    target = ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{args.side}Third2544.lean"
    target.write_text(render(args.side,args.count),encoding="utf-8",newline="\n")
    print("ENDPOINT_THIRD_GENERATED",args.side,args.count,flush=True)
