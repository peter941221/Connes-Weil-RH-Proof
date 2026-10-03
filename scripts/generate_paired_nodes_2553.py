"""Complete 30-family paired derivative certificates on a support ladder."""
from fractions import Fraction as Q
import json
import re

from generate_boundary_replay_2547 import ROOT, render as render_one
from generate_boundary_jets_2548 import render as render_jets, CASES as OLD_CASES
from validate_boundary_jets_2548 import check
from format_lean_source_2553 import wrap_source

CASES = {f"N{grid:05d}{label}": (Q(grid), Q(sign,2))
         for grid in (2700,2701,5440,10239)
         for label,sign in (("Plus",1),("Minus",-1))}


def render(name):
    grid,sigma = CASES[name]
    source,active = render_jets(name,grid_order=(grid,3),sigma=sigma,paired=True)
    report = check(source,name,grid_order=(grid,3),sigma=sigma)
    assert report["active"] == active
    # Only newly declared node names move to record2553; imported names stay.
    before = source
    source = re.sub(r"\bedge"+name+r"(\w*)2548\b",lambda m:"paired"+name+m[1]+"2553",source)
    assert re.findall(r"(?<!\w)\d+",source) == re.findall(r"(?<!\w)\d+",before)
    return wrap_source(source),dict(report,sigma=str(sigma))


def main():
    assert render_one()[0] == (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryReplay2547.lean").read_text(encoding="utf-8")
    for side in OLD_CASES:
        assert render_jets(side)[0] == (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}2548.lean").read_text(encoding="utf-8")
    reports = []
    for name in CASES:
        source,report = render(name)
        (ROOT/f"ConnesWeilRH/Dev/C1RouteAPaired{name}2553.lean").write_text(source,encoding="utf-8",newline="\n")
        reports.append(report)
        print(name,len(report["active"]),"active",flush=True)
    (ROOT/"results/2553_paired_node_inputs.json").write_text(json.dumps(dict(record=2553,cases=reports,
        defaults_byte_identical=True,formal_build_verified=False,full_grid_certificate=False),indent=2)+"\n")


if __name__ == "__main__":
    main()
