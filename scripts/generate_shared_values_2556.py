"""Signed endpoint values consuming the existing order0/order3 replay."""
import json
import re

from generate_adaptive_nodes_2542 import ROOT, render as template
from generate_paired_nodes_2553 import CASES
from format_lean_source_2553 import wrap_source
from validate_adaptive_nodes_2542 import check


def render(name):
    index,sigma = CASES[name]
    index,sign = int(index),1 if sigma > 0 else -1
    source,info = template(index,sign,shared_node=True)
    parent = (ROOT/f"ConnesWeilRH/Dev/C1RouteAKernel{name}2555.lean").read_text(encoding="utf-8")
    check(source,index,sign,shared_source=parent)
    source = re.sub(r"\badaptive"+name+r"(\w*)2542\b",lambda m:"shared"+name+m[1]+"2556",source)
    source = wrap_source(source)
    assert "compactExp" not in source and "cbv" not in source and "decide" not in source
    assert source.count("BaseError2555") == 30
    return source,info


if __name__ == "__main__":
    for index in (5440,10239):
        for sign in (1,-1):
            name = f"N{index:05d}{'Plus' if sign>0 else 'Minus'}"
            assert template(index,sign)[0] == (ROOT/f"ConnesWeilRH/Dev/C1RouteAAdaptive{name}2542.lean").read_text(encoding="utf-8")
    reports = []
    for name in CASES:
        source,info = render(name)
        (ROOT/f"ConnesWeilRH/Dev/C1RouteAShared{name}2556.lean").write_text(source,encoding="utf-8",newline="\n")
        reports.append(info)
        print(name,info["upper"],flush=True)
    (ROOT/"results/2556_shared_value_inputs.json").write_text(json.dumps(dict(record=2556,cases=reports,
        new_exponential_replays=0,full_grid_certificate=False),indent=2)+"\n")
