"""Same four accepted paired transfers, using kernel reduction for replay."""
import re
from generate_complex_exp_node_2541 import ROOT
from generate_paired_nodes_2553 import CASES
from format_lean_source_2553 import wrap_source


def render():
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteABatchPaired2552.lean").read_text(encoding="utf-8")
    assert source.count(":= by cbv") == 4
    source = source.replace(":= by cbv",":= by decide +kernel")
    return wrap_source(re.sub(r"\bbatchPaired(\w*)2547\b",lambda m:"kernelTrial"+m[1]+"2555",source))


def render_node(name):
    source = (ROOT/f"ConnesWeilRH/Dev/C1RouteAPaired{name}2553.lean").read_text(encoding="utf-8")
    before = source
    source = source.replace(":= by cbv",":= by decide +kernel")
    source = re.sub(r"\bpaired"+name+r"(\w*)2553\b",lambda m:"kernel"+name+m[1]+"2555",source)
    assert re.findall(r"(?<!\w)\d+",source) == re.findall(r"(?<!\w)\d+",before)
    return wrap_source(source)


if __name__ == "__main__":
    (ROOT/"ConnesWeilRH/Dev/C1RouteAKernelTrial2555.lean").write_text(render(),encoding="utf-8",newline="\n")
    for name in CASES:
        (ROOT/f"ConnesWeilRH/Dev/C1RouteAKernel{name}2555.lean").write_text(render_node(name),encoding="utf-8",newline="\n")
