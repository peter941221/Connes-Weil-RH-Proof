#!/usr/bin/env python3
"""Reprice Route B cell 4096 stages under the Lean-proved e0 box."""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "scripts/measure_route_b_replay_inflation_2842.py"
DATA = json.loads((ROOT / "results/2840_route_b_cell4096_stage_bridge.json").read_text())
spec = importlib.util.spec_from_file_location("m2852", SRC)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def sbox(a): return {"lo": str(a[0]), "hi": str(a[1])}
def main():
    order = 7
    stages = DATA["orders"][str(order)]
    phase = [m.bx(z) for z in stages["phase"]]
    e0 = (Fraction(1, 32), Fraction(1, 4))
    exp = m.expo(phase, e0)
    den = [m.add(exp[0], (Fraction(1), Fraction(1)))] + exp[1:]
    rec = m.recip(den)
    trans = m.product(exp, rec)
    tight = [m.bx(z) for z in stages["transition"]]
    rows=[]
    for k,(a,t) in enumerate(zip(trans,tight)):
        tw=t[1]-t[0]; rw=a[1]-a[0]
        rows.append({"k":k,"broad_width":str(rw),"tight_width":str(tw),
                     "width_ratio_float":float(rw/tw),
                     "broad_transition":sbox(a)})
    out={"record":2852,"status":"REPRICED_BROAD_E0","order":order,
         "cell":4096,"e0":"[1/32,1/4]",
         "phase": [sbox(x) for x in phase], "exp":[sbox(x) for x in exp],
         "denominator":[sbox(x) for x in den], "reciprocal":[sbox(x) for x in rec],
         "transition":rows,
         "nonclaims":["Lean enclosure", "ledger domination", "SourceRH", "RH"]}
    (ROOT/"results/2852_route_b_broad_e0_reprice.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"record":2852,"width_ratios":[r["width_ratio_float"] for r in rows]}))
if __name__ == "__main__": main()
