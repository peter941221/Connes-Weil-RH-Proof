#!/usr/bin/env python3
"""Diagnose the first Route B phase-box gate mismatch exactly."""
from fractions import Fraction
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = json.loads((ROOT / "results/2840_route_b_cell4096_stage_bridge.json").read_text())

def F(s):
    if isinstance(s, int): return Fraction(s)
    a, b = s.split("/")
    return Fraction(int(a), int(b))

def add(a,b): return (a[0]+b[0], a[1]+b[1])
def sub(a,b): return (a[0]-b[1], a[1]-b[0])
def mul(a,b):
    q=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(q),max(q)
def inv(a): return (1/a[1],1/a[0])
def scale(c,a): return (c*a[0],c*a[1])
def recip(X):
    out=[inv(X[0])]
    for n in range(len(X)-1):
        z=(Fraction(0),Fraction(0))
        for j in range(n+1): z=add(z,scale(F(math.comb(n+1,j+1)),mul(X[j+1],out[n-j])))
        out.append(mul(sub((Fraction(0),Fraction(0)),z),inv(X[0])))
    return out
def box(z): return F(z["lo"]),F(z["hi"])

def main():
    B=(Fraction(8392704,33554432),Fraction(8394751,33554432))
    U=[B,(Fraction(1),Fraction(1)),(Fraction(0),Fraction(0))]
    V=[sub((Fraction(1),Fraction(1)),B),(Fraction(-1),Fraction(-1)),(Fraction(0),Fraction(0))]
    lean= [sub(a,b) for a,b in zip(recip(V),recip(U))]
    py=[box(z) for z in DATA["orders"]["7"]["phase"][:3]]
    rows=[]
    for k,(a,b) in enumerate(zip(lean,py)):
        rows.append({"k":k,"lean_lo":str(a[0]),"lean_hi":str(a[1]),
                     "python_lo":str(b[0]),"python_hi":str(b[1]),
                     "lower_delta_lean_minus_python":str(a[0]-b[0]),
                     "upper_delta_python_minus_lean":str(b[1]-a[1]),
                     "python_contains_lean":b[0] <= a[0] and a[1] <= b[1]})
    out={"record":2846,"status":"DIAGNOSED","cell":4096,"rows":rows,
         "nonclaims":["Lean theorem","ledger domination","SourceRH","RH"]}
    path=ROOT/"results/2846_route_b_phase_gate_diagnosis.json"
    path.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
if __name__ == "__main__": main()
