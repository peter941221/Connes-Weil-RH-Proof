#!/usr/bin/env python3
"""Record 3046: C3' sensitivity to the exact 2678 midpoint-cast owner."""
from __future__ import annotations
import json, re, struct, sys
from fractions import Fraction
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_owner_signed_grid_refinement_2533 as base

def load_cast_owner():
    src=(ROOT/"ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2678.lean").read_text(encoding="utf-8")
    src=src.split("noncomputable def record2678BaseM0FamilyRects")[0]
    pairs=re.findall(r"⟨binary64Value2674\s+(\d+),\s*binary64Value2674\s+(\d+)⟩",src)
    cap=json.loads((ROOT/"results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    fs=[]
    for (rb,ib), row in zip(pairs, cap["families_hex"]):
        r=Fraction.from_float(float.fromhex(row[0]))**2
        reals=struct.unpack(">d",int(rb).to_bytes(8,"big"))[0]
        imags=struct.unpack(">d",int(ib).to_bytes(8,"big"))[0]
        theta=float.fromhex(row[1])
        fs.append({"re":mp.mpf(reals),"im":mp.mpf(imags),"err":mp.mpf(0),
                   "radius":mp.mpf(r.numerator)/r.denominator,"mod":mp.mpf(theta)})
    return fs

def main():
    base.mp.mp.dps=60
    fs=load_cast_owner(); rows=[]
    for cells in (2560,5120):
        for sigma in (base.mp.mpf("-0.5"),base.mp.mpf("0.5")):
            r=base.run_grid(fs,cells,sigma,17)
            rows.append({"cells":cells,"sigma":str(sigma),"total":r["total_with_node"],
                         "margin":r["base_endpoint_margin"],"curvature_ratio":r["curvature_ratio"]})
    out={"record":3046,"status":"EXACT_2678_CAST_OWNER_SENSITIVITY","rows":rows,
         "owner":"record2678BaseCoefficient binary64 casts; zero coefficient-radius",
         "nonclaims":["not whole-cell Arb enclosure","not Lean import","no chargeRest identity","no Producer GO","no RH"]}
    (ROOT/"results/3046_cast_owner_margin.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
if __name__=="__main__": main()
