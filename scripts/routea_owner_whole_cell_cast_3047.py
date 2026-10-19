#!/usr/bin/env python3
"""Record 3047: Arb whole-cell enclosure for the exact 2678 cast owner."""
from __future__ import annotations
import json, re, struct, hashlib, time
from fractions import Fraction
from pathlib import Path
import flint
from flint import acb, arb, ctx
import routea_owner_whole_cell_2535 as base

ROOT = Path(__file__).resolve().parents[1]

def load_cast_families():
    src=(ROOT/"ConnesWeilRH/Dev/C1RouteARepairedOwnerCell2678.lean").read_text(encoding="utf-8")
    src=src.split("noncomputable def record2678BaseM0FamilyRects")[0]
    pairs=re.findall(r"⟨binary64Value2674\s+(\d+),\s*binary64Value2674\s+(\d+)⟩",src)
    cap=json.loads((ROOT/"results/2275_gap_owner_audit.json").read_text())["owner_capture"]
    out=[]
    for (rb,ib), row in zip(pairs, cap["families_hex"]):
        r=Fraction.from_float(float.fromhex(row[0]))**2
        rv=struct.unpack(">d",int(rb).to_bytes(8,"big"))[0]
        iv=struct.unpack(">d",int(ib).to_bytes(8,"big"))[0]
        theta=float.fromhex(row[1])
        out.append(dict(r=r, radius=base.lift(r), theta=base.lift(Fraction.from_float(theta)),
                        center=acb(base.lift(Fraction.from_float(rv)), base.lift(Fraction.from_float(iv))),
                        error=arb(0), scale=base.upper(abs(acb(base.lift(Fraction.from_float(rv)), base.lift(Fraction.from_float(iv)))))))
    if len(out)!=30: raise ValueError("expected 30 cast-owner families")
    return out

def main():
    ctx.prec=192
    started=time.monotonic(); families=load_cast_families()
    endpoints=[base.run_grid(families,10240,sign,True) for sign in (Fraction(-1,2),Fraction(1,2))]
    result={"record":3047,"status":"EXTERNAL_WHOLE_CELL_CAST_OWNER_ENCLOSURE_NOT_LEAN",
            "precision_bits":ctx.prec,"python_flint_version":flint.__version__,
            "owner":"record2678BaseCoefficient binary64 casts; zero coefficient radius",
            "endpoints":endpoints,"all_fit":all(e["fits_pin"] for e in endpoints),
            "elapsed_seconds":time.monotonic()-started,
            "lean_certificate_imported":False,"chargeRest_identity":False,"producer_go":False,"rh_claim":False}
    out=ROOT/"results/3047_cast_owner_whole_cell_enclosure.json"; out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"all_fit":result["all_fit"],"endpoints":endpoints,"elapsed_seconds":result["elapsed_seconds"]},indent=2))
if __name__=="__main__": main()
