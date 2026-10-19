#!/usr/bin/env python3
"""Independent exact-payload checker for record 3047."""
import json
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def main():
    d=json.loads((ROOT/"results/3047_cast_owner_whole_cell_enclosure.json").read_text())
    assert d["record"]==3047 and d["all_fit"] is True
    pin=Fraction("2.7790943782"); radius=Fraction(65536001,10000000); total_cells=0
    rows_out=[]
    for e in d["endpoints"]:
        assert e["cells"]==10240; h=2*radius/10240; nodes=Fraction(0); rems=Fraction(0)
        for i,row in enumerate(e["rows"]):
            assert row["index"]==i
            assert Fraction(row["left_exact"]) == -radius+i*h
            assert Fraction(row["right_exact"]) == -radius+(i+1)*h
            node=Fraction(row["node_upper_exact"]); second=Fraction(row["second_upper_exact"]); rem=Fraction(row["remainder_upper_exact"])
            assert node>=0 and second>=0 and rem >= h**3*second/12
            nodes += node; rems += rem; total_cells += 1
        nup=Fraction(e["node_upper_exact"]); rup=Fraction(e["remainder_upper_exact"]); total=Fraction(e["total_upper_exact"])
        assert nodes<=nup and rems<=rup and total==nup+rup and total<pin
        assert Fraction(e["margin_lower_exact"])==pin-total
        rows_out.append((e["sigma_exact"],float(total),float(pin-total)))
    out={"status":"CAST_OWNER_EXACT_PAYLOAD_PASS","cells_checked":total_cells,"endpoints":rows_out,"analytic_bounds_checked":False}
    print(json.dumps(out,indent=2))
if __name__=="__main__": main()
