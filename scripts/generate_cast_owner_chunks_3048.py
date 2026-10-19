#!/usr/bin/env python3
"""Record 3048: exact 32-cell chunk sums for the 3047 payload."""
import json
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
def main():
    src=json.loads((ROOT/"results/3047_cast_owner_whole_cell_enclosure.json").read_text())
    chunks=[]
    for endpoint in src["endpoints"]:
        rows=endpoint["rows"]; assert len(rows)==10240
        vals=[Fraction(r["node_upper_exact"])+Fraction(r["remainder_upper_exact"]) for r in rows]
        for start in range(0,len(vals),32):
            chunks.append({"sigma":endpoint["sigma_exact"],"start":start,"end":start+32,
                           "sum_exact":str(sum(vals[start:start+32]))})
    assert len(chunks)==640
    sums={s:sum(Fraction(c["sum_exact"]) for c in chunks if c["sigma"]==s) for s in ("-1/2","1/2")}
    totals={e["sigma_exact"]:Fraction(e["total_upper_exact"]) for e in src["endpoints"]}
    assert all(sums[s] <= totals[s] for s in sums)
    out={"record":3048,"status":"CAST_OWNER_CHUNK_SUMS_EXACT","chunk_size":32,
         "chunk_count":len(chunks),"chunks":chunks,
         "endpoint_chunk_sums":{s:str(v) for s,v in sums.items()},
         "endpoint_totals":{s:str(v) for s,v in totals.items()},
         "chunk_sum_le_endpoint_total":True,
         "source":"results/3047_cast_owner_whole_cell_enclosure.json",
         "nonclaims":["no Lean import","no live chargeRest identity","no Producer GO","no RH"]}
    (ROOT/"results/3048_cast_owner_chunk_sums.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({k:out[k] for k in ("record","chunk_count","chunk_sum_le_endpoint_total","endpoint_chunk_sums")},indent=2))
if __name__=="__main__": main()
