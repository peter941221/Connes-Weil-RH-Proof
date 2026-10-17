#!/usr/bin/env python3
import argparse,hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MOD="ConnesWeilRH/Dev/C1SeedRationalPhaseBox2736"
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    pa=argparse.ArgumentParser(); pa.add_argument("--workspace",type=Path,required=True); a=pa.parse_args()
    log=a.workspace/"build-logs/2736_rational_phase_box.log"; body=log.read_text(encoding="utf-8")
    src=(ROOT/(MOD+".lean")).read_text(encoding="utf-8"); aud=(ROOT/(MOD+"Audit.lean")).read_text(encoding="utf-8")
    names=re.findall(r"^theorem (\w+)\b",src,re.M); pins=re.findall(r"^#print axioms (\w+)\s*$",aud,re.M)
    checks={"footer":bool(re.search(r"^Build completed successfully \(\d+ jobs\)\.$",body,re.M)),"no_errors":not re.search(r"^error:",body,re.M),"no_warnings":not re.search(r"^warning: "+re.escape(MOD),body,re.M),"decl_audit":names==pins==["rationalPhaseExpBox_mem2736","representativePhaseExpBox_mem2736"],"source_copy":sha(ROOT/(MOD+".lean"))==sha(a.workspace/(MOD+".lean")),"audit_copy":sha(ROOT/(MOD+"Audit.lean"))==sha(a.workspace/(MOD+"Audit.lean")),"representative_pins":all(x in src for x in ["representativeCell2736","hP","hcap"])}
    hits=re.findall(r"depends on axioms: \[([^\]]*)\]",body)
    checks["standard_axioms"]=len(hits)>=2 and all([x.strip() for x in h.replace("\n"," ").split(",")] == ["propext","Classical.choice","Quot.sound"] for h in hits[-2:])
    out={"record":2736,"status":"PASS" if all(checks.values()) else "FAIL","checks":checks,"source_sha256":sha(ROOT/(MOD+".lean")),"checker_sha256":sha(Path(__file__)),"nonclaims":["No full-cell replay or D4/D7 integral certificate."]}
    (ROOT/"results/2736_rational_phase_box.json").write_text(json.dumps(out,indent=2)+"\n")
    for k,v in checks.items(): print(("PASS " if v else "FAIL ")+k)
    return 0 if all(checks.values()) else 1
if __name__=="__main__":sys.exit(main())
