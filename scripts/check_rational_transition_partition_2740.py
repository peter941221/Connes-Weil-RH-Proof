#!/usr/bin/env python3
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MOD='ConnesWeilRH/Dev/C1RationalTransitionPartition2740'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ws=Path(sys.argv[1]); body=(ws/'build-logs/2740_rational_transition_partition.log').read_text(encoding='utf-8')
    src=(ROOT/(MOD+'.lean')).read_text(encoding='utf-8'); aud=(ROOT/(MOD+'Audit.lean')).read_text(encoding='utf-8')
    expected=['partitionRationalTransitionJet_mem2740','representativeCell_partition2740','representativeRationalTransitionPartition_mem2740','partitionCells_ordered2740','partitionCells_subset2740']
    pins=re.findall(r'^#print axioms (\w+)\s*$',aud,re.M); hits=re.findall(r'depends on axioms: \[([^\]]+)\]',body)
    checks={'footer':'Build completed successfully' in body,'no_errors':not re.search(r'^error:',body,re.M),'decl_audit':pins==expected,'source_copy':sha(ROOT/(MOD+'.lean'))==sha(ws/(MOD+'.lean')),'audit_copy':sha(ROOT/(MOD+'Audit.lean'))==sha(ws/(MOD+'Audit.lean')),'standard_axioms':len(hits)>=5 and all([x.strip() for x in h.replace('\n',' ').split(',')]==['propext','Classical.choice','Quot.sound'] for h in hits[-5:])}
    out={'record':'2740','status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'source_sha256':sha(ROOT/(MOD+'.lean')),'checker_sha256':sha(Path(__file__)),'nonclaims':['No outward floating-point replay, full partition integral, D4/D7, pins or RH claim.']}
    (ROOT/'results/2740_rational_transition_partition.json').write_text(json.dumps(out,indent=2)+'\n')
    for k,v in checks.items(): print(('PASS ' if v else 'FAIL ')+k)
    return 0 if all(checks.values()) else 1
if __name__=='__main__': raise SystemExit(main())
