#!/usr/bin/env python3
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MOD='ConnesWeilRH/Dev/C1SeedRationalTransitionJet2738'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ws=Path(sys.argv[1]); log=ws/'build-logs/2738_rational_transition_jet.log'; body=log.read_text(encoding='utf-8')
    src=(ROOT/(MOD+'.lean')).read_text(encoding='utf-8'); aud=(ROOT/(MOD+'Audit.lean')).read_text()
    names=re.findall(r'^theorem (\w+)\b',src,re.M); pins=re.findall(r'^#print axioms (\w+)\s*$',aud,re.M)
    checks={'footer':'Build completed successfully' in body,'no_errors':not re.search(r'^error:',body,re.M),'decl_audit':pins==['rationalSeedTransitionJet_mem2738'],'source_copy':sha(ROOT/(MOD+'.lean'))==sha(ws/(MOD+'.lean')),'audit_copy':sha(ROOT/(MOD+'Audit.lean'))==sha(ws/(MOD+'Audit.lean'))}
    hits=re.findall(r'depends on axioms: \[([^\]]+)\]',body)
    checks['standard_axioms']=bool(hits) and all([x.strip() for x in hits[-1].replace('\n',' ').split(',')]==['propext','Classical.choice','Quot.sound'] for x in hits[-1:])
    out={'record':2738,'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'source_sha256':sha(ROOT/(MOD+'.lean')),'checker_sha256':sha(Path(__file__)),'nonclaims':['No floating-point outward replay, finite integration, D4/D7, pins, carrier or RH claim.']}
    (ROOT/'results/2738_rational_transition_jet.json').write_text(json.dumps(out,indent=2)+'\n')
    for k,v in checks.items(): print(('PASS ' if v else 'FAIL ')+k)
    return 0 if all(checks.values()) else 1
if __name__=='__main__': raise SystemExit(main())


