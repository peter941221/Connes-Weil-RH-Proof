#!/usr/bin/env python3
from fractions import Fraction as F
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def taylor(y):
    s=F(0)
    fact=1
    for i in range(20):
        if i: fact*=i
        s += y**i/fact
    return s
def tail(y): return y**20*F(21,20*fact20)
fact20=1
for i in range(1,21): fact20*=i
def phase(x): return 1/(1-x)-1/x
def box(lo,hi,m=4):
    a=-lo/F(m); b=-hi/F(m)
    return 1/(taylor(a)+tail(a))**m, 1/(taylor(b)-tail(b))**m
def main():
    lo=F(2049,8192); hi=F(8394751,33554432); mid=(lo+hi)/2
    rows=[]
    for name,a,b in [('left',lo,mid),('right',mid,hi)]:
        plo=phase(a); phi=phase(b); blo,bhi=box(plo,phi)
        rows.append({'cell':name,'lo':str(a),'hi':str(b),'phase_lo':str(plo),'phase_hi':str(phi),'exp_lo_positive':blo>0,'exp_hi_positive':bhi>0,'ordered':blo<=bhi,'width_float':float(bhi-blo),'exp_lo_digits':len(str(blo.numerator)),'exp_hi_digits':len(str(bhi.numerator))})
    checks={'two_cells':len(rows)==2,'positive':all(r['exp_lo_positive'] and r['exp_hi_positive'] for r in rows),'ordered':all(r['ordered'] for r in rows),'shared_midpoint':mid==((lo+hi)/2)}
    out={'record':2741,'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'cells':rows,'method':'exact Fraction evaluation of order-20 Taylor plus rational tail; diagnostic endpoint replay only','nonclaims':['No derivative-jet outward replay','No finite integral','No D4/D7','No pins or RH']}
    (ROOT/'results/2741_rational_endpoint_replay.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)); return 0 if all(checks.values()) else 1
if __name__=='__main__': raise SystemExit(main())


