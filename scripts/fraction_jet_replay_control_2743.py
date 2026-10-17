#!/usr/bin/env python3
from fractions import Fraction as F
import json
from math import comb
import mpmath as mp
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class I:
 def __init__(self,l,h=None): self.l=F(l); self.h=self.l if h is None else F(h)
 def add(self,o): return I(self.l+o.l,self.h+o.h)
 def sub(self,o): return I(self.l-o.h,self.h-o.l)
 def mul(self,o):
  v=[self.l*o.l,self.l*o.h,self.h*o.l,self.h*o.h]; return I(min(v),max(v))
 def scale(self,c): return self.mul(I(c))
 def inv(self): assert self.l>0; return I(1/self.h,1/self.l)
 def ok(self): return self.l<=self.h

def taylor(y):
 s=F(0); f=1
 for i in range(20):
  if i:f*=i
  s+=y**i/f
 return s
def tail(y):
 f=1
 for i in range(1,21):f*=i
 return y**20*F(21,20*f)
def phase(x):return 1/(1-x)-1/x
def run(a,b,N=7,m=4):
 # coordinate jets and reflected coordinate jets
 u=[I(a,b)]+[I(1)]+[I(0) for _ in range(N-1)]
 v=[I(1-b,1-a)]+[I(-1)]+[I(0) for _ in range(N-1)]
 def rec(X):
  R=[X[0].inv()]
  for n in range(1,N+1):
   s=I(0)
   for j in range(n): s=s.add(X[j+1].scale(comb(n,j+1)).mul(R[n-1-j]))
   R.append(s.scale(-1).mul(R[0]))
  return R
 # recurrence above uses n choose j+1 and R[n-1-j]
 ru,rv=rec(u),rec(v); p=[rv[i].sub(ru[i]) for i in range(N+1)]
 e0=I(1/(taylor(-p[0].l/m)+tail(-p[0].l/m))**m,1/(taylor(-p[0].h/m)-tail(-p[0].h/m))**m)
 e=[e0]
 for n in range(1,N+1):
  s=I(0)
  for j in range(n): s=s.add(p[j+1].scale(comb(n-1,j)).mul(e[n-1-j]))
  e.append(s)
 d=[I(1).add(e[0])]+e[1:]
 rd=rec(d); q=[x for x in rd]
 out=[]
 for n in range(N+1):
  s=I(0)
  for j in range(n+1): s=s.add(e[j].scale(comb(n,j)).mul(q[n-j]))
  out.append(s)
 return out

def lift(q):
 return mp.mpf(q.numerator)/q.denominator

def main():
 mp.mp.dps=100
 lo=F(2049,8192); hi=F(8394751,33554432); mid=(lo+hi)/2; rows=[]
 for name,a,b in [('left',lo,mid),('right',mid,hi)]:
  z=run(a,b)
  f=lambda x: 1/(1+mp.exp(-(1/(1-x)-1/x)))
  samples=[a,(a+b)/2,b]
  contained=all(lift(z[n].l)<=mp.diff(f,lift(x),n)<=lift(z[n].h) for x in samples for n in range(8))
  rows.append({'cell':name,'independent_derivative_checks':24,'sampled_derivatives_contained':contained,'orders':len(z),'ordered':all(x.ok() for x in z),'widths':[float(x.h-x.l) for x in z],'finite':all(abs(x.l)<10**100000 and abs(x.h)<10**100000 for x in z)})
 checks={'independent_samples_contained':all(r['sampled_derivatives_contained'] for r in rows),'two_cells':len(rows)==2,'all_ordered':all(r['ordered'] for r in rows),'all_finite':all(r['finite'] for r in rows),'orders_0_to_7':all(r['orders']==8 for r in rows)}
 out={'record':2743,'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'cells':rows,'supersedes':'Original 2743 PASS withdrawn: collapsed coordinate cells, reversed phase endpoints, wrong exponential recurrence coefficients.', 'method':'independent Fraction interval recurrence through order 7','nonclaims':['Not a Lean theorem','Not an outward floating-point certificate','No finite integral, D4/D7, pins or RH claim']}
 (ROOT/'results/2743_fraction_jet_replay_control.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2)); return 0 if all(checks.values()) else 1
if __name__=='__main__':raise SystemExit(main())
