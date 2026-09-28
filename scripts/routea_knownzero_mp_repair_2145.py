#!/usr/bin/env python3
"""Record 2145: high-precision correction of the known-zero constrained owner."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'scripts'))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
import fourpoint_cert_d_1985 as cert  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402
OUTPUT=ROOT/'results'/'2145_routea_knownzero_mp_repair.json'; RHO=complex(.945,39.25244858548658); K=30.; N=0; FACTORS=[.5,.7,.9,1.1,1.3]; MP_M=320

def zeros(radius):
 out=[]; mp.mp.dps=60
 for i in range(1,101):
  z=mp.zetazero(i)
  if float(mp.im(z))-RHO.imag>radius+1: break
  p=complex(float(mp.re(z)),float(mp.im(z)))
  if abs(p-RHO)<=radius+1e-10 and not any(abs(p-q)<1e-10 for q in out): out.append(p)
 return out

def solve(M,G,y):
 ev,Q=np.linalg.eigh((G+G.conj().T)/2); floor=max(float(ev.max())*1e-12,1e-24); inv=(Q/np.maximum(ev,floor))@Q.conj().T
 return inv@M.conj().T@np.linalg.solve(M@inv@M.conj().T,y)
def mp_vals(fam,s):
 out=[]
 for a,t in fam:
  aa=mp.mpf(str(a)); tt=mp.mpf(str(t)); ss=mp.mpc(s); X,W=cert.phi_weights_mp(aa,6,MP_M); total=mp.mpc(0)
  for x,w in zip(X,W):
   u=x/aa
   if abs(u)<1: total += aa*w*mp.exp(-K/(1-u*u)+aa*(ss+1j*tt)*x)
  out.append(total)
 return out
def read(fam,xw,b,c,points=4001):
 xi=np.linspace(-40,40,points); V=density.family_values(fam,K,.5-2j*np.pi*xi,xw); lb=b@V; lc=c@V; W=np.abs(lb)**2*np.abs(lc)**2; P=np.real(density.P_from_nodes(xi,completion.counterpart_nodes(RHO))); sig=density.rig.sigma_vec(2*np.pi*xi); ker=sig.copy()
 for n,w in density.rig.prime_powers_up_to(math.exp(max(a for a,_ in fam)*2)): ker += 2*w/math.sqrt(n)*np.cos(2*np.pi*xi*math.log(n))
 C,B,D=[float(np.trapezoid(ker*q*W,xi)) for q in (np.ones_like(P),P,P*P)]; det=C*D-B*B
 return {'xi_points':points,'C':C,'B01':B,'D':D,'det':det,'healthy':bool(C>0 and D<0 and det<0)}
def main():
 mp.mp.dps=80; targets=density.target_nodes(RHO); tv=np.asarray([density.target_value(RHO,z) for z in targets],complex); zs=zeros(owner.formal_radius(RHO,N)); nodes=targets+zs; vals=np.concatenate([tv,np.zeros(len(zs),complex)]); bf=density.design_family(RHO,1.); fam=[(f*a,t) for f in FACTORS for a,t in bf]; xw=[density.phi_weights(a,6,400) for a,_ in fam]; Mt=density.family_values(fam,K,np.asarray(targets,complex),xw).T; M=density.family_values(fam,K,np.asarray(nodes,complex),xw).T; G=health.h1_gram(fam); base=solve(Mt,G,np.ones(len(targets),complex)); corr=solve(M,G,vals)
 H=np.asarray([[complex(v.real,v.imag) for v in mp_vals(fam,mp.mpc(float(z.real),float(z.imag)))] for z in nodes],complex); sv=np.linalg.svd(H,compute_uv=False); target=vals; before=H@corr; delta=np.linalg.lstsq(H,target-before,rcond=None)[0]; repaired=corr+delta; after=H@repaired
 result={'record':2145,'status':'KNOWNZERO-MP-REPAIR','known_zero_count':len(zs),'constraint_count':len(nodes),'mp_quadrature_points_per_panel':MP_M,'high_matrix_singular_values':[float(x) for x in sv], 'correction':{'before_max':float(np.max(np.abs(before-target))),'l2':float(np.linalg.norm(delta)),'max':float(np.max(np.abs(delta))),'after_max':float(np.max(np.abs(after-target)))},'gate_before':read(fam,xw,base,corr),'gate_after':read(fam,xw,base,repaired),'nonclaims':['known zeros are not the complete formal owner','high matrix is quadrature-based, not interval enclosed','no producer theorem or RH claim'],'provenance':{'script':os.fspath(Path(__file__).relative_to(ROOT))}}
 OUTPUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()

