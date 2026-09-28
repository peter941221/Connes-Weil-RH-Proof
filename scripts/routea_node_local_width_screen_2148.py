#!/usr/bin/env python3
"""Record 2148: randomized node-local width basis under known-zero pins."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'scripts'))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402
OUTPUT=ROOT/'results'/'2148_routea_node_local_width_screen.json'; RHO=complex(.945,39.25244858548658); K=30.; N=0

def zeros(radius):
 out=[]; mp.mp.dps=50
 for i in range(1,101):
  z=mp.zetazero(i)
  if float(mp.im(z))-RHO.imag>radius+1: break
  p=complex(float(mp.re(z)),float(mp.im(z)))
  if abs(p-RHO)<=radius+1e-10 and not any(abs(p-q)<1e-10 for q in out): out.append(p)
 return out
def solve(M,G,y):
 ev,Q=np.linalg.eigh((G+G.conj().T)/2); floor=max(float(ev.max())*1e-12,1e-24); inv=(Q/np.maximum(ev,floor))@Q.conj().T
 return inv@M.conj().T@np.linalg.solve(M@inv@M.conj().T,y)
def main():
 targets=density.target_nodes(RHO); tv=np.asarray([density.target_value(RHO,z) for z in targets],complex); zs=zeros(owner.formal_radius(RHO,N)); nodes=targets+zs; vals=np.concatenate([tv,np.zeros(len(zs),complex)]); basefam=density.design_family(RHO,1.); rng=np.random.default_rng(2148); result={'record':2148,'status':'NODE-LOCAL-WIDTH-SCREEN','known_zero_count':len(zs),'schemes':{},'nonclaims':['known zeros are not complete formal owner','direct grid is not an integral certificate','no producer theorem or RH claim']}
 for trial in range(12):
  block=np.array([.50,.70,.90,1.10,1.30])[...,None]; local=np.exp(rng.normal(0,.12,size=(5,len(basefam)))); factors=np.clip(block*local,.35,1.6); fam=[(float(factors[k,j]*a),t) for k in range(5) for j,(a,t) in enumerate(basefam)]; xw=[density.phi_weights(a,6,240) for a,_ in fam]; M=density.family_values(fam,K,np.asarray(nodes,complex),xw).T; Mt=density.family_values(fam,K,np.asarray(targets,complex),xw).T; G=health.h1_gram(fam); base=solve(Mt,G,np.ones(len(targets),complex)); corr=solve(M,G,vals); sv=np.linalg.svd(M,compute_uv=False); xi=np.linspace(-40,40,4001); V=density.family_values(fam,K,.5-2j*np.pi*xi,xw); W=np.abs(base@V)**2*np.abs(corr@V)**2; P=np.real(density.P_from_nodes(xi,completion.counterpart_nodes(RHO))); sig=density.rig.sigma_vec(2*np.pi*xi); ker=sig.copy()
  for n,w in density.rig.prime_power_up_to(math.exp(max(a for a,_ in fam)*2)) if hasattr(density.rig,'prime_power_up_to') else density.rig.prime_powers_up_to(math.exp(max(a for a,_ in fam)*2)): ker += 2*w/math.sqrt(n)*np.cos(2*np.pi*xi*math.log(n))
  C,B,D=[float(np.trapezoid(ker*q*W,xi)) for q in (np.ones_like(P),P,P*P)]; det=C*D-B*B; result['schemes'][str(trial)]={'min_singular':float(sv[-1]),'condition':float(sv[0]/max(sv[-1],1e-300)),'constraint_residual_base':float(np.max(np.abs(Mt@base-1))),'constraint_residual_corr':float(np.max(np.abs(M@corr-vals))),'C':C,'B01':B,'D':D,'det':det,'healthy':bool(C>0 and D<0 and det<0),'factor_min':float(factors.min()),'factor_max':float(factors.max())}
 OUTPUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
