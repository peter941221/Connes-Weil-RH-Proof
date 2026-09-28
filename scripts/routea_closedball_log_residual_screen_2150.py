#!/usr/bin/env python3
"""Record 2150: log-scaled closed-ball residual screen."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'scripts'))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402
OUTPUT=ROOT/'results'/'2150_routea_closedball_log_residual_screen.json'; RHO=complex(.945,39.25244858548658); K=30.; FACTORS=[.5,.7,.9,1.1,1.3]; TRIAL=162; SB=-2.7660862136111555; SC=-7.593725512173001

def solve(M,G,y):
 ev,Q=np.linalg.eigh((G+G.conj().T)/2); floor=max(float(ev.max())*1e-12,1e-24); inv=(Q/np.maximum(ev,floor))@Q.conj().T; return inv@M.conj().T@np.linalg.solve(M@inv@M.conj().T,y)
def coeffs():
 targets=density.target_nodes(RHO); tv=np.asarray([density.target_value(RHO,z) for z in targets],complex); fam0=density.design_family(RHO,1.); fam=[(f*a,t) for f in FACTORS for a,t in fam0]; xw=[density.phi_weights(a,6,400) for a,_ in fam]; M=density.family_values(fam,30,np.asarray(targets,complex),xw).T; G=health.h1_gram(fam); b0=solve(M,G,np.ones(8,complex)); c0=solve(M,G,tv); _u,sv,vh=np.linalg.svd(M); rank=int(np.sum(sv>1e-10*sv[0])); null=vh[rank:].conj().T; rng=np.random.default_rng(2141); ds=[]
 for _ in range(24):
  raw=null@(rng.normal(size=null.shape[1])+1j*rng.normal(size=null.shape[1])); ds.append(raw/math.sqrt(max(float(np.real(raw.conj()@G@raw)),1e-300)))
 return fam,xw,b0+SB*ds[TRIAL%24],c0+SC*ds[(7*TRIAL+3)%24]
def scaled_log_value(fam,xw,coeff,z):
 logs=[]; scaled=[]
 for (a,t),(X,W) in zip(fam,xw):
  s=a*(z+1j*t); realpart=float(np.real(s)*np.max(X)) if np.real(s)>=0 else float(np.real(s)*np.min(X)); logs.append(realpart)
  phase=np.exp(1j*np.imag(s)*X); u=X/a; phi=np.zeros_like(X); inside=np.abs(u)<1; phi[inside]=np.exp(-30/(1-u[inside]**2)); raw=np.sum(W*phi*np.exp(np.real(s)*X-realpart)*phase)*a; scaled.append(raw)
 m=max(logs); total=np.sum(coeff*np.asarray(scaled)*np.exp(np.asarray(logs)-m)); return m+math.log(max(abs(total),1e-300))
def main():
 fam,xw,b,c=coeffs(); R=owner.formal_radius(RHO,0); rng=np.random.default_rng(2150); u=rng.random(5000); ang=rng.random(5000)*2*np.pi; rad=R*np.sqrt(u); z=RHO+rad*np.exp(1j*ang); logs=[]
 for p in z:
  logs.append(scaled_log_value(fam,xw,b,p)+scaled_log_value(fam,xw,c,p)+scaled_log_value(fam,xw,b,1-np.conj(p))+scaled_log_value(fam,xw,c,1-np.conj(p)))
 logs=np.asarray(logs); finite=np.isfinite(logs); result={'record':2150,'status':'CLOSEDBALL-LOG-RESIDUAL-SCREEN','radius':R,'sample_count':len(z),'finite_count':int(finite.sum()),'max_log_product':float(np.max(logs[finite])),'max_product_log10':float(np.max(logs[finite])/math.log(10)),'p99_log_product':float(np.quantile(logs[finite],.99)),'mean_log_product':float(np.mean(logs[finite])),'max_location':[float(z[np.argmax(logs)].real),float(z[np.argmax(logs)].imag)],'anchor_model':1.0,'nonclaims':['random samples are not a supremum or interval bound','formal owner cardinality and complete zero set remain open','no producer theorem or RH claim'],'provenance':{'script':os.fspath(Path(__file__).relative_to(ROOT))}}
 OUTPUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
