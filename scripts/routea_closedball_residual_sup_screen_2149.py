#!/usr/bin/env python3
"""Record 2149: closed-ball residual sup screen for trial 162."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'scripts'))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
OUTPUT=ROOT/'results'/'2149_routea_closedball_residual_sup_screen.json'; RHO=complex(.945,39.25244858548658); K=30.; N=0; FACTORS=[.5,.7,.9,1.1,1.3]; SEED=2149; TRIAL=162; SB=-2.7660862136111555; SC=-7.593725512173001

def solve(M,G,y):
 ev,Q=np.linalg.eigh((G+G.conj().T)/2); floor=max(float(ev.max())*1e-12,1e-24); inv=(Q/np.maximum(ev,floor))@Q.conj().T
 return inv@M.conj().T@np.linalg.solve(M@inv@M.conj().T,y)
def main():
 targets=density.target_nodes(RHO); tv=np.asarray([density.target_value(RHO,z) for z in targets],complex); fam0=density.design_family(RHO,1.); fam=[(f*a,t) for f in FACTORS for a,t in fam0]; xw=[density.phi_weights(a,6,400) for a,_ in fam]; M=density.family_values(fam,K,np.asarray(targets,complex),xw).T; G=__import__('routea_health_cone_2006',fromlist=['h1_gram']).h1_gram(fam); base0=solve(M,G,np.ones(8,complex)); corr0=solve(M,G,tv); _u,sv,vh=np.linalg.svd(M); rank=int(np.sum(sv>1e-10*sv[0])); null=vh[rank:].conj().T; rng=np.random.default_rng(2141); dirs=[]
 for _ in range(24):
  raw=null@(rng.normal(size=null.shape[1])+1j*rng.normal(size=null.shape[1])); dirs.append(raw/math.sqrt(max(float(np.real(raw.conj()@G@raw)),1e-300)))
 base=base0+SB*dirs[TRIAL%24]; corr=corr0+SC*dirs[(7*TRIAL+3)%24]
 R=owner.formal_radius(RHO,N); rng=np.random.default_rng(SEED); u=rng.random(20000); ang=rng.random(20000)*2*np.pi; rad=R*np.sqrt(u); z=RHO+rad*np.exp(1j*ang); vals=density.family_values(fam,K,z,xw); counterpart=1-np.conj(z); vals2=density.family_values(fam,K,counterpart,xw); f=(base@vals)*(corr@vals); f2=(base@vals2)*(corr@vals2); prod=np.abs(np.conj(f2)*f); order=np.argsort(prod)[-20:][::-1]
 result={'record':2149,'status':'CLOSEDBALL-RESIDUAL-SUP-SCREEN','radius':R,'sample_count':len(z),'max_product':float(prod[order[0]]),'p99_product':float(np.quantile(prod,.99)),'p999_product':float(np.quantile(prod,.999)),'mean_product':float(np.mean(prod)),'max_radius_location':[float(z[order[0]].real),float(z[order[0]].imag)],'top_products':[float(prod[i]) for i in order[:20]],'anchor_model':1.0,'nonclaims':['random samples are not a supremum or interval bound','formal owner cardinality and complete zero set remain open','no producer theorem or RH claim'],'provenance':{'script':os.fspath(Path(__file__).relative_to(ROOT))}}
 OUTPUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
