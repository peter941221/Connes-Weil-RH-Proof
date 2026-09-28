#!/usr/bin/env python3
"""Record 2144: add known owner zeros as exact correction constraints."""
from __future__ import annotations
import json, math, os, sys
from pathlib import Path
import mpmath as mp
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fourpoint_actual_owner_1980 as owner  # noqa: E402
import fourpoint_owner_completion_1980 as completion  # noqa: E402
import fourpoint_owner_density_1959 as density  # noqa: E402
import routea_health_cone_2006 as health  # noqa: E402
OUTPUT = ROOT / "results" / "2144_routea_knownzero_constraint_screen.json"
RHO = complex(0.945, 39.25244858548658); K = 30.0; N = 0
FACTORS = [0.50, 0.70, 0.90, 1.10, 1.30]; SEED = 2144

def known_zeros(radius):
    out=[]; mp.mp.dps=60
    for i in range(1,101):
        z=mp.zetazero(i)
        if float(mp.im(z))-RHO.imag > radius+1: break
        p=complex(float(mp.re(z)),float(mp.im(z)))
        if abs(p-RHO)<=radius+1e-10 and not any(abs(p-q)<1e-10 for q in out): out.append(p)
    return out

def solve_h1(matrix, gram, values):
    ev, Q=np.linalg.eigh((gram+gram.conj().T)/2)
    floor=max(float(ev.max())*1e-12,1e-24)
    inv=(Q/np.maximum(ev,floor))@Q.conj().T
    schur=matrix@inv@matrix.conj().T
    return inv@matrix.conj().T@np.linalg.solve(schur,values)

def main():
    targets=density.target_nodes(RHO); target_values=np.asarray([density.target_value(RHO,z) for z in targets],complex)
    zeros=known_zeros(owner.formal_radius(RHO,N))
    nodes=targets+zeros; values=np.concatenate([target_values,np.zeros(len(zeros),complex)])
    basefam=density.design_family(RHO,1.0); fam=[(f*a,t) for f in FACTORS for a,t in basefam]
    xw=[density.phi_weights(a,panels=6,m=400) for a,_ in fam]
    M=density.family_values(fam,K,np.asarray(nodes,complex),xw).T; Mt=density.family_values(fam,K,np.asarray(targets,complex),xw).T
    G=health.h1_gram(fam)
    base=solve_h1(Mt,G,np.ones(len(targets),complex)); corr=solve_h1(M,G,values)
    xi=np.linspace(-40,40,4001); V=density.family_values(fam,K,0.5-2j*np.pi*xi,xw)
    sig=density.rig.sigma_vec(2*np.pi*xi); pset=density.rig.prime_powers_up_to(math.exp(max(a for a,_ in fam)*(N+2)))
    kernel=sig.copy()
    for n,w in pset: kernel += 2*w/math.sqrt(n)*np.cos(2*np.pi*xi*math.log(n))
    P=np.real(density.P_from_nodes(xi,completion.counterpart_nodes(RHO)))
    def read(b,c):
        lb=b@V; lc=c@V; W=np.abs(lb)**2*np.abs(lc)**2
        vals=[float(np.trapezoid(kernel*q*W,xi)) for q in (np.ones_like(P),P,P*P)]
        C,B,D=vals; det=C*D-B*B
        return {"C":C,"B01":B,"D":D,"det":det,"healthy":bool(C>0 and D<0 and det<0),"residual_known":float(sum(abs((b@density.family_values(fam,K,np.asarray([z],complex),xw)[:,0])*(c@density.family_values(fam,K,np.asarray([z],complex),xw)[:,0])) for z in zeros))}
    singular=np.linalg.svd(M,compute_uv=False)
    result={"record":2144,"status":"KNOWNZERO-CONSTRAINT-SCREEN","rho":[RHO.real,RHO.imag],"known_zero_count":len(zeros),"profile_count":len(fam),"constraint_count":len(nodes),"constraint_residual_base":float(np.max(np.abs(Mt@base-1))),"constraint_residual_corr":float(np.max(np.abs(M@corr-values))),"singular_values": [float(x) for x in singular],"gate":read(base,corr),"nonclaims":["known zeros are not complete formal owner","4001-point direct grid is not an integral certificate","no producer theorem or RH claim"],"provenance":{"script":os.fspath(Path(__file__).relative_to(ROOT))}}
    OUTPUT.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8"); print(json.dumps(result,indent=2))
if __name__ == "__main__": main()
