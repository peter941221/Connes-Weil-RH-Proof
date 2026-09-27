import json, math, os, sys
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT,"scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
GAMMA,SCALE,K,N,DELTA = r94.G8,0.88,30.0,0,0.10

def setup(two_copy):
    rho=(0.5+DELTA)+1j*GAMMA
    nodes,values=r94.owner_nodes_ext(rho,GAMMA)
    full,base_fam=r06.two_copy_family(nodes,SCALE,GAMMA)
    fam=full if two_copy else base_fam
    xw=r80.family_quad(fam,K)
    gram=r06.h1_gram(fam)
    a=r80.family_values(fam,K,np.asarray(nodes,complex),xw).T
    base_ref=None; corr_ref=None
    return rho,nodes,values,fam,xw,gram,a,base_ref,corr_ref

def min_h1(g,a,y):
    ew,ev=np.linalg.eigh(g); floor=max(float(ew.max())*1e-12,1e-18)
    inv=(ev/np.maximum(ew,floor))@ev.conj().T
    schur=a@inv@a.conj().T
    c=inv@a.conj().T@np.linalg.solve(schur,y)
    return c,{"resid":float(np.max(np.abs(a@c-y))),"cond_raw":float(ew.max()/max(abs(ew).min(),1e-300)),"min_eig":float(ew.min()),"max_eig":float(ew.max())}

def qmat(xi,fam,xw,base,rho):
    s=.5-2j*np.pi*xi; v=r80.family_values(fam,K,s,xw); lb=base@v
    p=np.real(r59.P_from_nodes(xi,r80.counterpart_nodes(rho)))
    support=max(a for a,_ in fam)*(N+2); ps=r59.rig.prime_powers_up_to(math.exp(support))
    ker=r59.rig.sigma_vec(2*np.pi*xi)
    for num,w in ps: ker += 2*w/math.sqrt(num)*np.cos(2*np.pi*xi*math.log(num))
    dxi=float(xi[1]-xi[0]); weight=ker*p*p*np.abs(lb)**(2*(N+1))
    m=(v.conj()*weight*dxi)@v.T; return (m+m.conj().T)/2, support,len(ps)

def run(two_copy,dxi):
    rho,nodes,values,fam,xw,g,a,base_ref,corr_ref=setup(two_copy)
    base,_=min_h1(g,a,np.ones(len(nodes),complex)); corr,hi=min_h1(g,a,np.asarray(values,complex))
    xi=np.linspace(-40,40,int(round(80/dxi))+1); m,support,npow=qmat(xi,fam,xw,base,rho)
    q=float(np.real(corr.conj()@m@corr))
    _u,sv,vh=np.linalg.svd(a,full_matrices=True); rank=int(np.sum(sv>1e-10*sv[0])); null=vh[rank:].conj().T
    if null.shape[1]:
        pn=null.conj().T@m@null; pn=(pn+pn.conj().T)/2; ew=np.linalg.eigvalsh(pn); emin=float(ew.min()); emax=float(ew.max()); stat="INDEFINITE" if emin<0 else "PSD"
    else: emin=emax=None; stat="NO_NULLSPACE"
    return {"basis":"two-copy" if two_copy else "one-copy","dxi":dxi,"basis_size":len(fam),"rank":rank,"nullity":int(null.shape[1]),"q_h1":q,"constraint_resid":hi["resid"],"gram_condition_raw":hi["cond_raw"],"projected_q_min":emin,"projected_q_max":emax,"fibre_status":stat,"support":support,"prime_power_count":npow}

rows=[run(two,dxi) for two in (False,True) for dxi in (0.008,0.004)]
for row in rows: print(json.dumps(row))
out={"record":2037,"status":"BASIS_COMPARISON","rows":rows,"nonclaims":["not interval certified","not complete owner","not uniform","not RH"]}
path=os.path.join(ROOT,"results","2037_route_a_g8h_basis_comparison.json")
with open(path,"w",encoding="utf-8",newline="\n") as f: json.dump(out,f,indent=2); f.write("\n")
print("RESULT",path)