import json, math, os, sys, time
import numpy as np
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_health_cone_2006 as r06
import routea_opposite_gates_height_1994 as r94
DELTA, GAMMA, SCALE, K, N = 0.10, r94.G8, 0.88, 30.0, 0

def setup():
    rho = (0.5 + DELTA) + 1j * GAMMA
    nodes, values = r94.owner_nodes_ext(rho, GAMMA)
    fam, base_fam = r06.two_copy_family(nodes, SCALE, GAMMA)
    xw = r80.family_quad(fam, K)
    gram = r06.h1_gram(fam)
    interpolation = r80.family_values(fam, K, np.asarray(nodes, complex), xw).T
    base_ref, _corr_ref, _amp = r80.amplitudes(nodes, values, base_fam, K, r80.family_quad(base_fam, K))
    return rho, nodes, values, fam, xw, gram, interpolation, r06.embedded_reference(base_ref)

def nullspace(a):
    _u, sv, vh = np.linalg.svd(a, full_matrices=True)
    rank = int(np.sum(sv > 1e-10 * sv[0]))
    return vh[rank:].conj().T, rank, sv

def min_h1(g, a, y):
    ew, ev = np.linalg.eigh(g)
    floor = max(float(ew.max()) * 1e-12, 1e-18)
    inv = (ev / np.maximum(ew, floor)) @ ev.conj().T
    schur = a @ inv @ a.conj().T
    c = inv @ a.conj().T @ np.linalg.solve(schur, y)
    return c, {"constraint_residual": float(np.max(np.abs(a @ c - y))), "h1_energy": float(np.real(c.conj() @ g @ c)), "gram_condition_raw": float(ew.max() / max(abs(ew).min(), 1.0e-300)), "gram_condition_effective": float(ew.max() / floor), "gram_min_eigenvalue": float(ew.min()), "gram_max_eigenvalue": float(ew.max())}

def q_matrix(xi, fam, xw, base, rho):
    s = 0.5 - 2j*np.pi*xi
    v = r80.family_values(fam, K, s, xw)
    lb = base @ v
    p = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
    support = max(a for a,_ in fam) * (N+2)
    primes = r59.rig.prime_powers_up_to(math.exp(support))
    kernel = r59.rig.sigma_vec(2*np.pi*xi)
    for number, weight in primes:
        kernel += 2*weight/math.sqrt(number)*np.cos(2*np.pi*xi*math.log(number))
    dxi = float(xi[1]-xi[0])
    w = kernel * p*p * np.abs(lb)**(2*(N+1))
    m = (v.conj()*w*dxi) @ v.T
    return (m+m.conj().T)/2, {"support_radius":float(support),"prime_power_count":len(primes),"base_max":float(np.max(np.abs(lb))),"dxi":dxi}

def run(dxi, data):
    rho, nodes, values, fam, xw, gram, a, base = data
    xi = np.linspace(-40,40,int(round(80/dxi))+1)
    corr, hi = min_h1(gram,a,np.asarray(values,complex))
    null, rank, sv = nullspace(a)
    m, qi = q_matrix(xi,fam,xw,base,rho)
    qh = float(np.real(corr.conj()@m@corr))
    pn = null.conj().T@m@null; pn=(pn+pn.conj().T)/2
    ew=np.linalg.eigvalsh(pn)
    status="INDEFINITE_FIBRE" if ew.min() < -max(np.max(np.abs(ew))*1e-12,1e-18) else "COERCIVE_NUMERIC_MIN"
    return {"dxi":dxi,"h1":hi,"rank":rank,"nullity":int(null.shape[1]),"min_singular":float(sv.min()),"q_h1":qh,"projected_q_min":float(ew.min()),"projected_q_max":float(ew.max()),"affine_status":status,"q_data":qi}

data=setup(); rows=[run(d,data) for d in (0.008,0.004)]
q0,q1=[r["q_h1"] for r in rows]; spread=abs(q0-q1)/max(abs(q1),1.0)
verdict="A-SMALLER-NUMERIC-CANDIDATE" if q0<0 and q1<0 and spread<=1e-2 else "A-DEAD-G8H-PROBE"
out={"record":2036,"status":verdict,"owner":"G8-H","rho":[0.6,GAMMA],"scale":SCALE,"target":"actual grouped ICgate(g.square) quadratic form","rows":rows,"q_h1_relative_spread":float(spread),"interval_certificate":False,"nonclaims":["not interval-certified","not complete-owner","not uniform","not RH"]}
path=os.path.join(ROOT,"results","2036_route_a_g8h_grouped_residual_probe.json")
with open(path,"w",encoding="utf-8") as f: json.dump(out,f,indent=2); f.write("\n")
print(json.dumps(out,indent=2))
print("RESULT",path)