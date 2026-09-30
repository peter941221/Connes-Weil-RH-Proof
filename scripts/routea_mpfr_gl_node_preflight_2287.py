"""2287: MPFR-directed finite-panel GL node preflight.

Builds on 2286 atom intervals. It certifies the arithmetic enclosure of a
finite Gauss-Legendre node sum, while deliberately leaving the quadrature
remainder open.
"""
import json, math, sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import routea_mpfr_owner_atom_preflight_2286 as atom
OUT=ROOT/'results/2287_mpfr_gl_node_preflight.json'

def iadd(x,y): return (x[0]+y[0],x[1]+y[1])
def iscale(x,c):
    if c>=0: return (x[0]*c,x[1]*c)
    return (x[1]*c,x[0]*c)
def integrate(xi,families,coefficients,panels,order):
    nodes,weights=np.polynomial.legendre.leggauss(order); half=max(w*w for w,_ in families); total_re=(0.,0.); total_im=(0.,0.)
    for panel in range(panels):
        left=-half+2*half*panel/panels; right=-half+2*half*(panel+1)/panels; centre=(left+right)/2; scale=(right-left)/2
        for node,weight in zip(nodes,weights):
            y=centre+scale*node; re,im=atom.atom(y,xi,families,coefficients)
            total_re=iadd(total_re,iscale(re,scale*weight)); total_im=iadd(total_im,iscale(im,scale*weight))
    return {'real':total_re,'imag':total_im,'radius':max(total_re[1]-total_re[0],total_im[1]-total_im[0]),'mid_abs':math.hypot((total_re[0]+total_re[1])/2,(total_im[0]+total_im[1])/2)}

def main():
    capture=json.loads(atom.CAPTURE.read_text()); owner=capture['owner_capture']; families=[(float.fromhex(a),float.fromhex(b)) for a,b in owner['families_hex']]; base=[complex(float.fromhex(a),float.fromhex(b)) for a,b in owner['base_hex']]; corr=[complex(float.fromhex(a),float.fromhex(b)) for a,b in owner['corr_hex']]
    rows=[]
    for xi in (40.,120.,200.):
        for panels,order in ((8,8),(8,16),(16,8),(16,16)):
            rows.append({'xi':xi,'panels':panels,'order':order,'base':integrate(xi,families,base,panels,order),'corr':integrate(xi,families,corr,panels,order)})
    result={'record':2287,'status':'MPFR-DIRECTED-GL-NODE-PREFLIGHT','certificate':False,'hgap_closed':False,'backend':{'library':'libmpfr.so.6','precision_bits':atom.PREC,'rounding':'RNDD/RNDU'},'owner':{'families':len(families),'support_half_width':max(w*w for w,_ in families),'prime_power_count':41136},'rows':rows,'nonclaims':['Gauss-Legendre quadrature remainder is not enclosed','finite xi window only','no hgap supplier, producer GO or RH claim']}
    result['max_base_radius']=max(r['base']['radius'] for r in rows); result['max_corr_radius']=max(r['corr']['radius'] for r in rows)
    movements=[]
    for xi in (40.,120.,200.):
        group=[r for r in rows if r['xi']==xi]
        reference=next(r for r in group if r['panels']==8 and r['order']==8)
        for row in group:
            if row is reference: continue
            movements.append({'xi':xi,'from':'8:8','to':f"{row['panels']}:{row['order']}", 'base_mid_relative_change':abs(row['base']['mid_abs']-reference['base']['mid_abs'])/max(row['base']['mid_abs'],1e-300), 'corr_mid_relative_change':abs(row['corr']['mid_abs']-reference['corr']['mid_abs'])/max(row['corr']['mid_abs'],1e-300)})
    result['node_rule_movement']=movements
    result['max_base_mid_relative_change']=max(x['base_mid_relative_change'] for x in movements)
    result['max_corr_mid_relative_change']=max(x['corr_mid_relative_change'] for x in movements)
    result['status_note']='NODE-ARITHMETIC-ONLY'
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'max_base_radius':result['max_base_radius'],'max_corr_radius':result['max_corr_radius']}))
if __name__=='__main__': main()


