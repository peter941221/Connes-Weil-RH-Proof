"""2286: MPFR-directed corrected-owner atom preflight.

This certifies interval propagation for individual complex owner atoms at fixed
(xi,y) points. It intentionally does not certify quadrature or the infinite
xi tail.
"""
import ctypes as C
import json, math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
CAPTURE=ROOT/'results/2275_gap_owner_audit.json'
OUT=ROOT/'results/2286_mpfr_owner_atom_preflight.json'
PREC=256; RNDD=3; RNDU=2
class M(C.Structure):
    _fields_=[('prec',C.c_long),('sign',C.c_int),('exp',C.c_long),('digits',C.POINTER(C.c_ulong))]
P=C.POINTER(M); lib=C.CDLL('libmpfr.so.6')
lib.mpfr_init2.argtypes=[P,C.c_long]; lib.mpfr_clear.argtypes=[P]; lib.mpfr_set_d.argtypes=[P,C.c_double,C.c_int]
for name in ('mpfr_add','mpfr_sub','mpfr_mul','mpfr_div'):
    getattr(lib,name).argtypes=[P,P,P,C.c_int]
for name in ('mpfr_exp','mpfr_sin','mpfr_cos'):
    getattr(lib,name).argtypes=[P,P,C.c_int]
lib.mpfr_get_d.argtypes=[P,C.c_int]; lib.mpfr_get_d.restype=C.c_double

def point_unary(name,value):
    lo=M(); hi=M(); src=M()
    for z in (lo,hi,src): lib.mpfr_init2(C.byref(z),PREC)
    lib.mpfr_set_d(C.byref(src),C.c_double(value),0); fn=getattr(lib,name)
    fn(C.byref(lo),C.byref(src),RNDD); low=lib.mpfr_get_d(C.byref(lo),RNDD)
    fn(C.byref(hi),C.byref(src),RNDU); high=lib.mpfr_get_d(C.byref(hi),RNDU)
    for z in (lo,hi,src): lib.mpfr_clear(C.byref(z))
    return (low,high)

def unary(name,x):
    if name in ("mpfr_sin","mpfr_cos"):
        if x[1]-x[0] >= 2*math.pi: return (-1.0,1.0)
        candidates=[x[0],x[1]]
        if name=='mpfr_sin':
            for base in (math.pi/2,-math.pi/2):
                k=math.ceil((x[0]-base)/(2*math.pi))
                point=base+2*math.pi*k
                if x[0] <= point <= x[1]: candidates.append(point)
        else:
            for base in (0.0,math.pi):
                k=math.ceil((x[0]-base)/(2*math.pi))
                point=base+2*math.pi*k
                if x[0] <= point <= x[1]: candidates.append(point)
        values=[point_unary(name,point) for point in candidates]
        return (min(v[0] for v in values),max(v[1] for v in values))
    return (point_unary(name,x[0])[0],point_unary(name,x[1])[1])
def binary(name,x,y):
    out=M(); a=M(); b=M()
    for z in (out,a,b): lib.mpfr_init2(C.byref(z),PREC)
    vals=[]
    for rnd in (RNDD,RNDU):
        lib.mpfr_set_d(C.byref(a),C.c_double(x[0]),0); lib.mpfr_set_d(C.byref(b),C.c_double(y[0]),0); getattr(lib,name)(C.byref(out),C.byref(a),C.byref(b),rnd); vals.append(lib.mpfr_get_d(C.byref(out),rnd))
    lo=vals[0]
    vals=[]
    for rnd in (RNDD,RNDU):
        lib.mpfr_set_d(C.byref(a),C.c_double(x[1]),0); lib.mpfr_set_d(C.byref(b),C.c_double(y[1]),0); getattr(lib,name)(C.byref(out),C.byref(a),C.byref(b),rnd); vals.append(lib.mpfr_get_d(C.byref(out),rnd))
    hi=vals[1]
    lib.mpfr_clear(C.byref(out)); lib.mpfr_clear(C.byref(a)); lib.mpfr_clear(C.byref(b)); return (min(lo,hi),max(lo,hi))

def add(x,y): return binary('mpfr_add',x,y)
def sub(x,y): return binary('mpfr_sub',x,y)
def mul(x,y):
    corners=[binary('mpfr_mul',(a,a),(b,b)) for a in x for b in y]
    return (min(v[0] for v in corners),max(v[1] for v in corners))
def div(x,y):
    if y[0]<=0<=y[1]: raise ValueError('division interval crosses zero')
    corners=[binary('mpfr_div',(a,a),(b,b)) for a in x for b in y]
    return (min(v[0] for v in corners),max(v[1] for v in corners))
def exact(x): return (math.nextafter(float(x),-math.inf),math.nextafter(float(x),math.inf))
def neg(x): return (-x[1],-x[0])
def atom(y,xi,families,coefficients):
    total=(0.0,0.0)
    for coefficient,(width,theta) in zip(coefficients,families):
        r=exact(width*width); yy=exact(y); u=div(yy,r); q=sub(exact(1.0),mul(u,u))
        if q[1]<=0: continue
        phi=unary('mpfr_exp',div(exact(-30.0),q)); amp=unary('mpfr_exp',mul(exact(.5),yy))
        angle=mul(exact((theta-2*math.pi*xi)*y),exact(1.0)); co=unary('mpfr_cos',angle); si=unary('mpfr_sin',angle)
        scale=mul(phi,amp); cr=exact(float(coefficient.real)); ci=exact(float(coefficient.imag))
        re=sub(mul(mul(cr,scale),co),mul(mul(ci,scale),si)); im=add(mul(mul(cr,scale),si),mul(mul(ci,scale),co))
        total=(add(total,re)[0],add(total,re)[1]) if False else add(total,re)
        imag_total=add((0.0,0.0),im) if False else im
        # Keep imaginary accumulator separately.
        if 'imag' not in locals(): imag=(0.0,0.0)
        imag=add(imag,im)
    return total,imag

def main():
    capture=json.loads(CAPTURE.read_text()); owner=capture['owner_capture']; families=[(float.fromhex(a),float.fromhex(b)) for a,b in owner['families_hex']]
    base=[complex(float.fromhex(a),float.fromhex(b)) for a,b in owner['base_hex']]; corr=[complex(float.fromhex(a),float.fromhex(b)) for a,b in owner['corr_hex']]
    rows=[]
    half=max(w*w for w,_ in families)
    for xi in (40.0,120.0,200.0):
        for index in range(1,10):
            y=-half+2*half*index/10
            br,bi=atom(y,xi,families,base); cr,ci=atom(y,xi,families,corr)
            rows.append({'xi':xi,'y':y,'base_radius':max(br[1]-br[0],bi[1]-bi[0]),'corr_radius':max(cr[1]-cr[0],ci[1]-ci[0]),'base_finite':all(math.isfinite(v) for pair in (br,bi) for v in pair),'corr_finite':all(math.isfinite(v) for pair in (cr,ci) for v in pair)})
    result={'record':2286,'status':'MPFR-DIRECTED-OWNER-ATOM-PREFLIGHT','certificate':False,'hgap_closed':False,'backend':{'library':'libmpfr.so.6','precision_bits':PREC,'rounding':'RNDD/RNDU'},'owner':{'families':len(families),'support_half_width':half,'prime_power_count':41136},'rows':rows,'nonclaims':['fixed atoms only; no quadrature enclosure','no infinite xi tail','no hgap supplier, producer GO or RH claim']}
    result['max_base_radius']=max(r['base_radius'] for r in rows); result['max_corr_radius']=max(r['corr_radius'] for r in rows)
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'max_base_radius':result['max_base_radius'],'max_corr_radius':result['max_corr_radius']}))
if __name__=='__main__': main()


