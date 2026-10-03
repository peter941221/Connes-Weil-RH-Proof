"""Exact production-constant pricing; not a Lean full-grid certificate."""
import argparse
from fractions import Fraction
import hashlib
import json
from multiprocessing import Pool
from math import comb,isqrt
from pathlib import Path
import time

import flint
from flint import fmpq as Q

ROOT = Path(__file__).resolve().parents[1]
R = Q(65536001,10000000)
H = Q(65536001,51200000000)
PIN = Q(13895471891,5000000000)
B160,B200 = 2**160,2**200
DELTA = Q(1,2**159)
POLYS = ((1,), (0,60), (60,0,3480,0,180),
         (0,10080,0,193680,0,31680,0,720),
         (10080,0,1085040,0,10189440,0,3575520,0,266400,0,3600))


def rational(value):
    v = Fraction(value)
    return Q(v.numerator,v.denominator)


def ceilq(value,scale):
    return Q((value*scale).ceil(),scale)


def floorq(value,scale):
    return Q((value*scale).floor(),scale)


def root_upper(square,scale):
    return Q(isqrt(int((square*scale*scale).floor()))+1,scale)


def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def magnitude(z):
    return abs(z[0])+abs(z[1])


def exp_replay(w):
    depth = 0
    while magnitude(w) > 2**depth:
        depth += 1
    assert depth <= 64
    z = w[0]/2**depth,w[1]/2**depth
    center = Q(1),Q(0)
    for j in range(19,0,-1):
        product = mul(z,center)
        center = floorq(1+product[0]/j,B160),floorq(product[1]/j,B160)
    error = Q(1,10**18)+19*DELTA
    for _ in range(depth):
        error = ceilq(error*(2*magnitude(center)+error)+DELTA,B200)
        product = mul(center,center)
        center = floorq(product[0],B160),floorq(product[1],B160)
    return center,error,depth


def load_families():
    capture = json.loads((ROOT/"results/2275_gap_owner_audit.json").read_text())["owner_capture"]["families_hex"]
    rows = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    assert len(capture) == len(rows) == 30
    result = []
    for i,(pair,row) in enumerate(zip(capture,rows)):
        assert row["index"] == i
        radius = rational(Fraction.from_float(float.fromhex(pair[0])))**2
        theta = rational(Fraction.from_float(float.fromhex(pair[1])))
        c = tuple((rational(row["ideal_base_coefficient"][part]["lower_exact"])+
                   rational(row["ideal_base_coefficient"][part]["upper_exact"]))/2 for part in ("real","imag"))
        result.append(dict(radius=radius,theta=theta,c=c,l1=magnitude(c),
            cm=magnitude(c)+Q(1,10**30),frequency=root_upper(Q(1,4)+theta*theta,2**40)))
    return result


def family_jet(f,x,sigma,order):
    radius,theta = f["radius"],f["theta"]
    if abs(x) >= radius:
        return (Q(0),Q(0)),Q(0),(Q(0),Q(0)),0
    deficit = 1-(x/radius)**2
    center,error,depth = exp_replay((sigma*x-30/deficit,theta*x))
    first = sigma-60*x/(radius**2*deficit**2),theta
    second = -60/(radius**2*deficit**2)-240*x*x/(radius**4*deficit**3)
    squared = mul(first,first)
    if order == 2:
        factor = squared[0]+second,squared[1]
    else:
        assert order == 3
        third = -720*x/(radius**4*deficit**3)-1440*x**3/(radius**6*deficit**4)
        cube = mul(squared,first)
        factor = cube[0]+3*first[0]*second+third,cube[1]+3*first[1]*second
    return center,error,factor,depth


def point(families,index,sigma,order):
    x = -R+index*H
    total,charge = (Q(0),Q(0)),Q(0)
    norms,depths = [],[]
    for f in families:
        center,error,factor,depth = family_jet(f,x,sigma,order)
        depths.append(depth)
        if order == 3:
            assert magnitude(center)+error <= 1
            product = mul(factor,center)
            norm = ceilq(root_upper(product[0]**2+product[1]**2,B160)+magnitude(factor)*error,B160)
            norms.append(norm)
            out,rad = center,error
        else:
            product = mul(factor,center)
            out = floorq(product[0],2**100),floorq(product[1],2**100)
            rad = ceilq(magnitude(factor)*error+Q(1,2**99),2**140)
            assert magnitude(out)+rad <= 1
        contribution = mul(f["c"],out)
        total = total[0]+contribution[0],total[1]+contribution[1]
        charge += f["l1"]*rad
    if order == 3:
        assert charge <= Q(1,10**12)
        assert charge+Q(30,10**30) <= Q(1,10**10)
        upper = root_upper(total[0]**2+total[1]**2,10**10)+Q(1,10**10)
    else:
        assert charge <= Q(1,10**8)
        assert charge+Q(30,10**30) <= Q(1,10**7)
        upper = root_upper(total[0]**2+total[1]**2,10**8)+Q(1,10**7)
    return dict(upper=upper,charge=charge,norms=norms,max_depth=max(depths))


def fourth(f,a,b,sigma):
    radius = f["radius"]
    near = min(abs(a),abs(b))/radius
    if near >= 1:
        return Q(0)
    assert a*b >= 0
    far = min(max(abs(a),abs(b)),radius)/radius
    exponent = max(sigma*a,sigma*b)-30/(1-near*near)
    center,error,_ = exp_replay((exponent,Q(0)))
    poly = sum(comb(4,j)*f["frequency"]**j*
        sum(Q(c)*far**k for k,c in enumerate(POLYS[4-j]))*
        (1-near*near)**(-2*(4-j))/radius**(4-j) for j in range(5))
    return ceilq((magnitude(center)+error)*poly,B160)


def cell(families,index,sign,left=None):
    sigma = Q(sign,2)
    left = point(families,Q(index),sigma,3) if left is None else left
    right = point(families,Q(index+1),sigma,3)
    midpoint = point(families,Q(2*index+1,2),sigma,2)
    a,b = -R+index*H,-R+(index+1)*H
    fourths = [fourth(f,a,b,sigma) for f in families]
    thirds = [ceilq(f["cm"]*(max(l,r)+H*v/2),10**6)
              for f,l,r,v in zip(families,left["norms"],right["norms"],fourths)]
    third = sum(thirds)
    curvature = ceilq(midpoint["upper"]+third*H/2,10**6)
    node = H*(left["upper"]+right["upper"])/2
    remainder = curvature*H**3/12
    integral = ceilq(node+remainder,10**12)
    return dict(index=index,sign=sign,left=str(left["upper"]),right=str(right["upper"]),
        midpoint=str(midpoint["upper"]),third=str(third),curvature=str(curvature),
        integral=str(integral),node=str(node),remainder=str(remainder),
        endpoint_charge_max=str(max(left["charge"],right["charge"])),
        midpoint_charge=str(midpoint["charge"]),
        max_depth=max(left["max_depth"],right["max_depth"],midpoint["max_depth"])),right


def source_hashes():
    paths = ["scripts/price_production_grid_2560.py","results/2338_exact_interpolation_repair.json",
        "results/2275_gap_owner_audit.json","ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean",
        "scripts/generate_signed_cells_2558.py","scripts/generate_cell_integral_2546.py",
        "scripts/generate_fourth_envelope_2545.py","scripts/generate_signed_midpoint_2543.py",
        "scripts/generate_endpoint_norms_2544.py","scripts/generate_adaptive_nodes_2542.py",
        "scripts/price_boundary_precision_2547.py"]
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in paths}


def run_span(task):
    start,count,sign = task
    families,left,rows = load_families(),None,[]
    for index in range(start,start+count):
        row,left = cell(families,index,sign,left)
        rows.append(row)
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--count",type=int,default=10240)
    parser.add_argument("--workers",type=int,default=1)
    parser.add_argument("--output",type=Path,default=ROOT/"results/2560_production_grid_price.json")
    args = parser.parse_args()
    assert 0 <= args.start < args.start+args.count <= 10240
    begin = time.monotonic()
    assert 1 <= args.workers <= 8
    signs = []
    for sign in (-1,1):
        tasks = [(start,min(256,args.start+args.count-start),sign)
                 for start in range(args.start,args.start+args.count,256)]
        rows = []
        if args.workers == 1:
            spans = map(run_span,tasks)
            for span in spans:
                rows.extend(span)
                print("GRID",sign,span[-1]["index"]+1,"elapsed",round(time.monotonic()-begin,2),flush=True)
        else:
            with Pool(args.workers) as pool:
                for span in pool.imap(run_span,tasks):
                    rows.extend(span)
                    print("GRID",sign,span[-1]["index"]+1,"elapsed",round(time.monotonic()-begin,2),flush=True)
        total = sum(Q(row["integral"]) for row in rows)
        signs.append(dict(sign=sign,rows=rows,total=str(total),pin=str(PIN),margin=str(PIN-total),
            fits_pin=total <= PIN,display=dict(total=float(total),margin=float(PIN-total))))
    result = dict(record=2560,status="EXACT_PRODUCTION_PRICE_NOT_LEAN",start=args.start,count=args.count,
        flint_version=flint.__version__,workers=args.workers,signs=signs,elapsed_seconds=time.monotonic()-begin,
        source_sha256=source_hashes(),full_grid_certificate=False,exact_coefficient_membership=False,
        producer_go=False,rh_claim=False)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print("PRODUCTION_PRICE",[(r["sign"],r["display"]) for r in signs],flush=True)
