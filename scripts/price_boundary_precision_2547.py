"""Price actual boundary-cell derivative evaluation errors at 100/160 bits.

Decision: whether fixed 100-bit coordinates can be copied to the named
support-boundary cells under a 1e-8 per-cell derivative-error allowance.
The higher-precision path is planning only; no new Lean evaluator is claimed.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import time

from generate_complex_exp_node_2541 import ROOT, CAPTURE, add, mul, scale
from routea_exp_schedule_probe_2542 import evaluate, R, STEP
from routea_derivative_pricing_2543 import multiplier


def precision_evaluate(radius,theta,x,sigma,bits):
    if abs(x) >= radius:
        return (Q(0),Q(0)),Q(0),0
    w = sigma*x-30/(1-(x/radius)**2),theta*x
    return precision_exponential(w,bits)


def precision_exponential(w,bits):
    """Evaluate an exact complex exponent with the existing rational replay."""
    depth = 0
    while sum(abs(v) for v in w) > 2**depth:
        depth += 1
    assert depth <= 64
    z = scale(w,Q(1,2**depth))
    def down(v):
        s = v*2**bits
        return Q(s.numerator//s.denominator,2**bits)
    def up(v):
        s = v*2**(bits+40)
        return Q(-((-s.numerator)//s.denominator),2**(bits+40))
    delta = Q(1,2**(bits-1))
    center = Q(1),Q(0)
    for j in range(19,0,-1):
        center = tuple(down(v) for v in add((Q(1),Q(0)),mul(scale(z,Q(1,j)),center)))
    error = Q(1,10**18)+19*delta
    for _ in range(depth):
        error = up(error*(2*sum(abs(v) for v in center)+error)+delta)
        center = tuple(down(v) for v in mul(center,center))
    return center,error,depth


def main():
    start = time.monotonic()
    repair = ROOT/"results/2338_exact_interpolation_repair.json"
    coeffs = json.loads(repair.read_text())["coefficient_rows"]
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    families = []
    cells = {0,5120,5440,10239}
    for values,row in zip(raw,coeffs):
        width,theta = (Q.from_float(float.fromhex(v)) for v in values)
        radius = width**2
        coefficient = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                              Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                          for p in ("real","imag"))
        families.append((radius,theta,coefficient))
        for sign in (-1,1):
            crossing = int((sign*radius+R)//STEP)
            cells.update(j for j in (crossing-1,crossing,crossing+1) if 0 <= j < 10240)
    rows,controls = [],0
    cache = {}
    def up(v,bits):
        s = v*2**bits
        return Q(-((-s.numerator)//s.denominator),2**bits)
    def charges(x,sigma,bits,order):
        nonlocal controls
        out = []
        for i,(radius,theta,coefficient) in enumerate(families):
            if abs(x) >= radius:
                out.append(Q(0))
                continue
            key = i,x,sigma,bits
            if key not in cache:
                cache[key] = precision_evaluate(radius,theta,x,sigma,bits)
                if bits == 100:
                    old = evaluate(radius,theta,x,sigma)
                    assert cache[key] == (old["center"],old["error"],old["depth"])
                    controls += 1
            factor = multiplier(order,radius,theta,sigma,x)
            error = cache[key][1]
            # Same coefficient-weighted factor error as the accepted path.
            # Order-two center rounding has its separate scalar allowance.
            rounding = Q(1,2**(bits-1))
            radius_error = sum(abs(v) for v in factor)*error+rounding
            if order == 2:
                radius_error = up(radius_error,bits+40)
            # For order three, rounding includes the two coordinate-grid
            # allowances from the norm-square root and final scalar upper.
            out.append(coefficient*radius_error)
        return out
    for index in sorted(cells):
        a,b = -R+index*STEP,-R+(index+1)*STEP
        for sigma in (Q(-1,2),Q(1,2)):
            for bits in (100,160):
                mid = sum(charges((a+b)/2,sigma,bits,2))*STEP**3/12
                left,right = charges(a,sigma,bits,3),charges(b,sigma,bits,3)
                endpoints = sum(max(l,r) for l,r in zip(left,right))*STEP**4/24
                total = mid+endpoints
                exported = up(total,160)
                assert (exported <= Q(1,10**8)) == (total <= Q(1,10**8))
                rows.append(dict(index=index,sigma=str(sigma),bits=bits,
                                 midpoint_charge=str(up(mid,160)),endpoint_charge=str(up(endpoints,160)),
                                 total_charge=str(exported),total_display=float(exported),
                                 allowance_pass=total <= Q(1,10**8)))
        print("BOUNDARY_CELL_PRICED",index,flush=True)
    summary = {}
    for bits in (100,160):
        subset = [r for r in rows if r["bits"] == bits]
        worst = max(subset,key=lambda r:Q(r["total_charge"]))
        summary[str(bits)] = dict(cases=len(subset),failures=sum(not r["allowance_pass"] for r in subset),
                                  worst_index=worst["index"],worst_sigma=worst["sigma"],
                                  worst_charge=worst["total_charge"],worst_display=worst["total_display"])
    result = dict(record=2547,decision="100-bit boundary-cell derivative precision under 1e-8 allowance",
                  scope="actual endpoint/midpoint evaluation error only; fourth envelope and total integral excluded",
                  export_convention="charges rounded upward to 2^-160; allowance decision checked against exact unrounded total",
                  cells=sorted(cells),control_comparisons=controls,summary=summary,rows=rows,
                  high_precision_lean_certificate=False,full_grid_certificate=False,rh_claim=False,
                  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in (Path(__file__),CAPTURE,repair,
                                           ROOT/"scripts/routea_exp_schedule_probe_2542.py",
                                           ROOT/"scripts/routea_derivative_pricing_2543.py")},
                  elapsed_seconds=time.monotonic()-start)
    (ROOT/"results/2547_boundary_precision.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_PRECISION_RESULT",json.dumps(summary),"controls",controls,flush=True)


if __name__ == "__main__":
    main()
