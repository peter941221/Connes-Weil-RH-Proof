"""Price fixed-precision derivative errors at named production midpoints."""
from fractions import Fraction as Q
import json
import hashlib
from math import comb
from pathlib import Path

from generate_complex_exp_node_2541 import ROOT, CAPTURE, add, mul, scale
from routea_exp_schedule_probe_2542 import evaluate, R, STEP


def multiplier(order, radius, theta, sigma, x):
    u = x/radius
    q = 1-u*u
    polys = [Q(1), -60*u, -60+3480*u**2+180*u**4,
             10080*u-193680*u**3-31680*u**5-720*u**7,
             10080-1085040*u**2+10189440*u**4+3575520*u**6+266400*u**8+3600*u**10]
    power, total = (Q(1),Q(0)), (Q(0),Q(0))
    for i in range(order+1):
        k = order-i
        total = add(total,scale(power,comb(order,i)*polys[k]/(radius**k*q**(2*k))))
        power = mul(power,(sigma,theta))
    return total


if __name__ == "__main__":
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    rows = []
    for index in (5120,5440,10239):
        x = -R+(Q(index)+Q(1,2))*STEP
        for sigma in (Q(-1,2),Q(1,2)):
            for order in (2,3):
                total, charge = (Q(0),Q(0)), Q(0)
                for raw,row in zip(capture,coefficients):
                    width,theta = (Q.from_float(float.fromhex(v)) for v in raw)
                    radius = width**2
                    if abs(x) >= radius:
                        continue
                    value = evaluate(radius,theta,x,sigma)
                    factor = multiplier(order,radius,theta,sigma,x)
                    coefficient = tuple((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                                         Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2
                                        for p in ("real","imag"))
                    total = add(total,mul(coefficient,mul(factor,value["center"])))
                    charge += sum(abs(v) for v in coefficient)*sum(abs(v) for v in factor)*value["error"]
                cell_charge = charge*STEP**3/12 if order == 2 else charge*STEP**4/24
                rows.append(dict(index=index,position=str(x),sigma=str(sigma),order=order,
                                 evaluation_charge=str(charge),evaluation_charge_float=float(charge),
                                 cell_charge=str(cell_charge),cell_charge_float=float(cell_charge),
                                 cell_allowance_pass=cell_charge <= Q(1,10**8)))
    result = dict(record=2543,scope="bounded midpoint pricing, not a Lean derivative certificate",
                  decision="test fixed precision against a 1e-8 local error allowance",
                  third_order_caveat="h^4/24 is a hypothetical third-cell charge; a midpoint value is not a supremum or endpoint certificate",
                  rows=rows,all_pass=all(row["cell_allowance_pass"] for row in rows),
                  second_order_pass=all(row["cell_allowance_pass"] for row in rows if row["order"] == 2),
                  third_order_pass=all(row["cell_allowance_pass"] for row in rows if row["order"] == 3),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  capture_sha256=hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
                  coefficient_sha256=hashlib.sha256((ROOT/"results/2338_exact_interpolation_repair.json").read_bytes()).hexdigest(),
                  full_grid_certificate=False,producer_go=False,rh_claim=False)
    (ROOT/"results/2543_derivative_pricing.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "rows"}),flush=True)
    for row in rows:
        print(row["index"],row["sigma"],row["order"],row["evaluation_charge_float"],row["cell_charge_float"],flush=True)
