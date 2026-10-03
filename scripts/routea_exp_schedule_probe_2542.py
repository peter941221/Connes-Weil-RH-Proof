"""Price adaptive squaring against a named 1e-8 node-evaluation allowance."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time

from generate_complex_exp_node_2541 import add, mul, scale, rounded, up, witness

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT/"results/2275_gap_owner_audit.json"
REPAIR = ROOT/"results/2338_exact_interpolation_repair.json"
R = Q(65536001,10**7)
STEP = 2*R/10240
DELTA = Q(1,2**99)
ALLOWANCE = Q(1,10**8)


def evaluate(radius, theta, x, sigma, fixed_depth=None):
    if abs(x) >= radius:
        return dict(exterior=True,depth=0,center=(Q(0),Q(0)),error=Q(0))
    w = (sigma*x-30/(1-(x/radius)**2),theta*x)
    size = abs(w[0])+abs(w[1])
    depth = 0
    while size > 2**depth:
        depth += 1
    if fixed_depth is not None:
        assert size <= 2**fixed_depth, "fixed schedule violates the unit-disk gate"
        depth = fixed_depth
    assert depth <= 64, "unpriced squaring depth"
    z = scale(w,Q(1,2**depth))
    h = [(Q(1),Q(0))]
    for k in range(19,0,-1):
        exact = add((Q(1),Q(0)),mul(scale(z,Q(1,k)),h[-1]))
        center = rounded(exact)
        assert sum(abs(a-b) for a,b in zip(exact,center)) <= DELTA
        h.append(center)
    squares, errors, magnitudes = [h[-1]], [Q(1,10**18)+19*DELTA], []
    for _ in range(depth):
        magnitude = sum(abs(v) for v in squares[-1])
        exact = mul(squares[-1],squares[-1])
        center = rounded(exact)
        assert sum(abs(a-b) for a,b in zip(exact,center)) <= DELTA
        errors.append(up(errors[-1]*(2*magnitude+errors[-1])+DELTA))
        squares.append(center)
        magnitudes.append(magnitude)
    return dict(exterior=False,depth=depth,center=squares[-1],error=errors[-1],
                fixed_six_valid=size<=64,trace=(z,h,squares,errors,magnitudes))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=ROOT/"results/2542_exp_schedule_probe.json")
    args = parser.parse_args()
    started = time.monotonic()
    capture = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    repair = json.loads(REPAIR.read_text())
    assert repair["capture_sha256"] == hashlib.sha256(CAPTURE.read_bytes()).hexdigest()
    families = []
    for pair,row in zip(capture,repair["coefficient_rows"]):
        width,theta = (Q.from_float(float.fromhex(v)) for v in pair)
        center = tuple((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                        Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2
                       for p in ("real","imag"))
        families.append((width**2,theta,center))
    assert len(families) == 30
    for i,(radius,theta,_) in enumerate(families):
        control = evaluate(radius,theta,STEP,Q(1,2),fixed_depth=6)
        assert control["trace"] == witness(i), i
    positions = {(-R+j*STEP):f"grid_{j:05d}" for j in
                 (0,1,1280,2560,3840,4800,5040,5119,5120,5121,5200,5440,6400,7680,8960,10239,10240)}
    for i,(radius,_,_) in enumerate(families):
        for sign in (-1,1):
            positions[sign*radius] = f"family_{i:03d}_edge_{sign}"
            positions[sign*radius*(1-Q(1,2**24))] = f"family_{i:03d}_inside_24bit_{sign}"
            index = int((sign*radius+R)//STEP)
            for j in (index,index+1):
                if 0 <= j <= 10240:
                    positions[-R+j*STEP] = f"grid_{j:05d}"
    rows = []
    max_depth = fixed_failures = exterior_count = 0
    for x,label in sorted(positions.items()):
        for sigma in (Q(-1,2),Q(1,2)):
            charge, signed = Q(0),(Q(0),Q(0))
            depths = []
            for radius,theta,coefficient in families:
                item = evaluate(radius,theta,x,sigma)
                exterior_count += item["exterior"]
                if not item["exterior"]:
                    fixed_failures += not item["fixed_six_valid"]
                depths.append(item["depth"])
                charge += sum(abs(v) for v in coefficient)*item["error"]
                signed = add(signed,mul(coefficient,item["center"]))
            max_depth = max(max_depth,max(depths))
            rows.append(dict(label=label,x=str(x),sigma=str(sigma),max_depth=max(depths),
                             charge_exact=str(charge),charge_display=float(charge),
                             signed_center_display=[float(v) for v in signed],
                             allowance_pass=charge<=ALLOWANCE))
    worst = max(rows,key=lambda row:Q(row["charge_exact"]))
    result = dict(record=2542,status="ADAPTIVE_SCHEDULE_SAMPLE_PASS" if all(r["allowance_pass"] for r in rows)
                  else "ADAPTIVE_SCHEDULE_SAMPLE_FAIL",
                  scope="bounded order-zero arithmetic pricing; not a full-grid or Lean certificate",
                  decision="adaptive depth within 1e-8 node evaluation allowance",
                  node_allowance=str(ALLOWANCE),sample_positions=len(positions),rows=rows,
                  family_evaluations=len(rows)*30,fixed_six_unit_disk_failures=fixed_failures,
                  exterior_evaluations=exterior_count,max_squaring_depth=max_depth,worst_row=worst,
                  parent_2541_same_run_traces_identical=True,
                  capture_sha256=hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
                  coefficient_sha256=hashlib.sha256(REPAIR.read_bytes()).hexdigest(),
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic()-started,
                  full_grid_certificate=False,derivative_certificate=False,producer_go=False,rh_claim=False)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(result["status"],len(rows),"rows",max_depth,"max depth",
          float(Q(worst["charge_exact"])),"worst charge",fixed_failures,"fixed-depth refusals",flush=True)


if __name__ == "__main__":
    main()
