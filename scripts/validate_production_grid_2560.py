"""Check production pricing against accepted Lean constants and old arithmetic."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from multiprocessing import Pool
from pathlib import Path
import re

import price_production_grid_2560 as p
from price_boundary_precision_2547 import precision_evaluate
from routea_derivative_pricing_2543 import multiplier
from validate_adaptive_nodes_2542 import scalar_def


def lean(module):
    return (p.ROOT/f"ConnesWeilRH/Dev/{module}.lean").read_text()


def controls():
    families,rows,jet_count = p.load_families(),[],0
    for index,sign in ((2700,1),(2701,1),(2700,-1),(2701,-1),
                       (5119,1),(5120,1),(5119,-1),(5120,-1)):
        if (index,sign) == (2700,1):
            module,prefix,record = "C1RouteABoundaryIntegral2551","boundaryCell",2551
        elif (index,sign) == (2701,1):
            module,prefix,record = "C1RouteANeighborIntegral2557","neighborCell",2557
        else:
            record = 2558 if index < 3000 else 2559
            prefix = f"batchC{index:05d}{'Plus' if sign>0 else 'Minus'}Cell"
            module = "C1RouteA"+prefix[0].upper()+prefix[1:-4]+"Integral"+str(record)
        row,_ = p.cell(families,index,sign)
        source = lean(module)
        for key in ("third","curvature","integral"):
            assert F(row[key]) == scalar_def(source,prefix+key.capitalize()+"Upper"+str(record)),(module,key)
        rows.append(dict(index=index,sign=sign,module=module,integral=row["integral"]))
    for index in (F(0),F(2700),F(5401,2),F(5120),F(10241,2),F(5440),F(10239),F(10240)):
        x = -F(65536001,10000000)+index*F(65536001,51200000000)
        for sign in (-1,1):
            for f in families:
                radius,theta = F(str(f["radius"])),F(str(f["theta"]))
                for order in (2,3):
                    center,error,factor,depth = p.family_jet(f,p.rational(x),p.Q(sign,2),order)
                    old_center,old_error,old_depth = precision_evaluate(radius,theta,x,F(sign,2),160)
                    old_factor = multiplier(order,radius,theta,F(sign,2),x) if abs(x)<radius else (F(0),F(0))
                    assert tuple(F(str(v)) for v in center) == old_center
                    assert F(str(error)) == old_error and depth == old_depth
                    assert tuple(F(str(v)) for v in factor) == old_factor
                    jet_count += 1
    tasks = [(2700,2,-1),(5119,2,1)]
    sequential = list(map(p.run_span,tasks))
    with Pool(2) as pool:
        parallel = list(pool.map(p.run_span,tasks))
    assert parallel == sequential
    pin_source = lean("C1RouteAEndpointStrip")
    pin = F(re.search(r"def baseNormUpper2343 : ℝ := ([0-9.]+)",pin_source)[1])
    assert pin == F(str(p.PIN))
    return dict(accepted_cells=rows,exact_jet_controls=jet_count,
                parallel_span_control=True,pin=str(pin))


def read_price(data):
    assert data["start"] == 0 and data["count"] == 10240
    assert data["source_sha256"] == p.source_hashes()
    assert [s["sign"] for s in data["signs"]] == [-1,1]
    h,pin = F(str(p.H)),F(str(p.PIN))
    reports = []
    for entry in data["signs"]:
        rows = entry["rows"]
        assert len(rows) == 10240
        total,node,remainder,previous = F(0),F(0),F(0),None
        for index,row in enumerate(rows):
            assert row["index"] == index and row["sign"] == entry["sign"]
            left,right,mid,third,curvature,integral = (F(row[k]) for k in
                ("left","right","midpoint","third","curvature","integral"))
            assert min(left,right,mid,third,curvature,integral) >= 0
            if previous is not None:
                assert left == previous
            previous = right
            assert F(row["node"]) == h*(left+right)/2
            assert curvature >= mid+third*h/2 and curvature-(mid+third*h/2) < F(1,10**6)
            assert F(row["remainder"]) == curvature*h**3/12
            residual = integral-F(row["node"])-F(row["remainder"])
            assert 0 <= residual < F(1,10**12)
            assert F(row["endpoint_charge_max"]) <= F(1,10**12)
            assert F(row["midpoint_charge"]) <= F(1,10**8)
            total += integral
            node += F(row["node"])
            remainder += F(row["remainder"])
        assert F(entry["total"]) == total and F(entry["margin"]) == pin-total
        assert entry["fits_pin"] == (total <= pin)
        reports.append(dict(sign=entry["sign"],total=str(total),margin=str(pin-total),
            node=str(node),remainder=str(remainder),rounding=str(total-node-remainder),
            display=dict(total=float(total),margin=float(pin-total),node=float(node),
                         remainder=float(remainder),rounding=float(total-node-remainder))))
    return reports


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--price",type=Path)
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    result = dict(record=2560,controls=controls(),full_grid_certificate=False,
                  exact_coefficient_membership=False,producer_go=False,rh_claim=False)
    if args.price:
        data = json.loads(args.price.read_text())
        result["signs"] = read_price(data)
        result["price_sha256"] = hashlib.sha256(args.price.read_bytes()).hexdigest()
        from copy import deepcopy
        bad = deepcopy(data)
        bad["signs"][0]["rows"][5120]["integral"] = "0"
        try:
            read_price(bad)
        except AssertionError:
            result["zeroed_cell_rejected"] = True
        else:
            raise AssertionError("Zeroed cell accepted")
    result["status"] = "EXACT_PRICE_CONTROLS_PASS" if not args.price else "EXACT_GRID_PRICE_READBACK_PASS_NOT_LEAN"
    strip_source = lean("C1RouteAEndpointStrip")
    pins = {name:F(re.search(r"def "+name+r" : ℝ := ([0-9.]+)",strip_source)[1]) for name in
            ("baseNormUpper2343","baseSecondUpper2343","correctionNormUpper2343","correctionSecondUpper2343")}
    budget = F(re.search(r"def bUpper2243 : Real := ([0-9.]+)",lean("C1RouteAItem5Arithmetic"))[1])
    product = pins["baseNormUpper2343"]*pins["correctionSecondUpper2343"]
    assert product <= budget
    result["consumer_budget"] = dict(pins={k:str(v) for k,v in pins.items()},budget=str(budget),
        chosen_product=str(product),slack=str(budget-product),
        display=dict(chosen_product=float(product),budget=float(budget),slack=float(budget-product)))
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:|declaration uses 'sorry'|warning: .*2560\.lean",log,re.M)
        module = "ConnesWeilRH/Dev/C1RouteATwoChannelStrip2560.lean"
        expected = set(re.findall(r"#print axioms ConnesWeilRH.Dev.(\w+)",(p.ROOT/module).read_text()))
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+2560)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected
        assert all(ax == ["propext","Classical.choice","Quot.sound"] for ax in audits.values())
        pending,hashes = ["ConnesWeilRH.lean",module],{}
        while pending:
            path = pending.pop()
            if path in hashes:
                continue
            data = (p.ROOT/path).read_bytes()
            assert data == (args.mirror/path).read_bytes(),path
            hashes[path] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(m.replace(".","/")+".lean" for m in line[7:].split() if m.startswith("ConnesWeilRH"))
        for path in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
            assert (p.ROOT/path).read_bytes() == (args.mirror/path).read_bytes()
        result.update(two_channel_bridge="BUILD_AXIOM_SOURCE_PASS",audits=audits,source_sha256=hashes,
            build_footer=footers[-1],build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (p.ROOT/"results/2560_production_grid_validation.json").write_text(json.dumps(result,indent=2)+"\n")
    print(result["status"],result.get("signs",[]),flush=True)
