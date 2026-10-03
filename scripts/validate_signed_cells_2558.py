"""Independently read signed cell payloads and check their numeric assembly."""
from fractions import Fraction as Q
import json
import re
import argparse
import hashlib
from pathlib import Path

from generate_signed_cells_2558 import ROOT,Cell,endpoint,endpoint_value,read,rename,scalar_layout,tag
from validate_adaptive_nodes_2542 import scalar_def,check as check_value
from validate_boundary_jets_2548 import check as check_jet
from validate_boundary_fourth_2550 import check as check_fourth
from validate_endpoint_thirds_2544 import check_norms
from validate_midpoint_derivatives_2543 import check_signed


def normalize(source,old,record,new,target):
    return scalar_layout(rename(source,old,record,new,target))


def check(cell,source):
    sides,values,jets = [],[],[]
    for side,offset in (("Left",0),("Right",1)):
        index = cell.index+offset
        parent,record,module = endpoint(index,cell.sign,cell.record)
        base = read(module)
        jets.append(check_jet(normalize(base,parent,record,"edge"+side,2548),side,
                              grid_order=(Q(index),3),sigma=Q(cell.sign,2)))
        sides.append(check_norms(
            normalize(read(cell.module(side+"Bounds")),cell.prefix+side,cell.record,"endpoint"+side,2544),
            normalize(base,parent,record,"endpoint"+side,2544),side))
        vp,vr,vm = endpoint_value(index,cell.sign,cell.record)
        values.append(check_value(normalize(read(vm),vp,vr,"adaptive"+tag(index,cell.sign),2542),
            index,cell.sign,shared_source=base,shared_prefix=parent,shared_record=record))
    raw_mid = read(cell.module("Midpoint"))
    jets.append(check_jet(normalize(raw_mid,cell.prefix+"Midpoint",cell.record,"edgeMidpoint",2548),
        "Midpoint",grid_order=(Q(2*cell.index+1,2),2),sigma=Q(cell.sign,2)))
    mids = normalize(read(cell.module("MidpointBounds")),cell.prefix+"Midpoint",cell.record,"midpoint",2543)
    mids = normalize(mids,cell.prefix+"SignedMidpoint",cell.record,"signedMidpoint",2543)
    mid = check_signed(mids,normalize(raw_mid,cell.prefix+"Midpoint",cell.record,"midpoint",2543))
    fourth = normalize(read(cell.module("Fourth")),cell.prefix+"Fourth",cell.record,"edgeFourth",2550)
    assert len(check_fourth(fourth,cell_index=cell.index,sigma=Q(cell.sign,2))) == 30
    # The opposite sign must not accept these exponent witnesses. This checks
    # the endpoint-growth choice independently of a generator's symbol labels.
    try:
        check_fourth(fourth,cell_index=cell.index,sigma=Q(-cell.sign,2))
    except AssertionError:
        pass
    else:
        raise AssertionError("Opposite-sign fourth exponent accepted")
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    h,total = Q(65536001,51200000000),Q(0)
    for i,row in enumerate(coefficients):
        cm = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                      Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                 for p in ("real","imag"))+Q(1,10**30)
        term = max(sides[0][i],sides[1][i])+h/2*scalar_def(fourth,f"edgeFourthP{i:03d}Upper2550")
        upper = scalar_def(source,cell.prefix+f"CellP{i:03d}Charge{cell.record}")
        assert upper >= cm*term
        total += upper
    third,curvature,integral = (scalar_def(source,cell.prefix+"Cell"+name+"Upper"+str(cell.record))
                                for name in ("Third","Curvature","Integral"))
    assert third >= total
    assert curvature >= Q(mid["signed_upper"])+third*h/2
    assert integral >= sum(Q(v["signed_upper"]) for v in values)*h/2+curvature*h**3/12
    return dict(index=cell.index,sign=cell.sign,jets=jets,values=values,midpoint=mid,
                third=str(third),curvature=str(curvature),integral=str(integral),
                opposite_sign_fourth_rejected=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    parser.add_argument("--cost-log",type=Path)
    args = parser.parse_args()
    reports = []
    for index in (2700,2701):
        cell = Cell(index,-1)
        source = read(cell.module("Integral"))
        report = check(cell,source)
        corrupted = re.sub(r"(noncomputable def "+cell.prefix+r"CellIntegralUpper2558\b.*?:=).*?(?=\n\n)",
                           r"\1 (0 : ℝ)",source,count=1,flags=re.S)
        assert corrupted != source
        try:
            check(cell,corrupted)
        except AssertionError:
            pass
        else:
            raise AssertionError("Zeroed integral accepted")
        expected = {"Midpoint":cell.render_midpoint(),"MidpointBounds":cell.render_midpoint_bounds()[0],
            "Fourth":cell.render_fourth(),"Assembly":cell.render_assembly(),"Integral":cell.render_integral()[0]}
        expected.update({side+"Bounds":cell.render_norm(side) for side in ("Left","Right")})
        for name,text in expected.items():
            assert read(cell.module(name)) == text,cell.module(name)
        report.update(zeroed_integral_rejected=True,regeneration=True)
        reports.append(report)
        print(index,report["integral"],flush=True)
    result = dict(record=2558,cells=reports,full_grid_certificate=False,
        exact_coefficient_membership=False,rh_claim=False)
    from generate_signed_cells_2558 import render_endpoint,render_value
    for module,text in (render_endpoint(2702,-1),render_value(2702,-1)[:2]):
        assert read(module) == text,module
    # Keep both the established positive-cell generator and the old scalar
    # reader as regression anchors for the newly parameterized paths.
    from generate_neighbor_cell_2557 import render_integral
    assert render_integral()[0] == read("C1RouteANeighborIntegral2557")
    from generate_fourth_envelope_2545 import render as default_fourth
    from generate_boundary_fourth_2550 import render as default_boundary
    from generate_endpoint_norms_2544 import render as default_norm
    from generate_signed_midpoint_2543 import render as default_midpoint
    from generate_cell_integral_2546 import render as default_integral
    assert default_fourth(30)[0] == read("C1RouteAFourthEnvelope2545")
    assert default_boundary()[0] == read("C1RouteABoundaryFourth2550")
    assert default_midpoint()[0] == read("C1RouteASignedMidpoint2543")
    assert default_integral()[0] == read("C1RouteACellIntegral2546")
    for side in ("Left","Right"):
        assert default_norm(side,30) == read("C1RouteAEndpoint"+side+"Norms2544")
    assert scalar_def("noncomputable def test : ℝ := ((7 :\n ℝ) / 11)\n\n", "test") == Q(7,11)
    result.update(endpoint_regeneration=True,positive_integral_regression=True,
                  split_scalar_cast_regression=True,default_regressions=6)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:|declaration uses 'sorry'|warning: .*2558\.lean",log,re.M)
        paths = sorted((ROOT/"ConnesWeilRH/Dev").glob("C1RouteA*2558.lean"))
        expected = set()
        for path in paths:
            expected.update(re.findall(r"#print axioms ConnesWeilRH.Dev.(\w+)",path.read_text()))
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+2558)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected,(expected-set(audits),set(audits)-expected)
        assert all(ax == ["propext","Classical.choice","Quot.sound"] for ax in audits.values())
        pending = ["ConnesWeilRH.lean"]+[str(p.relative_to(ROOT)) for p in paths]
        hashes = {}
        while pending:
            path = pending.pop()
            if path in hashes:
                continue
            data = (ROOT/path).read_bytes()
            assert data == (args.mirror/path).read_bytes(),path
            hashes[path] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(m.replace(".","/")+".lean" for m in line[7:].split() if m.startswith("ConnesWeilRH"))
        for path in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
            assert (ROOT/path).read_bytes() == (args.mirror/path).read_bytes()
        result.update(status="BOTH_SIGNS_SEGMENT_BUILD_AXIOM_SOURCE_PASS",audits=audits,
            source_sha256=hashes,build_footer=footers[-1],
            build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
            conditional_negative_segment_upper="4934/1000000000000",
            conditional_both_signs_sum_upper="5159/1000000000000")
    if args.cost_log:
        cost = args.cost_log.read_text()
        assert re.search(r"^Build completed successfully",cost,re.M)
        match = re.search(r"SIGNED_CELL_BUILD elapsed=([\d.]+) user=([\d.]+) system=([\d.]+) peak_kib=(\d+)",cost)
        assert match
        result.update(cell_build_cost=dict(zip(("elapsed","user","system","peak_kib"),match.groups())),
                      cost_log_sha256=hashlib.sha256(args.cost_log.read_bytes()).hexdigest())
    (ROOT/"results/2558_signed_cell_readback.json").write_text(json.dumps(result,indent=2)+"\n")
