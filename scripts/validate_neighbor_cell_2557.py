"""Independent exact arithmetic readback for neighboring cell2701."""
from fractions import Fraction as Q
import json
import re
import argparse
import hashlib
from pathlib import Path

from generate_complex_exp_node_2541 import ROOT
from validate_adaptive_nodes_2542 import scalar_def, check as check_value
from validate_boundary_jets_2548 import check as check_jet
from validate_boundary_fourth_2550 import check as check_fourth
from validate_endpoint_thirds_2544 import check_norms
from validate_midpoint_derivatives_2543 import check_signed


def read(name):
    return (ROOT/f"ConnesWeilRH/Dev/{name}.lean").read_text(encoding="utf-8")


def normalize(source,old,record,new,target):
    source = re.sub(r":\s*([ℝℚ])",r": \1",source)
    return re.sub(r"\b"+old+r"(\w*)"+str(record)+r"\b",lambda m:new+m[1]+str(target),source)


def check(source):
    jets = []
    for side,grid,order in (("Right",Q(2702),3),("Midpoint",Q(5403,2),2)):
        raw = read(f"C1RouteANeighbor{side}2557")
        jets.append(check_jet(normalize(raw,"neighbor"+side,2557,"edge"+side,2548),
                              side,grid_order=(grid,order)))
    sides = []
    for side in ("Left","Right"):
        prefix,record,module = (("kernelN02701Plus",2555,"C1RouteAKernelN02701Plus2555")
            if side == "Left" else ("neighborRight",2557,"C1RouteANeighborRight2557"))
        base = normalize(read(module),prefix,record,"endpoint"+side,2544)
        norms = normalize(read(f"C1RouteANeighbor{side}Bounds2557"),"neighbor"+side,2557,"endpoint"+side,2544)
        sides.append(check_norms(norms,base,side))
    mid = normalize(read("C1RouteANeighborMidpointBounds2557"),"neighborMidpoint",2557,"midpoint",2543)
    mid = normalize(mid,"neighborSignedMidpoint",2557,"signedMidpoint",2543)
    midpoint = check_signed(mid,normalize(read("C1RouteANeighborMidpoint2557"),"neighborMidpoint",2557,"midpoint",2543))
    fourth = normalize(read("C1RouteANeighborFourth2557"),"neighborFourth",2557,"edgeFourth",2550)
    assert len(check_fourth(fourth,cell_index=2701)) == 30
    value = normalize(read("C1RouteANeighborValueRight2557"),"neighborValueRight",2557,"adaptiveN02702Plus",2542)
    right = check_value(value,2702,1,shared_source=read("C1RouteANeighborRight2557"),
                        shared_prefix="neighborRight",shared_record=2557)
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    h,total = Q(65536001,51200000000),Q(0)
    for i,row in enumerate(coefficients):
        cm = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                      Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                 for p in ("real","imag"))+Q(1,10**30)
        term = max(sides[0][i],sides[1][i])+h/2*scalar_def(fourth,f"edgeFourthP{i:03d}Upper2550")
        upper = scalar_def(source,f"neighborCellP{i:03d}Charge2557")
        assert upper >= cm*term
        total += upper
    third = scalar_def(source,"neighborCellThirdUpper2557")
    curvature = scalar_def(source,"neighborCellCurvatureUpper2557")
    integral = scalar_def(source,"neighborCellIntegralUpper2557")
    assert third >= total
    assert curvature >= Q(midpoint["signed_upper"])+third*h/2
    left = scalar_def(read("C1RouteASharedN02701Plus2556"),"sharedN02701PlusUpper2556")
    assert integral >= (left+scalar_def(value,"adaptiveN02702PlusUpper2542"))*h/2+curvature*h**3/12
    return dict(jets=jets,right=right,third=str(third),curvature=str(curvature),integral=str(integral))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    source = read("C1RouteANeighborIntegral2557")
    result = check(source)
    corrupted = re.sub(r"(noncomputable def neighborCellIntegralUpper2557\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed integral upper accepted")
    result.update(record=2557,zeroed_integral_rejected=True,full_grid_certificate=False,
                  exact_coefficient_membership=False,rh_claim=False)
    from generate_neighbor_cell_2557 import render_jet,render_norm,render_midpoint,render_fourth,render_assembly,render_integral
    generated = {s:render_jet(s)[0] for s in ("Right","Midpoint")}
    generated.update({s+"Bounds":render_norm(s) for s in ("Left","Right")})
    generated.update(MidpointBounds=render_midpoint()[0],Fourth=render_fourth()[0],Assembly=render_assembly())
    integral,value,_ = render_integral()
    generated.update(Integral=integral,ValueRight=value)
    for name,text in generated.items():
        assert read("C1RouteANeighbor"+name+"2557") == text,name
    from generate_boundary_fourth_2550 import render as old_fourth
    from generate_cell_integral_2546 import render as old_integral
    from generate_adaptive_nodes_2542 import render as old_node
    assert old_fourth()[0] == read("C1RouteABoundaryFourth2550")
    assert old_integral()[0] == read("C1RouteACellIntegral2546")
    for index in (5440,10239):
        for sign in (1,-1):
            name = f"N{index:05d}{'Plus' if sign > 0 else 'Minus'}"
            assert old_node(index,sign)[0] == read("C1RouteAAdaptive"+name+"2542")
    result.update(regeneration=True,default_regressions=6)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:|declaration uses 'sorry'|warning: .*255[67]\.lean",log,re.M)
        paths = sorted((ROOT/"ConnesWeilRH/Dev").glob("C1RouteANeighbor*2557.lean"))
        expected = set()
        for path in paths:
            expected.update(re.findall(r"#print axioms ConnesWeilRH.Dev.(\w+)",path.read_text()))
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+2557)' depends on axioms:\s*\[([^]]*)\]",log)
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
        result.update(status="NEIGHBOR_SEGMENT_BUILD_AXIOM_SOURCE_PASS",audits=audits,
            source_sha256=hashes,build_footer=footers[-1],
            build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
            conditional_segment_upper="225/1000000000000")
    (ROOT/"results/2557_neighbor_numeric_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
