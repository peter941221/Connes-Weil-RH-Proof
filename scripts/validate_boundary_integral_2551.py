"""Independent exact checks for the first support-crossing cell integral."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT
from validate_adaptive_nodes_2542 import scalar_def,check as check_node
from validate_boundary_fourth_2550 import check as check_fourth
from validate_boundary_bounds_2549 import normalize_norm,normalize_mid
from validate_endpoint_thirds_2544 import check_norms
from validate_midpoint_derivatives_2543 import check_signed


def read(name):
    return (ROOT/f"ConnesWeilRH/Dev/{name}.lean").read_text()


def check(source,left_node,right_node):
    source = re.sub(r":\s*([ℝℚ])",r": \1",source)
    left_case,right_case = check_node(left_node,2700,1),check_node(right_node,2701,1)
    fourth = read("C1RouteABoundaryFourth2550")
    assert len(check_fourth(fourth)) == 30
    fourth = re.sub(r":\s*([ℝℚ])",r": \1",fourth)
    sides = []
    for side in ("Left","Right"):
        sides.append(check_norms(normalize_norm(read(f"C1RouteABoundary{side}Bounds2549"),side),
                                 normalize_norm(read(f"C1RouteABoundary{side}2548"),side),side))
    midpoint = check_signed(normalize_mid(read("C1RouteABoundaryMidpointBounds2549")),
                            normalize_mid(read("C1RouteABoundaryMidpoint2548")))
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    h,total = Q(65536001,51200000000),Q(0)
    for i,row in enumerate(coefficients):
        cm = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                      Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                 for p in ("real","imag"))+Q(1,10**30)
        term = max(sides[0][i],sides[1][i])+h/2*scalar_def(fourth,f"edgeFourthP{i:03d}Upper2550")
        upper = scalar_def(source,f"boundaryCellP{i:03d}Charge2551")
        assert upper >= cm*term
        total += upper
    third = scalar_def(source,"boundaryCellThirdUpper2551")
    curvature = scalar_def(source,"boundaryCellCurvatureUpper2551")
    integral = scalar_def(source,"boundaryCellIntegralUpper2551")
    assert third >= total
    assert curvature >= Q(midpoint["signed_upper"])+third*h/2
    endpoint_sum = scalar_def(left_node,"adaptiveN02700PlusUpper2542")+scalar_def(right_node,"adaptiveN02701PlusUpper2542")
    assert integral >= endpoint_sum*h/2+curvature*h**3/12
    return dict(left_node=left_case,right_node=right_case,third=str(third),curvature=str(curvature),
                integral=str(integral),integral_display=float(integral))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    from generate_boundary_integral_2551 import render
    source,left,right = (read("C1RouteABoundary"+name+"2551") for name in ("Integral","ValueLeft","ValueRight"))
    result = check(source,left,right)
    regen = render()
    assert (source,left,right) == regen[:3]
    mutated = re.sub(r"(noncomputable def boundaryCellIntegralUpper2551\b.*?:=).*?(?=\n\n)",
                     r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert mutated != source
    try:
        check(mutated,left,right)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed boundary integral upper accepted")
    result.update(record=2551,scope="cell2700 sigma+1/2, coefficient-ball membership retained",
                  zeroed_integral_rejected=True,full_grid_certificate=False,
                  exact_coefficient_membership=False,producer_go=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2551\.lean:",log,re.M)
        expected = {f"boundaryCell{x}Bound2551" for x in ("Charge","Third","Curvature","Integral")}
        expected |= {f"adaptiveN{index:05d}Plus{kind}_le2542" for index in (2700,2701) for kind in ("Signed","Physical")}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches if name in expected}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteABoundaryIntegral2551"],{}
        while pending:
            relative = pending.pop().replace(".","/")+".lean"
            if relative in hashes:
                continue
            data = (ROOT/relative).read_bytes()
            assert data == (args.mirror/relative).read_bytes(),relative
            hashes[relative] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(v for v in line[7:].split() if v.startswith("ConnesWeilRH"))
        for name in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
            assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(),name
        result.update(status="BUILD_AXIOM_SOURCE_BOUNDARY_INTEGRAL_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                      conditional_whole_cell_certificate=True)
    (ROOT/"results/2551_boundary_integral_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_INTEGRAL_READBACK_PASS",result["integral"],flush=True)
