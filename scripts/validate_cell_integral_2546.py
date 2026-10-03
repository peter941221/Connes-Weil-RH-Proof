"""Independent exact readback of the cell integral assembly and right node."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT
from validate_adaptive_nodes_2542 import scalar_def, check as check_node
from validate_fourth_envelope_2545 import check as check_fourth
from validate_endpoint_thirds_2544 import check_norms


def check(source,right):
    node = check_node(right,5441,1)
    fourth = (ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean").read_text()
    assert len(check_fourth(fourth)) == 30
    sides = []
    for side in ("Left","Right"):
        base = (ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Third2544.lean").read_text()
        norms = (ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Norms2544.lean").read_text()
        sides.append(check_norms(norms,base,side))
    coefficients = json.loads((ROOT/"results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    h = Q(65536001,51200000000)
    total = Q(0)
    for i,row in enumerate(coefficients):
        magnitude = sum(abs((Q(row["ideal_base_coefficient"][p]["lower_exact"])+
                            Q(row["ideal_base_coefficient"][p]["upper_exact"]))/2)
                        for p in ("real","imag"))+Q(1,10**30)
        term = max(sides[0][i],sides[1][i])+h/2*scalar_def(fourth,f"fourthP{i:03d}Upper2545")
        upper = scalar_def(source,f"cellP{i:03d}Charge2546")
        assert upper >= magnitude*term
        total += upper
    third = scalar_def(source,"cellThirdUpper2546")
    assert third >= total
    curvature = scalar_def(source,"cellCurvatureUpper2546")
    assert curvature >= Q(997840737,400000)+third*h/2
    upper = scalar_def(source,"cellIntegralUpper2546")
    right_upper = scalar_def(right,"adaptiveN05441PlusUpper2542")
    assert upper >= h/2*(Q(721605217,1250000000)+right_upper)+curvature*h**3/12
    return dict(right_node=node,third_upper=str(third),curvature_upper=str(curvature),
                integral_upper=str(upper),integral_upper_display=float(upper))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    from generate_cell_integral_2546 import render
    path = ROOT/"ConnesWeilRH/Dev/C1RouteACellIntegral2546.lean"
    source = path.read_text()
    right = (ROOT/"ConnesWeilRH/Dev/C1RouteACellRight2546.lean").read_text()
    result = check(source,right)
    regenerated,regenerated_right,_ = render()
    assert source == regenerated and right == regenerated_right
    corrupted = re.sub(r"(noncomputable def cellIntegralUpper2546\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(corrupted,right)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zero integral upper accepted")
    result.update(record=2546,scope="one cell, sigma +1/2, conditional on coefficient balls",
                  zeroed_integral_rejected=True,full_grid_certificate=False,
                  exact_owner_membership=False,producer_go=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2546\.lean:",log,re.M)
        expected = {"cellChargeBound2546","cellThirdBound2546","cellCurvatureBound2546",
                    "cellIntegralBound2546","adaptiveN05441PlusSigned_le2542",
                    "adaptiveN05441PlusPhysical_le2542"}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in axioms.split(",")] for name,axioms in matches if name in expected}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteACellIntegral2546"],{}
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
        result.update(status="BUILD_AXIOM_SOURCE_CELL_INTEGRAL_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                      conditional_whole_cell_certificate=True)
    (ROOT/"results/2546_cell_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("CELL_INTEGRAL_READBACK_PASS",result["integral_upper"],flush=True)
