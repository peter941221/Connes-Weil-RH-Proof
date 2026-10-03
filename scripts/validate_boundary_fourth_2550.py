"""Independent geometry, polynomial and 160-bit fourth-envelope readback."""
import argparse
from fractions import Fraction as Q
from math import comb
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT,CAPTURE
from validate_fourth_envelope_2545 import bump_polynomials
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def
from validate_nonzero_node_2541 import multiply


def check(source, *, cell_index=2700, sigma=Q(1,2)):
    assert sigma in (Q(1,2),Q(-1,2))
    source = re.sub(r":\s*([ℝℚ])",r": \1",source)
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    a = -Q(65536001,10**7)+cell_index*Q(65536001,51200000000)
    b = a+Q(65536001,51200000000)
    rows = []
    polys = bump_polynomials()
    for i,values in enumerate(raw):
        width,theta = (Q.from_float(float.fromhex(v)) for v in values)
        radius = width**2
        near,far = min(abs(a),abs(b))/radius,min(max(abs(a),abs(b)),radius)/radius
        p = f"edgeFourthP{i:03d}"
        upper = scalar_def(source,p+"Upper2550")
        if near >= 1:
            assert upper == 0 and p+"Input2550" not in source
            rows.append(dict(family=i,exterior=True))
            continue
        depth = int(re.search(r"compactExp2547\s+"+p+r"Input2550\s+(\d+)",source)[1])
        z = value(source,p+"Input2550")
        exponent = max(sigma*a,sigma*b)-30/(1-near**2)
        assert z == (exponent/2**depth,0) and sum(abs(v) for v in z) <= 1
        assert scalar_def(source,p+"Exponent2550") == exponent
        center,error = (Q(1),Q(0)),Q(1,10**18)+19*Q(1,2**159)
        def down(v):
            scaled = v*2**160
            return Q(scaled.numerator//scaled.denominator,2**160)
        for j in range(19,0,-1):
            prod = multiply(z,center)
            center = down(1+prod[0]/j),down(prod[1]/j)
        for _ in range(depth):
            scaled = (error*(2*sum(abs(v) for v in center)+error)+Q(1,2**159))*2**200
            error = Q(-((-scaled.numerator)//scaled.denominator),2**200)
            center = tuple(down(v) for v in multiply(center,center))
        assert center == value(source,p+"Center2550") and error == scalar_def(source,p+"Error2550")
        expupper = scalar_def(source,p+"ExpUpper2550")
        assert expupper >= sum(abs(v) for v in center)+error
        frequency = scalar_def(source,p+"Frequency2550")
        assert frequency >= 0 and frequency**2 >= Q(1,4)+theta**2
        poly = sum(comb(4,j)*frequency**j*sum(abs(c)*far**power for power,c in polys[4-j].items()) /
                   ((1-near**2)**(2*(4-j))*radius**(4-j)) for j in range(5))
        assert upper >= expupper*poly
        rows.append(dict(family=i,exterior=False,crossing=far==1,upper=str(upper)))
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    from generate_boundary_fourth_2550 import render
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryFourth2550.lean").read_text()
    rows = check(source)
    assert source == render()[0]
    corrupted = re.sub(r"(noncomputable def edgeFourthP015Upper2550\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed crossing envelope accepted")
    result = dict(record=2550,rows=rows,corrupted_crossing_upper_rejected=True,
                  whole_cell_certificate=False,full_grid_certificate=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2550\.lean:",log,re.M)
        expected = {f"edgeFourthP{i:03d}Bound2550" for i in range(30)} | {"edgeFourthBound2550"}
        expected |= {"edgeThirdCell_bound2550","edgeThirdAggregate_bound2550","edgeCurvature_bound2550"}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2550)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteABoundaryAssembly2550"],{}
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
        result.update(status="BUILD_AXIOM_SOURCE_CROSSING_FOURTH_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2550_boundary_fourth_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("CROSSING_FOURTH_READBACK_PASS",len(rows),flush=True)
