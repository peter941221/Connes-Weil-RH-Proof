"""Independent rational replay and derivative-polynomial recurrence checks."""
from fractions import Fraction as Q
from math import comb
import argparse
from pathlib import Path
import hashlib
import json
import re

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def
from validate_nonzero_node_2541 import multiply


def bump_polynomials():
    rows = [{0: Q(1)}]
    for k in range(4):
        out = {}
        def put(j, v):
            out[j] = out.get(j,Q(0))+v
        for j,c in rows[-1].items():
            if j:
                for shift,factor in ((0,1),(2,-2),(4,1)):
                    put(j-1+shift,j*c*factor)
            put(j+1,4*k*c-60*c)
            put(j+3,-4*k*c)
        rows.append({j:c for j,c in out.items() if c})
    return rows


def check(source):
    names = re.findall(r"def (fourthP\d{3})Input2545",source)
    assert names == [f"fourthP{i:03d}" for i in range(len(names))] and names
    families = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    a = Q(65536001,160000000)
    b = a+Q(65536001,51200000000)
    polynomials = bump_polynomials()
    rows = []
    for i,p in enumerate(names):
        width,theta = (Q.from_float(float.fromhex(v)) for v in families[i])
        radius = width**2
        near,far = a/radius,b/radius
        assert 0 < near < far < 1
        depth = int(re.search(r"compactExp2542\s+"+p+r"Input2545\s+(\d+)",source)[1])
        z = value(source,p+"Input2545")
        assert z == ((b/2-30/(1-near**2))/2**depth,0)
        assert scalar_def(source,p+"Exponent2545") == b/2-30/(1-near**2)
        assert sum(abs(v) for v in z) <= 1
        center,error = (Q(1),Q(0)),Q(1,10**18)+19*Q(1,2**99)
        def down(v):
            scaled = v*2**100
            return Q(scaled.numerator//scaled.denominator,2**100)
        for denominator in range(19,0,-1):
            product = multiply(z,center)
            center = down(1+product[0]/denominator),down(product[1]/denominator)
        for _ in range(depth):
            scaled = (error*(2*sum(abs(v) for v in center)+error)+Q(1,2**99))*2**140
            error = Q(-((-scaled.numerator)//scaled.denominator),2**140)
            center = tuple(down(v) for v in multiply(center,center))
        assert center == value(source,p+"Center2545")
        assert error == scalar_def(source,p+"Error2545")
        exponential = scalar_def(source,p+"ExpUpper2545")
        assert exponential >= sum(abs(v) for v in center)+error
        frequency = scalar_def(source,p+"Frequency2545")
        assert frequency >= 0 and frequency**2 >= Q(1,4)+theta**2
        poly = sum(comb(4,j)*frequency**j *
                   sum(abs(c)*far**power for power,c in polynomials[4-j].items()) /
                   ((1-near**2)**(2*(4-j))*radius**(4-j)) for j in range(5))
        upper = scalar_def(source,p+"Upper2545")
        assert upper >= exponential*poly
        rows.append(dict(index=i,upper=str(upper),upper_display=float(upper)))
    return rows


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    from generate_fourth_envelope_2545 import render
    path = ROOT/"ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean"
    source = path.read_text()
    rows = check(source)
    assert source == render(len(rows))[0]
    corrupted = re.sub(r"(noncomputable def fourthP000Upper2545\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed fourth envelope accepted")
    result = dict(record=2545,scope="exact arithmetic; Lean acceptance separate",
                  families_checked=len(rows),rows=rows,zeroed_upper_rejected=True,
                  polynomial_method="differentiate exp(-30/(1-u^2)) by rational recurrence",
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  whole_cell_certificate=False,full_grid_certificate=False,rh_claim=False)
    if args.log:
        assert args.mirror and len(rows) == 30
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2545\.lean:",log,re.M)
        expected = {f"fourthP{i:03d}Bound2545" for i in range(30)} | {
            "fourthBound2545", "weightedCell_factor2545", "cellPolynomial_mono2545",
            "weightedCell_upper2545"}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2545)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in axioms.split(",")] for name,axioms in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteAFourthEnvelope2545"],{}
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
        result.update(status="BUILD_AXIOM_SOURCE_FOURTH_ENVELOPE_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2545_fourth_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("FOURTH_ENVELOPE_READBACK_PASS",len(rows),flush=True)
