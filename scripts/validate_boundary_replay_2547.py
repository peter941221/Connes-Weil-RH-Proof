"""Independent 160-bit endpoint trace and exponent-derivative readback."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def
from validate_nonzero_node_2541 import multiply


def check(source, *, prefix="boundary", record=2547, family_index=None,
          grid_indices=(2700,2701), order=3, position_name="boundaryPosition2547"):
    i = family_index if family_index is not None else int(re.search(
        r"weightedUnitJet2539 3 \(1/2\) nodeModulation2541 ⟨(\d+),",source)[1])
    name = lambda suffix: prefix+suffix+str(record)
    depth = int(re.search(r"compactExp2547\s+"+name("Input")+r"\s+(\d+)",source)[1])
    x = scalar_def(source,position_name)
    assert x in (-Q(65536001,10**7)+j*Q(65536001,51200000000) for j in grid_indices)
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"][i]
    width,theta = (Q.from_float(float.fromhex(v)) for v in raw)
    r = width**2
    assert abs(x) < r
    q = 1-(x/r)**2
    a = Q(1,2)-60*x/(r**2*q**2),theta
    b = -60/(r**2*q**2)-240*x**2/(r**4*q**3)
    c = -720*x/(r**4*q**3)-1440*x**3/(r**6*q**4)
    square = multiply(a,a)
    if order == 3:
        cube = multiply(square,a)
        factor = cube[0]+3*a[0]*b+c,cube[1]+3*a[1]*b
    else:
        assert order == 2
        factor = square[0]+b,square[1]
    assert value(source,name("Factor")) == factor
    z = value(source,name("Input"))
    assert z == ((x/2-30/q)/2**depth,theta*x/2**depth)
    assert sum(abs(v) for v in z) <= 1
    center,error = (Q(1),Q(0)),Q(1,10**18)+19*Q(1,2**159)
    def down(v):
        t = v*2**160
        return Q(t.numerator//t.denominator,2**160)
    for j in range(19,0,-1):
        product = multiply(z,center)
        center = down(1+product[0]/j),down(product[1]/j)
    for _ in range(depth):
        t = (error*(2*sum(abs(v) for v in center)+error)+Q(1,2**159))*2**200
        error = Q(-((-t.numerator)//t.denominator),2**200)
        center = tuple(down(v) for v in multiply(center,center))
    assert value(source,name("Center")) == center
    assert scalar_def(source,name("Error")) == error
    return dict(family=i,position=str(x),depth=depth,error=str(error),
                derivative_error_display=float(sum(abs(v) for v in factor)*error))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    from generate_boundary_replay_2547 import render
    from generate_compact_exp160_2547 import render as render_engine
    path = ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryReplay2547.lean"
    source = path.read_text()
    result = check(source)
    assert source == render()[0]
    assert (ROOT/"ConnesWeilRH/Dev/C1RouteACompactExp1602547.lean").read_text() == render_engine()
    corrupted = re.sub(r"(noncomputable def boundaryError2547\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(corrupted)
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed boundary error accepted")
    result.update(record=2547,zeroed_error_rejected=True,whole_cell_certificate=False,
                  full_grid_certificate=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2547\.lean:",log,re.M)
        expected = {"embedPair_round_error2547","hornerRat_error2547","squareState_error2547",
                    "compactExp_error2547","boundaryBaseError2547","boundaryThirdError2547"}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2547)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteABoundaryReplay2547"],{}
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
        result.update(status="BUILD_AXIOM_SOURCE_BOUNDARY_DERIVATIVE_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2547_boundary_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_REPLAY_READBACK_PASS",result["family"],result["derivative_error_display"],flush=True)
