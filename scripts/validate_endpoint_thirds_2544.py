"""Independently check endpoint third factors as a^3+3ab+c."""
import hashlib
import argparse
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT
from generate_endpoint_thirds_2544 import render
from validate_midpoint_derivatives_2543 import check
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def
from validate_nonzero_node_2541 import multiply


def check_norms(source,base,side):
    bounds = []
    for i in range(30):
        p = f"endpoint{side}P{i:03d}"
        factor = value(base,p+"Factor2544")
        center = value(base,p+"Center2544")
        error = scalar_def(base,p+"Error2544")
        upper = scalar_def(source,p+"NormUpper2544")
        remainder = upper-sum(abs(v) for v in factor)*error
        product = multiply(factor,center)
        assert remainder >= 0 and remainder**2 >= sum(v*v for v in product)
        bounds.append(upper)
    return bounds


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    parser.add_argument("--norms",action="store_true")
    args = parser.parse_args()
    reports = []
    for side,index in (("Left",5440),("Right",5441)):
        path = ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Third2544.lean"
        if not path.exists():
            continue
        source = path.read_text()
        kwargs = dict(prefix="endpoint"+side,record=2544,order=3,grid_position=index)
        count = check(source,**kwargs)
        assert source == render(side,count)
        corrupted = re.sub(r"(def endpoint"+side+r"P000Factor2544\b.*?:=).*?(?=\n\n)",
                           r"\1 (0, 0)",source,count=1,flags=re.S)
        assert corrupted != source
        try:
            check(corrupted,**kwargs)
        except AssertionError:
            pass
        else:
            raise AssertionError("Corrupted third factor accepted")
        reports.append(dict(side=side,index=index,families_checked=count,corrupted_factor_rejected=True,
                            source_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
        if args.norms:
            from generate_endpoint_norms_2544 import render as render_norms
            norm_path = ROOT/f"ConnesWeilRH/Dev/C1RouteAEndpoint{side}Norms2544.lean"
            norm_source = norm_path.read_text()
            assert count == 30 and norm_source == render_norms(side,30)
            bounds = check_norms(norm_source,source,side)
            corrupted = re.sub(r"(noncomputable def endpoint"+side+r"P000NormUpper2544\b.*?:=).*?(?=\n\n)",
                               r"\1 (0 : ℝ)",norm_source,count=1,flags=re.S)
            assert corrupted != norm_source
            try:
                check_norms(corrupted,source,side)
            except AssertionError:
                pass
            else:
                raise AssertionError("Zeroed endpoint norm bound accepted")
            reports[-1].update(norm_source_sha256=hashlib.sha256(norm_path.read_bytes()).hexdigest(),
                               zeroed_norm_rejected=True,maximum_unit_norm_upper=str(max(bounds)))
    assert reports
    result = dict(record=2544,scope="exact endpoint arithmetic; Lean acceptance separate",cases=reports,
                  independent_factor_method="exponent derivatives a^3+3ab+c",
                  whole_cell_certificate=False,full_grid_certificate=False,producer_go=False,rh_claim=False)
    if args.log:
        assert args.mirror and args.norms and len(reports) == 2
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2544\.lean:",log,re.M)
        expected = {f"endpoint{side}P{i:03d}{kind}2544"
                    for side in ("Left","Right") for i in range(30)
                    for kind in ("DerivativeError","NormBound")}
        expected.update({f"endpoint{side}{kind}2544" for side in ("Left","Right")
                         for kind in ("NormBound","_grid")})
        expected.update({"thirdCellTerm_bounds2544", "thirdAggregate_bounds2544",
                         "curvature_after_endpoints2544"})
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2544)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in axioms.split(",")] for name,axioms in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending,hashes = ["ConnesWeilRH","ConnesWeilRH.Dev.C1RouteAEndpointThirds2544Audit",
                          "ConnesWeilRH.Dev.C1RouteAThirdCellEndpointAssembly2544"],{}
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
        result.update(status="BUILD_AXIOM_SOURCE_ENDPOINT_IDENTITY_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2544_endpoint_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("ENDPOINT_THIRD_READBACK_PASS",[(r["side"],r["families_checked"]) for r in reports],flush=True)
