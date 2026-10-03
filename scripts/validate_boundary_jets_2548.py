"""Independently check support branches and all cell-2700 derivative traces."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from generate_boundary_jets_2548 import CASES, render
from validate_boundary_replay_2547 import check as check_interior
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def


def check(source,side):
    grid,order = CASES[side]
    x = scalar_def(source,f"edge{side}Position2548")
    assert x == -Q(65536001,10**7)+grid*Q(65536001,51200000000)
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    active,exterior = [],[]
    for i,values in enumerate(raw):
        width = Q.from_float(float.fromhex(values[0]))
        p = f"edge{side}P{i:03d}"
        if abs(x) < width**2:
            check_interior(source,prefix=p,record=2548,family_index=i,grid_indices=(grid,),
                           order=order,position_name=f"edge{side}Position2548")
            assert p+"Exterior2548" not in source
            active.append(i)
        else:
            assert value(source,p+"Center2548") == (0,0)
            assert value(source,p+"Factor2548") == (0,0)
            assert scalar_def(source,p+"Error2548") == 0
            assert f"theorem {p}Exterior2548 (n : ℕ)" in source
            assert p+"Input2548" not in source
            exterior.append(i)
    assert len(active)+len(exterior) == 30
    return dict(side=side,order=order,grid=str(grid),active=active,exterior=exterior)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    reports = []
    for side in CASES:
        source = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}2548.lean").read_text()
        report = check(source,side)
        assert source == render(side)[0]
        p = f"edge{side}P{report['active'][0]:03d}"
        mutated = re.sub(r"(def "+p+r"Factor2548\b.*?:=).*?(?=\n\n)",
                         r"\1 (0, 0)",source,count=1,flags=re.S)
        assert mutated != source
        try:
            check(mutated,side)
        except AssertionError:
            pass
        else:
            raise AssertionError("Zeroed interior factor accepted")
        report["corrupt_factor_rejected"] = True
        reports.append(report)
    result = dict(record=2548,cases=reports,scope="cell2700 endpoint order3 and midpoint order2; sigma+1/2",
                  whole_cell_certificate=False,full_grid_certificate=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2548\.lean:",log,re.M)
        expected = {f"edge{s}P{i:03d}DerivativeError2548" for s in CASES for i in range(30)}
        expected |= {f"edge{s}Grid2548" for s in CASES}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2548)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending = ["ConnesWeilRH"]+[f"ConnesWeilRH.Dev.C1RouteABoundary{s}2548" for s in CASES]
        hashes = {}
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
        result.update(status="BUILD_AXIOM_SOURCE_BOUNDARY_JETS_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2548_boundary_jets_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_JETS_READBACK_PASS",[(r["side"],len(r["active"])) for r in reports],flush=True)
