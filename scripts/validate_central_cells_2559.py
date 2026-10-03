"""Independent readback for four zero-touching signed production cells."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

from generate_central_cells_2559 import CASES,render_segment
from generate_signed_cells_2558 import ROOT,read,render_endpoint,render_value
from validate_signed_cells_2558 import check
from validate_adaptive_nodes_2542 import scalar_def
from price_boundary_precision_2547 import precision_exponential
from routea_exp_schedule_probe_2542 import evaluate


def reject_zero(cell,source):
    corrupted = re.sub(r"(noncomputable def "+cell.prefix+r"CellIntegralUpper2559\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",source,count=1,flags=re.S)
    assert corrupted != source
    try:
        check(cell,corrupted)
    except AssertionError:
        return
    raise AssertionError("Zeroed central integral accepted")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    parser.add_argument("--cost-log",type=Path)
    args = parser.parse_args()
    reports = []
    for cell in CASES:
        source = read(cell.module("Integral"))
        report = check(cell,source)
        assert all(len(jet["active"]) == 30 for jet in report["jets"])
        reject_zero(cell,source)
        expected = {"Midpoint":cell.render_midpoint(),"MidpointBounds":cell.render_midpoint_bounds()[0],
            "Fourth":cell.render_fourth(),"Assembly":cell.render_assembly(),"Integral":cell.render_integral()[0]}
        expected.update({side+"Bounds":cell.render_norm(side) for side in ("Left","Right")})
        for name,text in expected.items():
            assert read(cell.module(name)) == text,cell.module(name)
        # All family fourth exponents use near=0 in these cells. On the
        # decaying side the maximum growth is exactly zero, not negative.
        fourth = read(cell.module("Fourth"))
        growth = Q(65536001,102400000000) if (cell.index == 5120) == (cell.sign > 0) else Q(0)
        for i in range(30):
            assert scalar_def(fourth,cell.prefix+f"FourthP{i:03d}Exponent2559") == growth-30
        report.update(zeroed_integral_rejected=True,regeneration=True,near_zero=True,
                      exact_fourth_growth=str(growth))
        reports.append(report)
        print(cell.index,cell.sign,report["integral"],flush=True)
    for sign in (1,-1):
        for index in (5119,5120,5121):
            for module,text in (render_endpoint(index,sign,2559),render_value(index,sign,2559)[:2]):
                assert read(module) == text,module
    # The extracted exponent evaluator retains the old 100-bit arithmetic,
    # including center and error, for nonzero and zero evaluation positions.
    controls = []
    for x in (Q(-1,4),Q(0),Q(1,4)):
        for sigma in (Q(-1,2),Q(1,2)):
            exponent = sigma*x-30/(1-x*x),3*x
            old = evaluate(Q(1),Q(3),x,sigma)
            assert precision_exponential(exponent,100) == (old["center"],old["error"],old["depth"])
            controls.append(dict(position=str(x),sigma=str(sigma)))
    totals = {str(sign):str(sum(Q(row["integral"]) for row in reports if row["sign"] == sign))
              for sign in (1,-1)}
    result = dict(record=2559,cells=reports,exponent_controls=controls,sign_totals=totals,
        both_signs_total=str(sum(Q(v) for v in totals.values())),full_grid_certificate=False,
        exact_coefficient_membership=False,rh_claim=False)
    if args.log:
        assert args.mirror
        assert read("C1RouteACentralSegment2559") == render_segment()
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:|declaration uses 'sorry'|warning: .*2559\.lean",log,re.M)
        paths = sorted((ROOT/"ConnesWeilRH/Dev").glob("C1RouteA*2559.lean"))
        expected = set()
        for path in paths:
            expected.update(re.findall(r"#print axioms ConnesWeilRH.Dev.(\w+)",path.read_text()))
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+2559)' depends on axioms:\s*\[([^]]*)\]",log)
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
        result.update(status="CENTRAL_BOTH_SIGNS_BUILD_AXIOM_SOURCE_PASS",audits=audits,
            source_sha256=hashes,build_footer=footers[-1],
            build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    if args.cost_log:
        cost = args.cost_log.read_text()
        assert len(re.findall(r"^Build completed successfully",cost,re.M)) == 4
        rows = re.findall(r"CENTRAL_CELL index=(\d+) sign=(Plus|Minus) elapsed=([\d.]+) user=([\d.]+) system=([\d.]+) peak_kib=(\d+)",cost)
        assert len(rows) == 4
        result.update(cell_build_costs=[dict(zip(("index","sign","elapsed","user","system","peak_kib"),row)) for row in rows],
                      cost_log_sha256=hashlib.sha256(args.cost_log.read_bytes()).hexdigest())
    (ROOT/"results/2559_central_cell_readback.json").write_text(json.dumps(result,indent=2)+"\n")
