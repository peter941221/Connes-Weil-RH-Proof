"""Exact endpoint norm and signed midpoint readback for the boundary cell."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_complex_exp_node_2541 import ROOT
from generate_boundary_bounds_2549 import render_norm,render_midpoint
from validate_endpoint_thirds_2544 import check_norms
from validate_midpoint_derivatives_2543 import check_signed


def normalize_norm(source,side):
    source = re.sub(r":\s*([ℝℚ])",r": \1",source)
    return re.sub(r"\bedge"+side+r"(\w*)254[89]\b",lambda m:"endpoint"+side+m[1]+"2544",source)


def normalize_mid(source):
    source = re.sub(r":\s*([ℝℚ])",r": \1",source)
    source = re.sub(r"\bedgeMidpoint(\w*)254[89]\b",lambda m:"midpoint"+m[1]+"2543",source)
    return re.sub(r"\bedgeSignedMidpoint(\w*)2549\b",lambda m:"signedMidpoint"+m[1]+"2543",source)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",type=Path)
    parser.add_argument("--mirror",type=Path)
    args = parser.parse_args()
    reports = []
    for side in ("Left","Right"):
        source = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}Bounds2549.lean").read_text()
        base = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}2548.lean").read_text()
        assert source == render_norm(side)
        bounds = check_norms(normalize_norm(source,side),normalize_norm(base,side),side)
        # Family1 is interior at both endpoints; its positive upper cannot
        # be replaced by zero, unlike a legitimately exterior family.
        normalized = normalize_norm(source,side)
        corrupted = re.sub(r"(noncomputable def endpoint"+side+r"P001NormUpper2544\b.*?:=).*?(?=\n\n)",
                           r"\1 (0 : ℝ)",normalized,count=1,flags=re.S)
        assert corrupted != normalized
        try:
            check_norms(corrupted,normalize_norm(base,side),side)
        except AssertionError:
            pass
        else:
            raise AssertionError("Zeroed interior norm accepted")
        reports.append(dict(side=side,families_checked=len(bounds),corrupted_norm_rejected=True))
    source = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryMidpointBounds2549.lean").read_text()
    base = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryMidpoint2548.lean").read_text()
    assert source == render_midpoint()[0]
    signed = check_signed(normalize_mid(source),normalize_mid(base))
    normalized = normalize_mid(source)
    corrupted = re.sub(r"(noncomputable def midpointP001Radius2543\b.*?:=).*?(?=\n\n)",
                       r"\1 (0 : ℝ)",normalized,count=1,flags=re.S)
    assert corrupted != normalized
    try:
        check_signed(corrupted,normalize_mid(base))
    except AssertionError:
        pass
    else:
        raise AssertionError("Zeroed midpoint radius accepted")
    result = dict(record=2549,endpoints=reports,signed=signed,zeroed_radius_rejected=True,
                  whole_cell_certificate=False,full_grid_certificate=False,rh_claim=False)
    if args.log:
        assert args.mirror
        log = args.log.read_text()
        footers = re.findall(r"^Build completed successfully.*$",log,re.M)
        assert footers and not re.search(r"^error:",log,re.M)
        assert not re.search(r"^warning: .*2549\.lean:",log,re.M)
        expected = {f"edge{s}P{i:03d}NormBound2549" for s in ("Left","Right") for i in range(30)}
        expected |= {"edgeSignedMidpointExpError2549","edgeSignedMidpointSum_eq2549",
                     "edgeSignedMidpointCharge2549","edgeSignedMidpointUpper_le2549",
                     "weightedPhysical_edge_midpoint_le2549"}
        matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+2549)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert set(audits) == expected
        assert all(v == ["propext","Classical.choice","Quot.sound"] for v in audits.values())
        pending = ["ConnesWeilRH"]+[f"ConnesWeilRH.Dev.C1RouteABoundary{s}Bounds2549" for s in ("Left","Right","Midpoint")]
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
        result.update(status="BUILD_AXIOM_SOURCE_BOUNDARY_BOUNDS_PASS",build_footer=footers[-1],
                      audits=audits,project_sources_checked=len(hashes),source_sha256=hashes,
                      build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest())
    (ROOT/"results/2549_boundary_bounds_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("BOUNDARY_BOUNDS_READBACK_PASS",signed["signed_upper"],flush=True)
