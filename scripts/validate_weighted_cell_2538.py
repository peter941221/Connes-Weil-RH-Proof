"""Verify weighted-family build, audit coverage and source identity."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["ConnesWeilRH.Dev.C1RouteAWeightedFamilyLocal2537Audit",
           "ConnesWeilRH.Dev.C1RouteAWeightedFamilyCell2538Audit", "ConnesWeilRH"]
EXPECTED = {
    "weightedExternalFamily_eq2537",
    "weightedExternalFamily_iteratedDeriv2537",
    "weightedExternalFamily_iteratedDeriv_le_local2537",
    "weightedExternalFamily_iteratedDeriv_le_cell2538",
    "weightedExternalFamily_iteratedDeriv_zero_outside2538",
    "weightedExternalFamily_third_le_endpoints2538",
    "weightedExternalFamily_third_le_cell2538",
    "weightedFamilyCellUpper_four2538",
    "weightedExternalFamily_third_le_coefficient_ball2538",
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT/"results/2538_weighted_cell_validation.json")
    args = parser.parse_args()
    text = args.log.read_text(encoding="utf-8")
    footers = re.findall(r"^Build completed successfully.*$", text, re.M)
    assert footers and not re.search(r"^error:", text, re.M)
    matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+253[78])' depends on axioms:\s*\[([^]]*)\]", text)
    assert len(matches) == len(EXPECTED) and {name for name, _ in matches} == EXPECTED
    reports = {name: [part.strip() for part in axioms.split(",")] for name, axioms in matches}
    assert all(axioms == ["propext", "Classical.choice", "Quot.sound"] for axioms in reports.values())
    pending, hashes, mismatches = MODULES[:], {}, []
    while pending:
        name = pending.pop()
        path = name.replace(".", "/")+".lean"
        if path in hashes:
            continue
        source = (ROOT/path).read_bytes()
        mirror_path = args.mirror/path
        if not mirror_path.exists() or source != mirror_path.read_bytes():
            mismatches.append(path)
        hashes[path] = hashlib.sha256(source).hexdigest()
        for line in source.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(item for item in line[7:].split()
                               if item.startswith("ConnesWeilRH.") or item == "ConnesWeilRH")
    assert not mismatches, mismatches
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(), name
    result = dict(record=2538, status="BUILD_AXIOM_SOURCE_IDENTITY_PASS", build_footer=footers[-1],
                  audits=reports, project_sources_checked=len(hashes), source_sha256=hashes,
                  build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  scope="weighted-family derivatives and explicit whole-cell third bound; numeric import open",
                  lean_numeric_certificate=False, exact_owner_transfer=False,
                  producer_go=False, rh_claim=False)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["status"], len(reports), len(hashes), flush=True)


if __name__ == "__main__":
    main()
