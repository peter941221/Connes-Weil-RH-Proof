"""Check the signed aggregate build, eight axiom leaves and source identity."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539Audit", "ConnesWeilRH"]
EXPECTED = {
    "weightedPhysical2539_iteratedDeriv",
    "weightedPhysical2539_jet_le_center_error",
    "weightedPhysical2539_third_le_cell",
    "weightedPhysical2539_second_le_signed_midpoint",
    "weightedPhysical2539_norm_integral_le_signed_cell",
    "weightedPhysical2539_norm_integral_le_signed_composite",
    "externalPhysical2344_strip_eq_interval2539",
    "externalPhysical2344_strip_le_signed_10240_2539",
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT/"results/2539_signed_aggregate_validation.json")
    args = parser.parse_args()
    text = args.log.read_text(encoding="utf-8")
    footers = re.findall(r"^Build completed successfully.*$", text, re.M)
    assert footers and not re.search(r"^error:", text, re.M)
    matches = re.findall(r"'ConnesWeilRH\.Dev\.([A-Za-z0-9_]+)' depends on axioms:\s*\[([^]]*)\]", text)
    matches = [(name, axioms) for name, axioms in matches if "2539" in name]
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
    result = dict(record=2539, status="BUILD_AXIOM_SOURCE_IDENTITY_PASS", build_footer=footers[-1],
                  audits=reports, project_sources_checked=len(hashes), source_sha256=hashes,
                  build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  scope="signed aggregate analytic cell and full-strip bounds; coefficient membership and numeric evaluations open",
                  lean_numeric_certificate=False, exact_owner_transfer=False,
                  producer_go=False, rh_claim=False)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["status"], len(reports), len(hashes), flush=True)


if __name__ == "__main__":
    main()
