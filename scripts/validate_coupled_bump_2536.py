"""Check build acceptance and byte identity of the audited project import cone."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
AUDIT = "ConnesWeilRH.Dev.C1RouteACoupledBumpEnvelope2536Audit"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=ROOT/"results/2536_coupled_bump_validation.json")
    args = parser.parse_args()
    text = args.log.read_text(encoding="utf-8")
    assert "Build completed successfully" in text
    assert not re.search(r"^error:", text, re.M)
    lines = [line for line in text.splitlines() if "depends on axioms:" in line and "2536" in line]
    assert len(lines) == 3
    assert all(line.endswith("[propext, Classical.choice, Quot.sound]") for line in lines)
    seen, pending, hashes = set(), [AUDIT, "ConnesWeilRH"], {}
    mismatch = []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = Path(module.replace(".", "/")+".lean")
        source = ROOT/relative
        built = args.mirror/relative
        body = source.read_bytes()
        if not built.exists() or body != built.read_bytes():
            mismatch.append(relative.as_posix())
        hashes[relative.as_posix()] = hashlib.sha256(body).hexdigest()
        for line in body.decode("utf-8-sig").splitlines():
            if line.startswith("import "):
                pending.extend(name for name in line[7:].split()
                               if name == "ConnesWeilRH" or name.startswith("ConnesWeilRH."))
    assert not mismatch, mismatch
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes(), name
    result = dict(record=2536, status="BUILD_AXIOM_SOURCE_IDENTITY_PASS",
                  build_footer=next(line for line in reversed(text.splitlines())
                                    if "Build completed successfully" in line),
                  audit_lines=lines, project_sources_checked=len(hashes),
                  source_sha256=hashes,
                  build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
                  scope="actual bump derivatives through order four; no weighted-family or numeric import",
                  producer_go=False, rh_claim=False)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(result["status"], result["project_sources_checked"], flush=True)


if __name__ == "__main__":
    main()
