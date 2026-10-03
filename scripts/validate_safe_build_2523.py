"""Bind the 2523 safe-cell certificate audit to the authoritative source cone.

Run under Linux after the focused audit build. A green log alone is not
enough: all project imports must match the authoritative source bytes and
the mathlib checkout must match lake-manifest.json. No numeric or RH claim
is added.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = ["ConnesWeilRH.Dev.C1RouteASafeCertificate2523Audit"]
EXPECTED = {
    "safeSum_reflect2523", "safeCell320_2523", "safeCell443_2523",
    "safeRight_hcell2523", "production_hcell2523",
    "productionTable_remainder_le_415_2523",
    "ownerPanelStripNorm_le_nodes_add_415_2523",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_cone():
    seen, pending = set(), list(TARGETS)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for imported in re.findall(r"^import\s+(ConnesWeilRH[\w.]*)", source.read_text(encoding="utf-8"), re.M):
            pending.append(imported)
    return sorted(module.replace(".", "/")+".lean" for module in seen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()
    log = args.log.read_text(encoding="utf-8")
    assert "Build completed successfully" in log
    assert not re.search(r"^error:", log, re.M) and "sorryAx" not in log
    audited = {}
    for name, axioms in re.findall(r"'ConnesWeilRH.Dev.(\w+)' depends on axioms:\s*\[([^]]+)\]", log):
        if name in EXPECTED:
            names = [x.strip() for x in axioms.split(",")]
            assert names == ["propext", "Classical.choice", "Quot.sound"], (name, names)
            audited[name] = names
    assert set(audited) == EXPECTED, EXPECTED-set(audited)
    files = source_cone()
    mismatches = [name for name in files if (ROOT/name).read_bytes() != (args.mirror/name).read_bytes()]
    assert not mismatches, [{"file": name, "text_equal":
        (ROOT/name).read_text(encoding="utf-8") == (args.mirror/name).read_text(encoding="utf-8")}
        for name in mismatches]
    manifest = json.loads((ROOT/"lake-manifest.json").read_text(encoding="utf-8"))
    expected_rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    actual_rev = subprocess.check_output(["git", "-C", str(args.mirror/".lake/packages/mathlib"),
                                          "rev-parse", "HEAD"], text=True).strip()
    assert actual_rev == expected_rev
    artifact_path = ROOT/"results/2523_safe_certificate.json"
    artifact = json.loads(artifact_path.read_text(encoding="utf-8"))
    assert artifact["status"] == "EXACT_WITNESSES_BUILD_REQUIRED"
    for name, expected_digest in artifact.get("sources", {}).items():
        assert digest(ROOT/name) == expected_digest, f"generator source drift: {name}"
    for name, expected_digest in artifact.get("generated", {}).items():
        assert digest(ROOT/name) == expected_digest, f"generated module drift: {name}"
    fallback_path = ROOT/"results/2522_fallback_certificate.json"
    fallback = json.loads(fallback_path.read_text(encoding="utf-8"))
    for name, expected_digest in fallback.get("sources", {}).items():
        assert digest(ROOT/name) == expected_digest, f"fallback source drift: {name}"
    hashes = {name: digest(ROOT/name) for name in files}
    result = {"record": 2523, "status": "PASS_FOCUSED_BUILD_AND_SOURCE_BINDING",
              "targets": TARGETS, "audited": audited,
              "mathlib_rev": actual_rev, "source_cone_files": len(files),
              "source_cone_sha256": hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest(),
              "source_hashes": hashes, "build_log_sha256": digest(args.log),
              "validator_sha256": digest(Path(__file__).resolve()),
              "certificate_artifact_sha256": digest(artifact_path),
              "fallback_artifact_sha256": digest(fallback_path),
              "scope": "all 640 remainder cells, both signs, table total <= 415; "
                       "node sum, midpoint-to-interpolant and selected-detector margin remain"}
    (ROOT/"results/2523_safe_build_validation.json").write_text(
        json.dumps(result, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(f"PASS: {len(audited)} audited declarations, {len(files)}-file source cone byte-identical")


if __name__ == "__main__":
    main()
