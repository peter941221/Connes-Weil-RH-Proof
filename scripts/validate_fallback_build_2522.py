"""Bind the 2521/2522 Lean audit to the Windows-authoritative source cone.

Run under Linux after the focused audit build. A green log alone is not enough:
all project imports must match the authoritative source bytes and the mathlib
checkout must match lake-manifest.json. No numeric or RH claim is added.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = ["ConnesWeilRH.Dev.C1RouteAExpFamilyFallback2521Audit",
           "ConnesWeilRH.Dev.C1RouteAFallbackCertificate2522Audit"]
EXPECTED = {
    "ownerPanelWeightedSecondDeriv_le_familyFallback2521", "ownerProductionCell_bound2521",
    "ownerPanelStripNorm_le_productionExpUpper2521", "ownerPanelStripNorm_le_productionTable2521",
    "familyFallback_scalar2522", "fallbackFamily_bound2522", "familyFallback_bound2522",
    "fallback_hcell2522", "cell0_hcell2522", "ownerPanelStripNorm_le_safeTable2522",
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
    price_path = ROOT/"results/2521_fallback_reprice.json"
    price = json.loads(price_path.read_text(encoding="utf-8"))
    assert price["status"] == "PASS_EXTERNAL_PRICE_NOT_FULL_CERTIFICATE"
    for name, expected_digest in price["sources"].items():
        assert digest(ROOT/name) == expected_digest, f"price source drift: {name}"
    hashes = {name: digest(ROOT/name) for name in files}
    result = {"record": 2522, "status": "PASS_FOCUSED_BUILD_AND_SOURCE_BINDING",
              "targets": TARGETS, "audited": audited,
              "mathlib_rev": actual_rev, "source_cone_files": len(files),
              "source_cone_sha256": hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest(),
              "source_hashes": hashes, "build_log_sha256": digest(args.log),
              "validator_sha256": digest(Path(__file__).resolve()),
              "external_price_sha256": digest(price_path),
              "scope": "392 fallback cells, both signs; 248 safe hcell premises remain"}
    (ROOT/"results/2522_fallback_build_validation.json").write_text(
        json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"PASS: {len(audited)} audited declarations; {len(files)} byte-identical project sources")


if __name__ == "__main__":
    main()
