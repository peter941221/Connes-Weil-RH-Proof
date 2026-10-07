"""Compile and audit the record-2625 remaining-panel batch.

Completes the committed 180-panel partition: panels 000-089 and 100-179
(the record-2622 batch 090-099 is the hash-checked parent and stays
untouched). The 170 panel triplets plus the record-2625 batch audit
compile serially through the resource runner; all 26 x 170 audited leaves
must report exactly the standard three axioms.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REMAINING = [index for index in range(180) if not 90 <= index <= 99]
OUTPUT = ROOT / "results/2625_moment_panel_remaining_validation.json"
AUDIT_MODULE = "C1RouteAMomentPanelBatchAudit2625"
PAYLOAD = ROOT / "results/2625_moment_panel_remaining_payload.json"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PARENT = "results/2622_moment_panel_batch_validation.json"
GRANDPARENT = "results/2621_moment_panel_validation.json"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def batch_modules():
    modules = []
    for index in REMAINING:
        tag = f"{index:03d}"
        modules.append(f"C1RouteAMomentPanelScalars2622Panel{tag}")
        modules.append(f"C1RouteAMomentPanelTable2622Panel{tag}")
        modules.append(f"C1RouteAMomentActualPanel2622Panel{tag}")
    modules.append(AUDIT_MODULE)
    return modules


def parse_successful_log(text, audited_theorem=None, source_sha256=None,
                         olean_sha256=None):
    if text.count("RESOURCE_RESULT exit=0") != 1:
        raise ValueError("build log does not record one successful runner exit")
    if re.search(r"\berror(?:\(|:)|sorryAx|\bsorry\b|\badmit\b", text):
        raise ValueError("build log contains an error or forbidden placeholder")
    if "Command terminated by signal" in text:
        raise ValueError("interrupted build is not a successful proof")
    for label, value in (("SOURCE_SHA256", source_sha256),
                         ("OLEAN_SHA256", olean_sha256)):
        if value is not None and text.count(f"{label}={value}\n") != 1:
            raise ValueError(f"build log has a stale or missing {label}")
    if audited_theorem is not None:
        pattern = rf"'{re.escape(audited_theorem)}' depends on axioms:\s*\[([^\]]*)\]"
        matches = re.findall(pattern, text)
        if len(matches) != 1 or [v.strip() for v in matches[0].split(",")] != AXIOMS:
            raise ValueError(f"audit does not certify {audited_theorem} "
                             "with the exact standard axioms")
    peak = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", text)
    if peak is None or wall is None:
        raise ValueError("build log omits resource measurements")
    seconds = 0.0
    for part in wall[1].split(":"):
        seconds = seconds * 60 + float(part)
    return {"wall_seconds": seconds, "peak_rss_kib": int(peak[1])}


def check_generated_inputs():
    spec = __import__("importlib").util.spec_from_file_location(
        "panel_remaining_2625_validate",
        ROOT / "scripts/generate_moment_panel_remaining_2625.py")
    driver = __import__("importlib").util.module_from_spec(spec)
    sys.modules["panel_remaining_2625_validate"] = driver
    spec.loader.exec_module(driver)
    if driver.REMAINING != REMAINING:
        raise ValueError("driver scope does not match the validation scope")
    committed_payload = json.loads(PAYLOAD.read_text())
    if committed_payload["panels"] != REMAINING:
        raise ValueError("payload panel list does not match the batch scope")
    sources, payload = driver.generate(REMAINING, write=False)
    for filename, expected in sources.items():
        if (ROOT / "ConnesWeilRH/Dev" / filename).read_bytes() != expected.encode("utf-8"):
            raise ValueError(f"generated source drift: {filename}")
    committed = json.loads(PAYLOAD.read_text())
    if committed != payload:
        raise ValueError("payload drift")
    return digest(PAYLOAD)


def audit_theorems():
    text = (ROOT / "ConnesWeilRH/Dev" / (AUDIT_MODULE + ".lean")).read_text()
    theorems = re.findall(r"^#print axioms (\S+)$", text, re.MULTILINE)
    if len(theorems) != 26 * len(REMAINING) or len(set(theorems)) != 26 * len(REMAINING):
        raise ValueError("expected 26 distinct audited leaves per panel")
    return theorems


def validate(workspace, logs, lean, test_python):
    library = workspace / ".lake/build/lib/lean"
    if os.name != "posix" or not library.is_dir():
        raise ValueError("Linux workspace with a copied project library required")
    # Prefer a workspace-local package copy: reading Mathlib objects
    # through the /mnt/c 9p mount costs minutes per module on a cold VM,
    # while an ext4 copy keeps the serial batch near the 2622-era pacing.
    local_packages = workspace / ".lake/packages"
    package_root = (local_packages if local_packages.is_dir()
                    else ROOT / ".lake/packages")
    packages = sorted(str(path) for path in
                      package_root.glob("*/.lake/build/lib/lean"))
    lean_path = ":".join([str(library)] + packages)

    parent_path = ROOT / PARENT
    parent_hash = digest(parent_path)
    parent = json.loads(parent_path.read_text())
    if parent.get("status") != "ACTUAL_PANEL_BATCH_INTEGRALS_LEAN_CERTIFIED":
        raise ValueError("record-2622 prerequisite is not certified")
    grandparent_path = ROOT / GRANDPARENT
    if digest(grandparent_path) != parent["parent_validation_sha256"]:
        raise ValueError("record-2622 parent link to the 2621 artifact drifted")
    if json.loads(grandparent_path.read_text()).get("status") != \
            "ACTUAL_PANEL094_INTEGRAL_LEAN_CERTIFIED":
        raise ValueError("record-2621 prerequisite is not certified")
    committed_2622_payload = ROOT / "results/2622_moment_panel_batch_payload.json"
    if digest(committed_2622_payload) != parent["payload_sha256"]:
        raise ValueError("record-2622 payload drifted from its validation artifact")
    for row in parent["stages"]:
        module = row["module"]
        source = ROOT / "ConnesWeilRH/Dev" / (module + ".lean")
        output = library / "ConnesWeilRH/Dev" / (module + ".olean")
        if digest(source) != row["source_sha256"] or digest(output) != row["olean_sha256"]:
            raise ValueError(f"record-2622 prerequisite drift: {module}")

    payload_hash = check_generated_inputs()
    theorems = audit_theorems()
    logs.mkdir(parents=True, exist_ok=True)
    test_source = ROOT / "scripts/moment_panel_remaining_selftest_2625.py"
    test_hash = digest(test_source)
    test_log = logs / "selftest.log"
    with test_log.open("w", encoding="utf-8") as stream:
        tests = subprocess.run([test_python, str(test_source)],
                               stdout=stream, stderr=subprocess.STDOUT)
    text = test_log.read_text()
    count = re.search(r"Ran (\d+) tests? in", text)
    if tests.returncode != 0 or count is None or int(count[1]) != 12 or "\nOK\n" not in text:
        raise RuntimeError("remaining-panel selftests failed or did not run completely")

    stages = []
    for module in batch_modules():
        source = ROOT / "ConnesWeilRH/Dev" / (module + ".lean")
        output = library / "ConnesWeilRH/Dev" / (module + ".olean")
        source_hash = digest(source)
        log = logs / (module + ".log")
        with log.open("w", encoding="utf-8") as stream:
            stream.write(f"SOURCE_SHA256={source_hash}\n")
            stream.flush()
            process = subprocess.run([
                "bash", str(ROOT / "scripts/run_resource_aware_task.sh"),
                "--class", "normal", "--workspace", str(workspace), "--",
                "/usr/bin/time", "-v", lean, f"--root={ROOT}", "-o", str(output),
                str(source),
            ], env=dict(os.environ, LEAN_PATH=lean_path, LC_ALL="C"),
               stdout=stream, stderr=subprocess.STDOUT)
            if process.returncode != 0 or not output.is_file() or digest(source) != source_hash:
                raise RuntimeError(f"failed or drifting compilation: {module}")
            object_hash = digest(output)
            stream.write(f"OLEAN_SHA256={object_hash}\n")
        text = log.read_text()
        metrics = parse_successful_log(text, source_sha256=source_hash,
                                       olean_sha256=object_hash)
        if module == AUDIT_MODULE:
            for theorem in theorems:
                parse_successful_log(text, theorem, source_hash, object_hash)
        stages.append({"module": module, "source_sha256": source_hash,
                       "olean_sha256": object_hash, "exit_code": 0, **metrics})

    refreshed_hash = check_generated_inputs()
    if refreshed_hash != payload_hash or digest(parent_path) != parent_hash:
        raise ValueError("inputs changed during certification")
    if digest(test_source) != test_hash:
        raise ValueError("selftest source changed during execution")
    for row in parent["stages"] + stages:
        module = row["module"]
        source = ROOT / "ConnesWeilRH/Dev" / (module + ".lean")
        output = library / "ConnesWeilRH/Dev" / (module + ".olean")
        if digest(source) != row["source_sha256"] or digest(output) != row["olean_sha256"]:
            raise ValueError("source/object changed during certification")
    payload = json.loads(PAYLOAD.read_text())
    return {"record": 2625, "status": "ACTUAL_PANEL_REMAINING_INTEGRALS_LEAN_CERTIFIED",
            "entry": [0, 0], "panels": REMAINING, "degree": 32,
            "committed_batch_panels": list(range(90, 100)),
            "partition_coverage_lean_certified_panels": 180,
            "partition_pricing": payload["partition_pricing"],
            "payload_sha256": payload_hash,
            "parent_validation_sha256": parent_hash,
            "grandparent_validation_sha256": digest(grandparent_path),
            "capture_sha256": payload["capture_sha256"],
            "witness_sha256": payload["witness_sha256"],
            "validator_sha256": digest(Path(__file__)),
            "stages": stages, "audited_theorems": theorems, "audited_axioms": AXIOMS,
            "selftests": {"source_sha256": test_hash, "log_sha256": digest(test_log),
                          "tests_run": int(count[1]), "exit_code": tests.returncode},
            "panel094_regression_control": "out-of-scope canary reproduces the "
                                           "committed 2621 payload exactly",
            "polynomial_tables_batch_lean_verified": True,
            "actual_panel_integrals_batch_lean_verified": True,
            "partition_assembly_lean_verified": False,
            "actual_entry_containment_lean_verified": False,
            "producer_go": False, "rh_claim": False,
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="/home/peter/.elan/bin/lean")
    parser.add_argument("--test-python", default=sys.executable)
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(),
                      arguments.lean, arguments.test_python)
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], flush=True)


if __name__ == "__main__":
    main()
