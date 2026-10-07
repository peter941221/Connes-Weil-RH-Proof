"""Compile and audit coordinate-bound certificate rows 1-5 of record 2600.

Extends the record-2617 row-zero control to a row batch. Upstream objects
(2598, 2617, the row-zero leaves, the common and payload modules) are
required present and hash-checked against the committed 2617 artifact; the
five new rows compile serially through the resource runner. Every cell
audit and row audit must report exactly the standard three axioms.
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
DEV = ROOT / "ConnesWeilRH/Dev"
BATCH_ROWS = [1, 2, 3, 4, 5]
OUTPUT = ROOT / "results/2623_static_coordinate_rows_validation.json"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
PARENT = ROOT / "results/2617_static_coordinate_bound_validation.json"
UPSTREAM = ["C1RouteACorrectionIntervalPropagation2598",
            "C1RouteACorrectionCoordinateBound2617",
            "C1RouteACorrectionStaticDefectBounds2600Common",
            "C1RouteACorrectionStaticDefectBounds2600PayloadRows0009",
            "C1RouteACorrectionStaticDefectBounds2600PayloadRows1019",
            "C1RouteACorrectionStaticDefectBounds2600PayloadRows2029",
            "C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def batch_modules():
    modules = []
    for row in BATCH_ROWS:
        modules.append(f"C1RouteACorrectionStaticDefectProductCache2600Row{row:02d}")
        for column in range(30):
            modules.append(
                f"C1RouteACorrectionStaticDefectSumBlocks2600Row{row:02d}Col{column:02d}")
        for column in range(30):
            modules.extend(
                f"C1RouteACorrectionStaticDefectSum2617Cell{row:02d}{column:02d}{suffix}"
                for suffix in ("ReLo", "ReHi", "ImLo", "ImHi"))
            modules.append(f"C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}")
            modules.append(
                f"C1RouteACorrectionStaticDefectCoordinate2617Cell{row:02d}{column:02d}Audit")
        modules.append(f"C1RouteACorrectionStaticDefectBounds2600Row{row:02d}")
        modules.append(f"C1RouteACorrectionStaticDefectCoordinate2617Row{row:02d}Audit")
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


def cell_audit_theorem(module):
    match = re.search(r"Cell(\d\d)(\d\d)Audit$", module)
    if match:
        return (f"ConnesWeilRH.Dev.candidateInverseDefectEntryBound2617_"
                f"{match[1]}_{match[2]}")
    match = re.search(r"Row(\d\d)Audit$", module)
    return f"ConnesWeilRH.Dev.candidateInverseDefectEntryBound2600_row_{match[1]}"


def check_generated_sources():
    spec = __import__("importlib").util.spec_from_file_location(
        "coord_rows_2623", ROOT / "scripts/generate_static_coordinate_rows_2623.py")
    generator = __import__("importlib").util.module_from_spec(spec)
    sys.modules["coord_rows_2623"] = generator
    spec.loader.exec_module(generator)
    payload = json.loads(
        (ROOT / "results/2351_moment_matrix_witness.json").read_text(encoding="utf-8"))
    for row in BATCH_ROWS:
        for filename, expected in generator.generated_row_sources(payload, row).items():
            if (DEV / filename).read_bytes() != expected.encode("utf-8"):
                raise ValueError(f"generated source drift: {filename}")


def validate(workspace, logs, lean):
    library = workspace / ".lake/build/lib/lean"
    if os.name != "posix" or not library.is_dir():
        raise ValueError("Linux workspace with a copied project library required")
    # Prefer a workspace-local package copy: reading Mathlib objects
    # through the /mnt/c 9p mount costs minutes per module on a cold VM,
    # while an ext4 copy keeps the serial batch near the 2621-era pacing.
    local_packages = workspace / ".lake/packages"
    package_root = (local_packages if local_packages.is_dir()
                    else ROOT / ".lake/packages")
    packages = sorted(str(path) for path in
                      package_root.glob("*/.lake/build/lib/lean"))
    lean_path = ":".join([str(library)] + packages)

    parent = json.loads(PARENT.read_text())
    if not parent.get("row_static_comparison_verified"):
        raise ValueError("record-2617 row-zero prerequisite is not certified")
    for row in parent["stages"]:
        module = row["module"]
        output = library / "ConnesWeilRH/Dev" / (module + ".olean")
        if not output.is_file() or digest(output) != row["olean_sha256"]:
            raise ValueError(f"record-2617 prerequisite object drift: {module}")
        if digest(DEV / (module + ".lean")) != row["source_sha256"]:
            raise ValueError(f"record-2617 prerequisite source drift: {module}")
    for module in UPSTREAM:
        if not (library / "ConnesWeilRH/Dev" / (module + ".olean")).is_file():
            raise ValueError(f"upstream object missing from library: {module}")

    check_generated_sources()
    logs.mkdir(parents=True, exist_ok=True)
    test_source = ROOT / "scripts/static_coordinate_rows_selftest_2623.py"
    test_hash = digest(test_source)
    test_log = logs / "selftest.log"
    with test_log.open("w", encoding="utf-8") as stream:
        tests = subprocess.run([sys.executable, str(test_source)],
                               stdout=stream, stderr=subprocess.STDOUT)
    text = test_log.read_text()
    count = re.search(r"Ran (\d+) tests? in", text)
    if tests.returncode != 0 or count is None or int(count[1]) != 9 or "\nOK\n" not in text:
        raise RuntimeError("row-batch selftests failed or did not run completely")

    stages = []
    audited = []
    for module in batch_modules():
        source = DEV / (module + ".lean")
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
        if module.endswith("Audit"):
            theorem = cell_audit_theorem(module)
            parse_successful_log(text, theorem, source_hash, object_hash)
            audited.append(theorem)
        stages.append({"module": module, "source_sha256": source_hash,
                       "olean_sha256": object_hash, "exit_code": 0, **metrics})

    check_generated_sources()
    if digest(test_source) != test_hash:
        raise ValueError("selftest source changed during execution")
    if len(audited) != len(BATCH_ROWS) * 31:
        raise ValueError("expected 31 audited theorems per row")
    return {"record": 2623, "status": "STATIC_COORDINATE_ROWS_COMPARISON_PASS",
            "rows": BATCH_ROWS, "entries_verified": len(BATCH_ROWS) * 30,
            "matrix_entries": 900, "witness_sha256": digest(
                ROOT / "results/2351_moment_matrix_witness.json"),
            "generated_sources_match": True, "audited_axioms": AXIOMS,
            "cell_audits_verified": len(BATCH_ROWS) * 30,
            "row_audits_verified": len(BATCH_ROWS),
            "audited_theorems": audited,
            "parent_validation_sha256": digest(PARENT),
            "validator_sha256": digest(Path(__file__)),
            "remaining_static_rows": [row for row in range(6, 30)],
            "full_static_comparison_verified": False,
            "analytic_interval_soundness": "external_premise_required",
            "actual_coefficient_membership": "not_proved",
            "producer_go": False, "rh_claim": False,
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "stages": stages,
            "selftests": {"source_sha256": test_hash, "log_sha256": digest(test_log),
                          "tests_run": int(count[1]), "exit_code": tests.returncode}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="/home/peter/.elan/bin/lean")
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(),
                      arguments.lean)
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["status"], flush=True)


if __name__ == "__main__":
    main()
