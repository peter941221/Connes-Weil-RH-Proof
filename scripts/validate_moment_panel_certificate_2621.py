"""Fingerprint and audit the first actual normalized moment panel certificate."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from generate_moment_panel_certificate_2621 import generated_sources, panel_data, payload_data
from validate_moment_scalar_certificate_2620 import check_inputs as check_scalar_inputs
from validate_moment_residual_stability_2619 import digest
from validate_static_coordinate_bounds_2617 import AXIOMS, parse_successful_log

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("C1RouteARationalPolynomial2621", "C1RouteAMomentPanelTable2621Panel094",
           "C1RouteAMomentActualPanel2621Panel094", "C1RouteAMomentPanelAudit2621")


def check_inputs():
    check_scalar_inputs()
    data = panel_data()
    for filename, expected in generated_sources(data).items():
        if ROOT.joinpath("ConnesWeilRH/Dev", filename).read_bytes() != expected.encode("utf-8"):
            raise ValueError(f"generated source drift: {filename}")
    path = ROOT / "results/2621_moment_panel_payload.json"
    if json.loads(path.read_text()) != payload_data(data):
        raise ValueError("panel payload or fingerprint drift")
    return digest(path), data


def validate(workspace, logs, lean, test_python):
    library = workspace / ".lake/build/lib/lean"
    roots = os.environ.get("LEAN_PATH", "").split(":")
    if os.name != "posix" or not roots[0] or Path(roots[0]).resolve() != library.resolve():
        raise ValueError("Linux and a complete first project-library root are required")
    if any(not Path(root).is_dir() for root in roots):
        raise ValueError("explicit library roots must exist")
    payload_hash, data = check_inputs()
    parent_path = ROOT / "results/2620_moment_scalar_validation.json"
    parent_hash = digest(parent_path)
    parent = json.loads(parent_path.read_text())
    if (parent["audited_axioms"] != AXIOMS or len(parent["audited_theorems"]) != 22 or
            not parent["scalar_exponentials_lean_verified"] or not parent["actual_both_edge_integrals_lean_verified"]):
        raise ValueError("scalar prerequisite is not certified")
    for row in parent["stages"]:
        source = ROOT / "ConnesWeilRH/Dev" / (row["module"] + ".lean")
        output = library / "ConnesWeilRH/Dev" / (row["module"] + ".olean")
        if digest(source) != row["source_sha256"] or digest(output) != row["olean_sha256"]:
            raise ValueError("scalar prerequisite source/object drift")
    logs.mkdir(parents=True, exist_ok=True)
    test_source = ROOT / "scripts/moment_panel_certificate_selftest_2621.py"
    test_hash = digest(test_source)
    test_log = logs / "selftest.log"
    with test_log.open("w", encoding="utf-8") as stream:
        tests = subprocess.run([test_python, str(test_source), "-v"],
                               stdout=stream, stderr=subprocess.STDOUT)
    text = test_log.read_text()
    count = re.search(r"Ran (\d+) tests? in", text)
    if tests.returncode != 0 or count is None or int(count[1]) != 14 or "\nOK\n" not in text:
        raise RuntimeError("panel selftests failed or did not run completely")
    audit_source = ROOT / "ConnesWeilRH/Dev" / (MODULES[-1] + ".lean")
    theorems = re.findall(r"^#print axioms (\S+)$", audit_source.read_text(), re.MULTILINE)
    if len(theorems) != 26 or len(set(theorems)) != 26:
        raise ValueError("expected twenty-six distinct audited leaves")
    stages = []
    for module in MODULES:
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
                "/usr/bin/time", "-v", lean, f"--root={ROOT}", "-o", str(output), str(source),
            ], env=dict(os.environ, LC_ALL="C"), stdout=stream, stderr=subprocess.STDOUT)
            if process.returncode != 0 or not output.is_file() or digest(source) != source_hash:
                raise RuntimeError(f"failed or drifting compilation: {module}")
            object_hash = digest(output)
            stream.write(f"OLEAN_SHA256={object_hash}\n")
        text = log.read_text()
        metrics = parse_successful_log(text, source_sha256=source_hash, olean_sha256=object_hash)
        if module == MODULES[-1]:
            for theorem in theorems:
                parse_successful_log(text, theorem, source_hash, object_hash)
        stages.append({"module": module, "source_sha256": source_hash, "olean_sha256": object_hash,
                       "exit_code": 0, **metrics})
    refreshed_hash, refreshed_data = check_inputs()
    if refreshed_hash != payload_hash or refreshed_data != data or digest(parent_path) != parent_hash:
        raise ValueError("inputs changed during certification")
    if digest(test_source) != test_hash:
        raise ValueError("selftest source changed during execution")
    for row in parent["stages"] + stages:
        source = ROOT / "ConnesWeilRH/Dev" / (row["module"] + ".lean")
        output = library / "ConnesWeilRH/Dev" / (row["module"] + ".olean")
        if digest(source) != row["source_sha256"] or digest(output) != row["olean_sha256"]:
            raise ValueError("source/object changed during certification")
    return {"record": 2621, "status": "ACTUAL_PANEL094_INTEGRAL_LEAN_CERTIFIED",
            "entry": [0, 0], "panel": 94, "degree": 32,
            "normalized_interval_exact": ["1/25", "1/20"],
            "physical_radius_exact": str(data["radius"]),
            "integral_center_exact": str(data["integral_center"]),
            "integral_charge_exact": str(data["integral_charge"]), "integral_charge_upper_exact": "1/" + str(10 ** 82),
            "payload_sha256": payload_hash, "scalar_validation_sha256": parent_hash,
            "capture_sha256": data["capture_sha256"], "witness_sha256": data["witness_sha256"],
            "validator_sha256": digest(Path(__file__)),
            "stages": stages, "audited_theorems": theorems, "audited_axioms": AXIOMS,
            "selftests": {"source_sha256": test_hash, "log_sha256": digest(test_log),
                          "tests_run": int(count[1]), "exit_code": tests.returncode},
            "polynomial_table_panel094_lean_verified": True, "actual_panel094_integral_lean_verified": True,
            "partition_assembly_lean_verified": False, "actual_entry_containment_lean_verified": False,
            "producer_go": False, "rh_claim": False,
            "upstream_objects": "fingerprint-checked 2620 objects and reused older objects; not freshly rebuilt",
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--test-python", default=sys.executable)
    parser.add_argument("--output", type=Path, default=ROOT / "results/2621_moment_panel_validation.json")
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(), arguments.lean,
                      arguments.test_python)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"], flush=True)


if __name__ == "__main__":
    main()
