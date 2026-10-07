"""Rebuild and audit actual-owner scalar certificates and both edge integrals."""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from generate_moment_scalar_certificate_2620 import (
    COORDINATE_BITS, RADIUS_BITS, SCALING_STEPS, compact_scalar,
    generated_sources, get_data,
)
from validate_moment_residual_stability_2619 import digest
from validate_static_coordinate_bounds_2617 import AXIOMS, parse_successful_log

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "C1RouteACompactExpSharp3202620", "C1RouteAMomentScalarOwner2620",
    "C1RouteAMomentScalarAmplitude2620Panel094",
    "C1RouteAMomentScalarGrowth2620Panel094",
    "C1RouteAMomentScalarEdge2620Panel094", "C1RouteAMomentActualEdge2620",
    "C1RouteAMomentScalarAudit2620",
)


def check_inputs():
    data = get_data()
    for filename, expected in generated_sources(data).items():
        if (ROOT / "ConnesWeilRH/Dev" / filename).read_bytes() != expected.encode("utf-8"):
            raise ValueError(f"generated source drift: {filename}")
    payload_path = ROOT / "results/2620_moment_scalar_payload.json"
    payload = json.loads(payload_path.read_text())
    expected_fields = {
        "record": 2620, "panel": 94, "center_exact": "9/200", "half_width_exact": "1/200",
        "coordinate_bits": COORDINATE_BITS, "radius_bits": RADIUS_BITS,
        "scaling_steps": SCALING_STEPS,
        "capture_sha256": data["capture_sha256"], "witness_sha256": data["witness_sha256"],
        "generator_sha256": digest(ROOT / "scripts/generate_moment_scalar_certificate_2620.py"),
        "lean_verified": False, "polynomial_table_lean_verified": False,
        "actual_entry_containment_lean_verified": False, "producer_go": False, "rh_claim": False,
    }
    for key, expected in expected_fields.items():
        if payload.get(key) != expected:
            raise ValueError(f"payload scope or input drift: {key}")
    expected_scalars = {}
    for key in ("phase", "growth", "edge"):
        center, radius = compact_scalar(data[key])[-1]
        expected_scalars[key] = {"argument_exact": str(data[key]), "center_exact": str(center),
                                 "radius_exact": str(radius)}
    if payload.get("scalars") != expected_scalars:
        raise ValueError("scalar payload differs from exact reconstruction")
    return {"payload_sha256": digest(payload_path), **expected_fields}, expected_scalars


def validate(workspace, logs, lean, test_python):
    library = workspace / ".lake/build/lib/lean"
    roots = os.environ.get("LEAN_PATH", "").split(":")
    if os.name != "posix" or not roots[0] or Path(roots[0]).resolve() != library.resolve():
        raise ValueError("Linux and a complete first project-library root are required")
    if any(not Path(root).is_dir() for root in roots):
        raise ValueError("explicit library roots must exist")
    inputs, scalars = check_inputs()
    audit_source = ROOT / "ConnesWeilRH/Dev" / f"{MODULES[-1]}.lean"
    theorems = re.findall(r"^#print axioms (\S+)$", audit_source.read_text(), re.MULTILINE)
    if len(theorems) != 22 or len(set(theorems)) != 22:
        raise ValueError("expected twenty-two distinct audited leaves")
    logs.mkdir(parents=True, exist_ok=True)
    stages = []
    environment = dict(os.environ, LC_ALL="C")
    test_source = ROOT / "scripts/moment_scalar_certificate_selftest_2620.py"
    test_hash = digest(test_source)
    test_log = logs / "selftest.log"
    with test_log.open("w", encoding="utf-8") as stream:
        tests = subprocess.run([test_python, str(test_source), "-v"], env=environment,
                               stdout=stream, stderr=subprocess.STDOUT)
    test_text = test_log.read_text()
    count = re.search(r"Ran (\d+) tests? in", test_text)
    if tests.returncode != 0 or count is None or int(count[1]) != 13 or "\nOK\n" not in test_text:
        raise RuntimeError("independent scalar selftests failed or did not run completely")
    if digest(test_source) != test_hash:
        raise ValueError("selftest source changed during execution")
    for module in MODULES:
        source = ROOT / "ConnesWeilRH/Dev" / f"{module}.lean"
        output = library / "ConnesWeilRH/Dev" / f"{module}.olean"
        source_hash = digest(source)
        log = logs / f"{module}.log"
        with log.open("w", encoding="utf-8") as stream:
            stream.write(f"SOURCE_SHA256={source_hash}\n")
            stream.flush()
            process = subprocess.run([
                "bash", str(ROOT / "scripts/run_resource_aware_task.sh"),
                "--class", "normal", "--workspace", str(workspace), "--",
                "/usr/bin/time", "-v", lean, f"--root={ROOT}", "-o", str(output), str(source),
            ], env=environment, stdout=stream, stderr=subprocess.STDOUT)
            if process.returncode != 0 or not output.is_file():
                raise RuntimeError(f"Lean failed for {module}: {process.returncode}")
            if digest(source) != source_hash:
                raise RuntimeError("source changed during compilation")
            object_hash = digest(output)
            stream.write(f"OLEAN_SHA256={object_hash}\n")
        text = log.read_text()
        metrics = parse_successful_log(text, source_sha256=source_hash, olean_sha256=object_hash)
        if module == MODULES[-1]:
            for theorem in theorems:
                parse_successful_log(text, theorem, source_hash, object_hash)
        stages.append({"module": module, "source_sha256": source_hash,
                       "olean_sha256": object_hash, "exit_code": 0, **metrics})
    refreshed_inputs, refreshed_scalars = check_inputs()
    if refreshed_inputs != inputs or refreshed_scalars != scalars:
        raise ValueError("certificate inputs changed during compilation")
    return {
        "record": 2620, "status": "ACTUAL_SCALARS_AND_BOTH_EDGES_LEAN_VERIFIED",
        "entry": [0, 0], "panel": 94, "center_exact": "9/200", "half_width_exact": "1/200",
        "stages": stages, "audited_axioms": AXIOMS, "audited_theorems": theorems,
        "input_fingerprints": inputs, "scalar_certificates": scalars,
        "both_edge_charge_upper_exact": str(Fraction(2, 10 ** 68)),
        "scalar_exponentials_lean_verified": True, "actual_both_edge_integrals_lean_verified": True,
        "polynomial_table_lean_verified": False, "panel_integral_lean_verified": False,
        "partition_assembly_lean_verified": False, "actual_entry_containment_lean_verified": False,
        "producer_go": False, "rh_claim": False,
        "upstream_objects": "reused; not freshly rebuilt",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "validator_sha256": digest(Path(__file__)),
        "selftests": {"source_sha256": test_hash, "log_sha256": digest(test_log),
                      "exit_code": tests.returncode, "tests_run": int(count[1]),
                      "independent_engine": "512-bit Arb; test control, not Lean proof input"},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--test-python", default=sys.executable)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2620_moment_scalar_validation.json")
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(), arguments.lean,
                      arguments.test_python)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["status"], flush=True)


if __name__ == "__main__":
    main()
