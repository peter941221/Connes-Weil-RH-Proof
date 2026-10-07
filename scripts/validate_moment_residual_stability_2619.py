"""Fingerprint and audit the residual-stability and edge-bound Lean leaves."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from validate_static_coordinate_bounds_2617 import AXIOMS, parse_successful_log

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("C1RouteAMomentResidualStability2619", "C1RouteAMomentEdgeBound2619",
           "C1RouteAMomentResidualStabilityAudit2619")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(workspace, logs, lean):
    library = workspace / ".lake/build/lib/lean"
    roots = os.environ.get("LEAN_PATH", "").split(":")
    if os.name != "posix" or not roots[0] or Path(roots[0]).resolve() != library.resolve():
        raise ValueError("Linux and a complete first project-library root are required")
    if any(not Path(root).is_dir() for root in roots):
        raise ValueError("explicit library roots must exist")
    audit_source = ROOT / "ConnesWeilRH/Dev" / f"{MODULES[-1]}.lean"
    theorems = re.findall(r"^#print axioms (\S+)$", audit_source.read_text(), re.MULTILINE)
    if len(theorems) != 14 or len(set(theorems)) != 14:
        raise ValueError("expected fourteen distinct audited leaves")
    logs.mkdir(parents=True, exist_ok=True)
    stages = []
    environment = dict(os.environ, LC_ALL="C")
    for module in MODULES:
        source = ROOT / "ConnesWeilRH/Dev" / f"{module}.lean"
        output = library / "ConnesWeilRH/Dev" / f"{module}.olean"
        source_hash = digest(source)
        with (logs / f"{module}.log").open("w", encoding="utf-8") as stream:
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
        text = (logs / f"{module}.log").read_text()
        metrics = parse_successful_log(text, source_sha256=source_hash, olean_sha256=object_hash)
        if module == MODULES[-1]:
            for theorem in theorems:
                parse_successful_log(text, theorem, source_hash, object_hash)
        stages.append({"module": module, "source_sha256": source_hash,
                       "olean_sha256": object_hash, "exit_code": 0, **metrics})
    probe = ROOT / "results/2619_analytic_moment_residual_probe.json"
    probe_data = json.loads(probe.read_text())
    if probe_data["actual_entry_containment_lean_verified"] or probe_data["integration_backend_used"]:
        raise ValueError("model-pricing artifact overstates its scope")
    for key, relative in (("capture_sha256", "results/2275_gap_owner_audit.json"),
                          ("witness_sha256", "results/2351_moment_matrix_witness.json"),
                          ("probe_source_sha256", "scripts/analytic_moment_residual_probe_2619.py")):
        if probe_data[key] != digest(ROOT / relative):
            raise ValueError(f"model-pricing input drift: {key}")
    return {"record": 2619, "scope": "owner phase, polynomial residual stability, and edge integral bound",
            "stages": stages, "audited_axioms": AXIOMS, "audited_theorems": theorems,
            "probe_sha256": digest(probe), "probe_source_sha256": digest(ROOT / "scripts/analytic_moment_residual_probe_2619.py"),
            "upstream_objects": "reused; not freshly rebuilt",
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "actual_entry_containment_lean_verified": False,
            "polynomial_table_lean_verified": False,
            "scalar_exponential_table_lean_verified": False,
            "partition_assembly_lean_verified": False,
            "producer_go": False, "rh_claim": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2619_moment_residual_stability_validation.json")
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(), arguments.lean)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("three modules and fourteen exact-axiom audits verified", flush=True)


if __name__ == "__main__":
    main()
