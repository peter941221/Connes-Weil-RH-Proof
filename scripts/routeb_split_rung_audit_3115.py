#!/usr/bin/env python3
"""Build and audit the split-rung envelope and actual cardinal exterior.

Run from a Linux ext4 checkout with the local import closure synchronized.
The numerical probe has its own MODEL-PASS artifact and is not a proof input.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/3115_routeb_split_rung_audit.json"
NS = "ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115."
NAMES = [
    "splitRungs_nonempty3115", "splitD_nonneg3115", "splitD_bound3115",
    "norm_cardinalSum_poweredSeed_le_split_env3115", "poweredSeed_exterior_arm3115",
    "weighted_cardinalSum_le_exterior3115", "normalized_cardinalSum_le_exterior3115",
    "empty_exterior_bound3115", "zero_values_exterior_bound3115",
    "reject_low_rung_degree3115", "reject_zero_frequency_exterior3115",
    "negative_frequency_exterior3115",
]
ANALYTIC = {NS + name for name in NAMES[2:7] + NAMES[11:]}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULES = ["ConnesWeilRH.Dev.C1RouteBSplitRungEnvelope3115",
           "ConnesWeilRH.Dev.C1RouteBCardinalExterior3115",
           "ConnesWeilRH.Dev.C1RouteBSplitRungEnvelope3115Audit"]
SOURCES = [name.replace(".", "/") + ".lean" for name in MODULES] + [
    "scripts/routeb_split_rung_audit_3115.py",
    "ConnesWeilRH/Dev/C1SeedD4D7Certified3103.lean",
    "ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderIntervalCertificate.lean",
    "ConnesWeilRH/Dev/C1PoweredSeedEnvelope2725.lean",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inspect(log, returncode):
    matches = re.findall(r"(?:^|: )'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.M)
    pure = re.findall(r"(?:^|: )'([^']+)' does not depend on any axioms", log, re.M)
    declarations = {name: [a.strip() for a in axioms.split(",") if a.strip()]
                    for name, axioms in matches}
    declarations.update({name: [] for name in pure})
    missing = [NS + name for name in NAMES if NS + name not in declarations]
    unexpected = {name: axioms for name, axioms in declarations.items()
                  if not set(axioms) <= ALLOWED or
                  (name in ANALYTIC and set(axioms) != ALLOWED)}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    errors = bool(re.search(r"^(?:[^\r\n]*:\d+:\d+: )?error:", log, re.M))
    passed = (returncode == 0 and footer is not None and not errors
              and "sorryAx" not in log and not missing and not unexpected)
    return {"status": "PASS" if passed else "FAIL", "build_returncode": returncode,
            "build_jobs": int(footer.group(1)) if footer else None,
            "error_lines_present": errors, "sorryAx_present": "sorryAx" in log,
            "required_theorems": {NS + n: declarations.get(NS + n) for n in NAMES},
            "missing_theorems": missing, "unexpected_axioms": unexpected}


def self_test():
    good = "".join(f"'{NS}{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                   for n in NAMES) + "Build completed successfully (3 jobs).\n"
    cases = {
        "accept_complete_audit": inspect(good, 0)["status"] == "PASS",
        "accept_lake_info_prefix": inspect(re.sub(r"(?m)^'", "info: Test.lean:1:0: '",
                                                   good), 0)["status"] == "PASS",
        "reject_nonzero_exit": inspect(good, 1)["status"] == "FAIL",
        "reject_missing_footer": inspect(good.split("Build completed")[0], 0)["status"] == "FAIL",
        "reject_suffix_name_substitution":
            inspect(good.replace(NAMES[3], NAMES[3] + "Extra"), 0)["status"] == "FAIL",
        "reject_new_axiom": inspect(good.replace("Quot.sound", "newAxiom"), 0)["status"] == "FAIL",
        "reject_sorryAx": inspect(good + "sorryAx\n", 0)["status"] == "FAIL",
        "reject_error_with_success_footer": inspect(good + "error: broken\n", 0)["status"] == "FAIL",
        "reject_source_error_with_success_footer":
            inspect(good + "Test.lean:12:3: error: broken\n", 0)["status"] == "FAIL",
        "reject_weakened_analytic_footprint":
            inspect(good.replace("[propext, Classical.choice, Quot.sound]", "[propext]"), 0)["status"] == "FAIL",
    }
    if not all(cases.values()):
        raise RuntimeError("audit rejection controls failed")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    controls = self_test()
    if args.self_test:
        print(json.dumps(controls, indent=2))
        return 0
    if sys.platform != "linux":
        raise RuntimeError("run this checker in the Linux verification checkout")
    free = shutil.disk_usage(ROOT).free
    if free < 8 * 1024 ** 3:
        raise RuntimeError("less than 8 GiB free before build")
    provenance = {rel: digest(ROOT / rel) for rel in SOURCES}
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    log_path = results / "3115_routeb_split_rung_build.log"
    resources_path = results / "3115_routeb_split_rung_resources.log"
    environment = {**os.environ, "LEAN_NUM_THREADS": "1", "LC_ALL": "C"}
    command = ["/usr/bin/time", "-v", "-o", str(resources_path), "lake", "build", *MODULES]
    started = time.monotonic()
    with log_path.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=1200)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise TimeoutError("20-minute focused build budget exhausted")
    report = inspect(log_path.read_text(encoding="utf-8"), code)
    usage = resources_path.read_text(encoding="utf-8")
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", usage)
    rss_bytes = int(rss.group(1)) * 1024 if rss else None
    source_unchanged = provenance == {rel: digest(ROOT / rel) for rel in SOURCES}
    if not source_unchanged or rss_bytes is None or rss_bytes > 8 * 1024 ** 3:
        report["status"] = "FAIL"
    report.update({"record": 3115, "modules": MODULES, "failure_controls": controls,
                   "elapsed_seconds": time.monotonic() - started,
                   "max_rss_bytes": rss_bytes, "free_bytes_before": free,
                   "free_bytes_after": shutil.disk_usage(ROOT).free,
                   "source_unchanged_during_build": source_unchanged,
                   "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "hash_convention": "SHA-256 of text with CRLF normalized to LF",
                   "provenance": provenance,
                   "scope": "Proved split-rung envelope and actual-cardinal two-sided "
                            "exterior bound; finite interval replay, numeric pins, "
                            "gate and arbitrary-rho duties remain open."})
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("status", "build_jobs", "elapsed_seconds",
                                           "max_rss_bytes", "missing_theorems")}, indent=2))
    if report["status"] != "PASS":
        print(log_path.read_text(encoding="utf-8")[-14000:])
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.parent.mkdir(exist_ok=True)
        OUT.write_text(json.dumps({"record": 3115, "status": "FAIL",
                                   "failure_type": type(exc).__name__}, indent=2) + "\n",
                       encoding="utf-8")
        print(f"audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
