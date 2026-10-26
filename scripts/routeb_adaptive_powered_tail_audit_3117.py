#!/usr/bin/env python3
"""Bounded Linux build and exact-identifier axiom audit of the actual powered-family adaptive tail."""

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

from seed_d4_d7_audit_3103 import inspect_log

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/3117_routeb_adaptive_powered_tail_audit.json"
NS = "ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117."
ANALYTIC = [NS + n for n in (
    "poweredFamily_target3117", "poweredFamily_raw_targets3117",
    "poweredFamily_raw_kills3117", "poweredFamily_prefix_square_zero3117",
    "poweredFamily_span_prefix3117", "poweredFamily_cc20_vanishes3117",
    "exists_eventual_relative_tail_budget3117", "exists_eventual_powered_span_qw_neg3117",
    "negative_powered_span_rejects_gate3117",
)]
OTHER = [NS + n for n in (
    "shrinking_coefficient_blocks_relative_decay3117",
    "nonpositive_floor_cannot_supply_relative_budget3117", "unit_factor_does_not_contract3117",
)]
MODULES = ["ConnesWeilRH.Dev.C1RouteBAdaptivePoweredTail3117",
           "ConnesWeilRH.Dev.C1RouteBAdaptivePoweredTail3117Audit"]
SOURCES = [m.replace(".", "/") + ".lean" for m in MODULES] + [
    "scripts/routeb_adaptive_powered_tail_audit_3117.py", "scripts/seed_d4_d7_audit_3103.py",
    "ConnesWeilRH/Dev/C1RouteBQuadraticPinGapCost3116.lean",
    "ConnesWeilRH/Dev/C1ExplicitHealthyCorrectionBudget.lean",
    "ConnesWeilRH/Dev/C1HealthyYoshidaClosedPrefix.lean",
    "ConnesWeilRH/Dev/C1FourPointContradictionAssembly.lean",
    "ConnesWeilRH/Dev/C1FourPointHighShellTail.lean",
    "ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean",
    "ConnesWeilRH/Dev/C1SpectralWeil.lean",
    "ConnesWeilRH/Dev/C1SpectralTailBound.lean",
    "ConnesWeilRH/Dev/C1LaneRD3Root.lean",
    "lean-toolchain", "lake-manifest.json",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inspect(log, code):
    report = inspect_log(log, code, ANALYTIC, OTHER)
    if re.search(r"^(?:[^\r\n]*:\d+:\d+: )?error:", log, re.M):
        report.update(status="FAIL", error_lines_present=True)
    return report


def self_test():
    good = "".join(f"info: Test.lean:1:0: '{n}' depends on axioms: "
                   "[propext, Classical.choice, Quot.sound]\n" for n in ANALYTIC + OTHER)
    good += "Build completed successfully (2 jobs).\n"
    cases = {
        "accept_lake_format": inspect(good, 0)["status"] == "PASS",
        "accept_direct_format": inspect(good.replace("info: Test.lean:1:0: ", ""), 0)["status"] == "PASS",
        "reject_wrong_identifier_suffix": inspect(good.replace(ANALYTIC[0], ANALYTIC[0] + "Extra"), 0)["status"] == "FAIL",
        "reject_missing_footer": inspect(good.split("Build completed")[0], 0)["status"] == "FAIL",
        "reject_nonzero_exit": inspect(good, 1)["status"] == "FAIL",
        "reject_sorryAx": inspect(good.replace("Quot.sound", "sorryAx"), 0)["status"] == "FAIL",
        "reject_new_axiom": inspect(good.replace("Quot.sound", "newAxiom"), 0)["status"] == "FAIL",
        "reject_weakened_analytic_footprint": inspect(good.replace("Classical.choice, ", ""), 0)["status"] == "FAIL",
        "reject_error_with_footer": inspect(good + "error: broken\n", 0)["status"] == "FAIL",
        "reject_source_error_with_footer": inspect(good + "Test.lean:2:1: error: broken\n", 0)["status"] == "FAIL",
    }
    if not all(cases.values()):
        raise RuntimeError("audit negative controls failed")
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
        raise RuntimeError("run in the Linux ext4 verification checkout")
    free = shutil.disk_usage(ROOT).free
    if free < 8 * 1024 ** 3:
        raise RuntimeError("less than 8 GiB free before build")
    provenance = {rel: digest(ROOT / rel) for rel in SOURCES}
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    log = results / "3117_routeb_adaptive_powered_tail_build.log"
    resources = results / "3117_routeb_adaptive_powered_tail_resources.log"
    started = time.monotonic()
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(
            ["/usr/bin/time", "-v", "-o", str(resources), "lake", "build", *MODULES],
            cwd=ROOT, env={**os.environ, "LEAN_NUM_THREADS": "1", "LC_ALL": "C"},
            stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
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
    report = inspect(log.read_text(encoding="utf-8"), code)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", resources.read_text())
    rss_bytes = int(rss.group(1)) * 1024 if rss else None
    unchanged = provenance == {rel: digest(ROOT / rel) for rel in SOURCES}
    if not unchanged or rss_bytes is None or rss_bytes > 8 * 1024 ** 3:
        report["status"] = "FAIL"
    revision = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                                       cwd=ROOT, text=True).strip()
    report.update({"record": 3117, "modules": MODULES, "failure_controls": controls,
                   "elapsed_seconds": time.monotonic() - started, "max_rss_bytes": rss_bytes,
                   "free_bytes_before": free, "free_bytes_after": shutil.disk_usage(ROOT).free,
                   "source_unchanged_during_build": unchanged,
                   "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "mathlib_revision": revision,
                   "hash_convention": "SHA-256 of text with CRLF normalized to LF",
                   "provenance": provenance,
                   "scope": "Under a hypothetical right off-line source zero, choose a complete "
                            "prefix and its actual powered correction before the convolution "
                            "threshold; all later counts and all coefficients above a positive "
                            "floor give negative same-owner qw. Retains the necessary C2 cost. "
                            "No uniform numeric C2, same-owner gate supplier or RH proof."})
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("status", "build_jobs", "elapsed_seconds",
                                           "max_rss_bytes", "missing_theorems")}, indent=2))
    if report["status"] != "PASS":
        print(log.read_text(encoding="utf-8")[-14000:])
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.parent.mkdir(exist_ok=True)
        OUT.write_text(json.dumps({"record": 3117, "status": "FAIL",
                                   "failure_type": type(exc).__name__}, indent=2) + "\n",
                       encoding="utf-8")
        print(f"audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
