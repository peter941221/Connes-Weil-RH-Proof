#!/usr/bin/env python3
"""Bounded Linux build and exact-identifier axiom audit of the same-owner signed prime cut."""

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
OUT = ROOT / "results/3119_routeb_signed_prime_cut_audit.json"
NS = "ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119."
ANALYTIC = [NS + n for n in (
    "primeCut_eq_visible_filter3119", "finitePrimeSum_eq_cut_add_remainder3119",
    "full_gate_eq_cut_add_remainder3119", "gate_iff_signed_remainder_budget3119",
    "poweredFamily_full_gate3119", "storedSpan_support3119",
    "storedSpan_visible_prime_bound3119", "storedSpan_remainder_at_complete_bound3119",
    "storedSpan_complete_prime_cut3119", "storedSpan_full_gate3119",
)]
OTHER = [NS + n for n in (
    "primeCut_zero3119", "remainder_at_zero3119", "primeCut_succ3119",
    "nonzero_terms_can_cancel3119", "negative_cut_does_not_determine_full_sign3119",
)]
MODULES = ["ConnesWeilRH.Dev.C1RouteBSignedPrimeCut3119",
           "ConnesWeilRH.Dev.C1RouteBSignedPrimeCut3119Audit"]
SOURCES = [m.replace(".", "/") + ".lean" for m in MODULES] + [
    "scripts/routeb_signed_prime_cut_audit_3119.py", "scripts/seed_d4_d7_audit_3103.py",
    "ConnesWeilRH/Dev/C1RouteBAdaptivePoweredTail3117.lean",
    "ConnesWeilRH/Dev/C1RouteBPoweredSeedCarrier3110.lean",
    "ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean",
    "ConnesWeilRH/Dev/C1ExplicitSmoothSeed.lean",
    "ConnesWeilRH/Dev/C1SameOwnerWeil.lean",
    "ConnesWeilRH/Dev/C1OrbitWindowSemiLocalGate.lean",
    "ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean",
    "ConnesWeilRH/Dev/C1TwoPointSpectralDecomposition.lean",
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
    log = results / "3119_routeb_signed_prime_cut_build.log"
    resources = results / "3119_routeb_signed_prime_cut_resources.log"
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
    report.update({"record": 3119, "modules": MODULES, "failure_controls": controls,
                   "elapsed_seconds": time.monotonic() - started, "max_rss_bytes": rss_bytes,
                   "free_bytes_before": free, "free_bytes_after": shutil.disk_usage(ROOT).free,
                   "source_unchanged_during_build": unchanged,
                   "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "mathlib_revision": revision,
                   "hash_convention": "SHA-256 of text with CRLF normalized to LF",
                   "provenance": provenance,
                   "scope": "Exact signed cut/remainder identity on the actual powered spans; "
                            "proved finite complete prime bound on the stored n=3 span. "
                            "No truncated Fourier readback, numerical remainder value, "
                            "full gate sign, zero-set assertion or RH proof."})
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
        OUT.write_text(json.dumps({"record": 3119, "status": "FAIL",
                                   "failure_type": type(exc).__name__}, indent=2) + "\n",
                       encoding="utf-8")
        print(f"audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
