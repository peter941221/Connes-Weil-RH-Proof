#!/usr/bin/env python3
"""Bounded Linux build and exact-identifier audit of the exact same-owner unavoidable Weil deficit."""

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
OUT = ROOT / "results/3122_actual_weil_unavoidable_deficit_audit.json"
NS = "ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122."
ANALYTIC = [NS + n for n in (
    "c3Sigma_continuous3122",
    "gateSymbol_continuous3122",
    "weilDensity_continuous3122",
    "gateSymbol_zero_pos3122",
    "fourier_analytic3122",
    "fourier_global_nonzero3122",
    "exists_deficit_frequency3122",
    "weilDensity_integrable3122",
    "credit_integrable3122",
    "deficit_integrable3122",
    "deficit_integral_pos3122",
    "not_weilDensity_pointwise_nonneg3122",
    "density_eq_credit_sub_deficit3122",
    "qw_eq_credit_sub_deficit3122",
    "poweredFamily_span_test_ne_zero3122",
    "poweredFamily_deficit_integral_pos3122",
    "selectedOwner_deficit_integral_pos3122",
    "density_zero_at_origin_of_transform_zero3122",
    "deficit_zero_of_zero_test3122",
    "poweredFamily_span_fourier_zero3122",
    "zero_at_origin_and_strict_deficit3122",
)]
OTHER = []
MODULES = ["ConnesWeilRH.Dev.C1ActualWeilUnavoidableDeficit3122",
           "ConnesWeilRH.Dev.C1ActualWeilUnavoidableDeficit3122Audit"]
SOURCES = [m.replace(".", "/") + ".lean" for m in MODULES] + [
    "scripts/actual_weil_unavoidable_deficit_audit_3122.py",
    "scripts/seed_d4_d7_audit_3103.py",
    "ConnesWeilRH/Dev/C1RouteBArchimedeanFourierReadback3121.lean",
    "ConnesWeilRH/Dev/C1RouteBPrimeFourierReadback3120.lean",
    "ConnesWeilRH/Dev/C1RouteBSignedPrimeCut3119.lean",
    "ConnesWeilRH/Dev/C1RouteBAdaptivePoweredTail3117.lean",
    "ConnesWeilRH/Dev/C1RouteAOwnerAnalyticTransform3092.lean",
    "ConnesWeilRH/Dev/C1RouteAAnalyticPuncturedWitness3085.lean",
    "ConnesWeilRH/Dev/C1RouteAOwnerPuncturedBridge3087.lean",
    "ConnesWeilRH/Dev/C1RouteANegativeEnergyWitness3093.lean",
    "ConnesWeilRH/Dev/C1C3SigmaZeroMargin3090.lean",
    "ConnesWeilRH/Dev/C1C3SigmaKernel.lean",
    "ConnesWeilRH/Dev/C1G8R3ScatteringPhaseDigamma.lean",
    "ConnesWeilRH/Dev/C1SameOwnerWeil.lean",
    "ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean",
    "ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean",
    "ConnesWeilRH/Dev/C1FourPointSpectralPrefixTransport.lean",
    "ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean",
    "lean-toolchain",
    "lake-manifest.json",
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
    log = results / "3122_actual_weil_unavoidable_deficit_build.log"
    resources = results / "3122_actual_weil_unavoidable_deficit_resources.log"
    build_bytes_before = int(subprocess.check_output(
        ["du", "-sb", str(ROOT / ".lake/build")], text=True).split()[0])
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
    build_bytes_after = int(subprocess.check_output(
        ["du", "-sb", str(ROOT / ".lake/build")], text=True).split()[0])
    build_growth_bytes = max(0, build_bytes_after - build_bytes_before)
    unchanged = provenance == {rel: digest(ROOT / rel) for rel in SOURCES}
    if (not unchanged or rss_bytes is None or rss_bytes > 8 * 1024 ** 3
            or build_growth_bytes > 2 * 1024 ** 3):
        report["status"] = "FAIL"
    revision = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
                                       cwd=ROOT, text=True).strip()
    report.update({"record": 3122, "modules": MODULES, "failure_controls": controls,
                   "elapsed_seconds": time.monotonic() - started, "max_rss_bytes": rss_bytes,
                   "build_bytes_before": build_bytes_before,
                   "build_bytes_after": build_bytes_after,
                   "build_growth_bytes": build_growth_bytes,
                   "free_bytes_before": free, "free_bytes_after": shutil.disk_usage(ROOT).free,
                   "source_unchanged_during_build": unchanged,
                   "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "mathlib_revision": revision,
                   "hash_convention": "SHA-256 of text with CRLF normalized to LF",
                   "provenance": provenance,
                   "scope": "Integrable exact physical Weil credit and deficit with the actual "
                            "signed identity. Strict positive deficit on the selected detector "
                            "and actual powered spans; zero at the origin does not erase it. "
                            "No global credit-deficit domination, Weil sign or RH proof."})
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
        OUT.write_text(json.dumps({"record": 3122, "status": "FAIL",
                                   "failure_type": type(exc).__name__}, indent=2) + "\n",
                       encoding="utf-8")
        print(f"audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
