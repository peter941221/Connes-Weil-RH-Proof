#!/usr/bin/env python3
"""Replay kernel-checked certificates, actual integrals and existing consumers.

Run in a Linux-side Lean workspace with lake on PATH. Compile independent
certificate modules in bounded batches before building the aggregate, so
Lake never launches all 128 expensive reductions concurrently.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DEV = "ConnesWeilRH.Dev."
NS = DEV + "C1SeedCertificate3101."
SEM = DEV + "C1SeedCertificate3098."
SEED = "ConnesWeilRH.Source.C1ExplicitSmoothSeed."
TRIO = {"propext", "Classical.choice", "Quot.sound"}
ANALYTIC = [SEM + name for name in (
    "initialExp_mem", "power_chain_mem", "valid_product_mem",
    "cell_integral_le_price", "checked_cells_integral_le", "checked_full_integral_lt",
)] + [SEED + name for name in (
    "norm_iteratedDeriv_one_sub3102", "derivOrderL1_smoothSeed_eq_half_integral3102",
)] + [NS + name for name in (
    "transition_integral_four_lt3103", "transition_integral_seven_lt3103",
    "smoothSeed_derivOrderL1_four_lt3103", "smoothSeed_derivOrderL1_seven_lt3103",
    "smoothSeed_d4_d7_bounds3103",
)]
COMPUTATIONAL = [NS + name for name in (
    "allCells_checked", "allCells_length", "allCells_price4", "allCells_price7",
    "reject_underpriced_four3103", "reject_underpriced_seven3103",
    "reject_false_initial_exp3103", "reject_outside_partition3103",
)]
CONTROLS = [
    DEV + "C1RouteBSeedLedgerAllowance3071Audit",
    DEV + "C1RowBPrefixTransport2723Audit",
]


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inspect_log(log, returncode, analytic=(), computational=()):
    declarations = {
        name: [a.strip() for a in axioms.split(",") if a.strip()]
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    }
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        declarations[name] = []
    missing = [name for name in (*analytic, *computational) if name not in declarations]
    unexpected = {name: axioms for name, axioms in declarations.items()
                  if not set(axioms) <= TRIO or
                  (name in analytic and set(axioms) != TRIO)}
    footer = re.search(r"Build completed successfully \((\d+) jobs?\)", log)
    errors = bool(re.search(r"^error:", log, re.MULTILINE))
    passed = (returncode == 0 and footer is not None and not errors
              and "sorryAx" not in log and not unexpected and not missing)
    return {"status": "PASS" if passed else "FAIL", "returncode": returncode,
            "build_jobs": int(footer.group(1)) if footer else None,
            "error_lines_present": errors, "sorryAx_present": "sorryAx" in log,
            "declarations": declarations, "unexpected_axioms": unexpected,
            "missing_theorems": missing}


def self_test():
    good = ("'target' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'calculation' does not depend on any axioms\n"
            "Build completed successfully (2 jobs).\n")
    cases = {
        "valid_analytic_and_pure_computation":
            inspect_log(good, 0, ["target"], ["calculation"])["status"] == "PASS",
        "reject_missing_theorem": inspect_log(good, 0, ["targetExtra"])["status"] == "FAIL",
        "reject_extra_axiom": inspect_log(good.replace("Quot.sound", "newAxiom"),
                                         0, ["target"])["status"] == "FAIL",
        "reject_sorryAx": inspect_log(good + "sorryAx", 0)["status"] == "FAIL",
        "reject_error_with_footer": inspect_log(good + "error: bad\n", 0)["status"] == "FAIL",
        "reject_nonzero_exit": inspect_log(good, 1)["status"] == "FAIL",
        "reject_missing_footer": inspect_log(good.split("Build completed")[0],
                                             0)["status"] == "FAIL",
        "reject_weakened_analytic_audit":
            inspect_log(good, 0, ["calculation"])["status"] == "FAIL",
    }
    if not all(cases.values()):
        raise RuntimeError(f"audit failure controls failed: {cases}")
    return cases


def build(modules, log_path, analytic=(), computational=()):
    run = subprocess.run(["lake", "build", *modules], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8")
    log_path.write_text(run.stdout, encoding="utf-8")
    reading = inspect_log(run.stdout, run.returncode, analytic, computational)
    if reading["status"] != "PASS":
        print(run.stdout[-16000:], flush=True)
        raise RuntimeError(f"Lean build/audit rejected: {reading}")
    return reading


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--batch-size", type=int, choices=range(1, 9), default=4)
    args = parser.parse_args()
    checks = self_test()
    if args.self_test:
        print(json.dumps(checks, indent=2))
        return 0
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    generation = json.loads((results / "3101_seed_certificate_generation.json").read_text())
    assert generation["cells"] == 8192 and len(generation["chunks"]) == 128
    assert generation["generator_sha256"] == digest(ROOT / "scripts/generate_seed_certificates_3101.py")
    batches = []
    for start in range(0, 128, args.batch_size):
        stop = min(start + args.batch_size, 128)
        for index in range(start, stop):
            path = ROOT / f"ConnesWeilRH/Dev/SeedCertificates3101/Chunk{index:03d}.lean"
            assert generation["chunks"][index]["source_sha256"] == digest(path)
        modules = [DEV + f"SeedCertificates3101.Chunk{i:03d}" for i in range(start, stop)]
        reading = build(modules, results / "3103_seed_chunk_build.log")
        batches.append({"start": start, "stop": stop, **reading})
        print(f"kernel-checked chunks {stop}/128", flush=True)
    modules = [DEV + "C1SeedD4D7Certified3103Audit", *CONTROLS]
    final = build(modules, results / "3103_seed_d4_d7_build.log", ANALYTIC, COMPUTATIONAL)
    paths = [ROOT / f"ConnesWeilRH/Dev/{name}.lean" for name in (
        "C1SeedCertificateIntervals3098", "C1SeedCellCertificate3099",
        "C1SeedIntegralCertificate3100", "C1SeedCertificatePilot3101",
        "C1SeedDerivativeReflection3102", "C1SeedD4D7Certified3103",
        "C1SeedCertificateControls3103", "C1SeedD4D7Certified3103Audit",
        "C1SeedJetSemantics2731", "C1SeedEndpointMajorants2732",
        "C1SeedEndpointIntegral2733", "C1RationalNegativeExp2735",
        "C1SeedRationalPhaseBox2736", "C1D4D7EndpointCharges2756",
        "C1ExplicitSeedTransitionReduction", "C1ExplicitSeedThirdOrderStructure",
        "C1RouteBSeedLedgerAllowance3071", "C1RowBPrefixTransport2723",
    )] + [ROOT / "scripts/generate_seed_certificates_3101.py", Path(__file__).resolve()]
    paths += sorted((ROOT / "ConnesWeilRH/Dev/SeedCertificates3101").glob("Chunk*.lean"))
    report = {"record": 3103, **final, "modules": modules,
              "chunk_batch_size": args.batch_size,
              "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "chunk_batches": batches, "failure_controls": checks,
              "cells": 8192, "price_units": generation["price_units"],
              "units_denominator": 4096, "endpoint_added": "proved charge < 1, once",
              "hash_convention": "SHA-256 of text sources with CRLF normalized to LF",
              "provenance": {p.relative_to(ROOT).as_posix(): digest(p) for p in paths},
              "scope": "Actual smoothSeed D4/D7 bounds; cardinal pins, poweredSeed transfer, "
                       "rho-dependent duties and selected signed positivity remain unproved."}
    (results / "3103_seed_d4_d7_audit.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("status", "cells", "build_jobs", "price_units")}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        # A failed rerun must replace an older PASS, not leave a stale verdict.
        failure_path = ROOT / "results/3103_seed_d4_d7_audit.json"
        failure_path.parent.mkdir(exist_ok=True)
        failure_path.write_text(json.dumps({
            "record": 3103, "status": "FAIL", "failure_type": type(exc).__name__,
        }, indent=2) + "\n", encoding="utf-8")
        print(f"certificate audit failed: {exc}", file=sys.stderr)
        sys.exit(1)
