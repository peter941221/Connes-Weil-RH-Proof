"""Compile or validate the row-zero coordinate-bound certificate, not all 2600."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import routea_moment_matrix_exact_check_2351 as checker
from generate_static_coordinate_bounds_2617 import (
    DEV,
    WITNESS,
    generated_sources,
    row_facade_source,
)
from generate_static_sum_blocks_2600 import module_source


ROOT = DEV.parent.parent
OUTPUT = ROOT / "results/2617_static_coordinate_bound_validation.json"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def get_module_order() -> list[str]:
    modules = ["C1RouteACorrectionIntervalPropagation2598",
               "C1RouteACorrectionCoordinateBound2617"]
    for column in range(30):
        modules.append(f"C1RouteACorrectionStaticDefectSumBlocks2600Row00Col{column:02d}")
        modules.extend(
            f"C1RouteACorrectionStaticDefectSum2617Cell00{column:02d}{suffix}"
            for suffix in ("ReLo", "ReHi", "ImLo", "ImHi")
        )
        modules.append(f"C1RouteACorrectionStaticDefectCoordinate2617Cell00{column:02d}")
        modules.append(f"C1RouteACorrectionStaticDefectCoordinate2617Cell00{column:02d}Audit")
    modules.extend(["C1RouteACorrectionStaticDefectBounds2600Row00",
                    "C1RouteACorrectionStaticDefectCoordinate2617Row00Audit"])
    return modules


def parse_successful_log(text: str, audited_theorem: str | None = None,
                         source_sha256: str | None = None,
                         olean_sha256: str | None = None) -> dict:
    if text.count("RESOURCE_RESULT exit=0") != 1:
        raise ValueError("build log does not record one successful runner exit")
    if re.search(r"\berror(?:\(|:)|sorryAx|\bsorry\b|\badmit\b", text):
        raise ValueError("build log contains an error or forbidden placeholder")
    if "Command terminated by signal" in text:
        raise ValueError("interrupted build is not a successful proof")
    for label, digest in (("SOURCE_SHA256", source_sha256), ("OLEAN_SHA256", olean_sha256)):
        if digest is not None and text.count(f"{label}={digest}\n") != 1:
            raise ValueError(f"build log has a stale or missing {label}")
    if audited_theorem is not None:
        pattern = rf"'{re.escape(audited_theorem)}' depends on axioms:\s*\[([^\]]*)\]"
        matches = re.findall(pattern, text)
        if len(matches) != 1 or [value.strip() for value in matches[0].split(",")] != AXIOMS:
            raise ValueError("audit does not report the expected theorem and exact axioms")
    peak = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", text)
    if peak is None or wall is None:
        raise ValueError("build log omits resource measurements")
    parts = wall[1].split(":")
    seconds = 0.0
    for part in parts:
        seconds = seconds * 60 + float(part)
    return {"wall_seconds": seconds, "peak_rss_kib": int(peak[1])}


def compile_modules(workspace: Path, logs: Path, lean: str) -> Path:
    if os.name != "posix":
        raise ValueError("compilation requires Linux and GNU time")
    workspace.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    if workspace.resolve() != ROOT.resolve():
        shutil.copy2(ROOT / "lean-toolchain", workspace / "lean-toolchain")
    library = workspace / ".lake/build/lib/lean"
    library.mkdir(parents=True, exist_ok=True)
    upstream_library = ROOT / ".lake/build/lib/lean"
    if library.resolve() != upstream_library.resolve():
        print("copy upstream project library", flush=True)
        subprocess.run([
            "bash", str(ROOT / "scripts/run_resource_aware_task.sh"),
            "--class", "normal", "--workspace", str(workspace), "--",
            "python3", "-c",
            "import shutil, sys; shutil.copytree(sys.argv[1], sys.argv[2], dirs_exist_ok=True)",
            str(upstream_library), str(library),
        ], check=True, stdout=subprocess.DEVNULL)
    paths = [str(library)]
    configured_paths = [path for path in os.environ.get("LEAN_PATH", "").split(":") if path]
    if configured_paths:
        paths.extend(configured_paths)
    else:
        paths.extend(str(path) for path in (ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))
    environment = dict(os.environ, LEAN_PATH=":".join(paths), LC_ALL="C")
    for module in get_module_order():
        relative = Path("ConnesWeilRH/Dev") / f"{module}.lean"
        source = workspace / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        if source.resolve() != (ROOT / relative).resolve():
            shutil.copy2(ROOT / relative, source)
        output = library / "ConnesWeilRH/Dev" / f"{module}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"compile {module}", flush=True)
        source_digest = hashlib.sha256(source.read_bytes()).hexdigest()
        with (logs / f"{module}.log").open("w", encoding="utf-8") as stream:
            stream.write(f"SOURCE_SHA256={source_digest}\n")
            stream.flush()
            process = subprocess.run([
                "bash", str(ROOT / "scripts/run_resource_aware_task.sh"),
                "--class", "normal", "--workspace", str(workspace), "--",
                "/usr/bin/time", "-v", lean, "-o", str(output), str(relative),
            ], env=environment, stdout=stream, stderr=subprocess.STDOUT)
            if process.returncode == 0 and output.is_file():
                if hashlib.sha256(source.read_bytes()).hexdigest() != source_digest:
                    raise RuntimeError(f"source changed during compilation: {module}")
                stream.write(f"OLEAN_SHA256={hashlib.sha256(output.read_bytes()).hexdigest()}\n")
        if process.returncode != 0:
            raise RuntimeError(f"Lean compilation failed for {module}: {process.returncode}")
        if not output.is_file():
            raise RuntimeError(f"Lean did not emit {module}.olean")
    return library


def validate(logs: Path, library: Path) -> dict:
    payload = json.loads(WITNESS.read_text(encoding="utf-8"))
    expected_sources = {}
    for column in range(30):
        expected_sources.update(generated_sources(payload, column))
    expected_sources["C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00.lean"] = module_source(0, payload)
    expected_sources["C1RouteACorrectionStaticDefectBounds2600Row00.lean"] = row_facade_source()
    for filename, expected in expected_sources.items():
        if (DEV / filename).read_text(encoding="utf-8") != expected:
            raise ValueError(f"generated source drift: {filename}")
    exact = checker.run(WITNESS)
    committed = json.loads((ROOT / "results/2351_moment_matrix_exact_check.json").read_text())
    for key in ("eta_exact", "row_bounds_exact", "channels", "coefficient_boxes_invariant"):
        if exact[key] != committed[key]:
            raise ValueError(f"independent exact certificate drift: {key}")
    stages = []
    for module in get_module_order():
        theorem = None
        if module.endswith("Audit"):
            match = re.search(r"Cell00(\d\d)Audit$", module)
            theorem = (f"ConnesWeilRH.Dev.candidateInverseDefectEntryBound2617_00_{match[1]}"
                       if match else "ConnesWeilRH.Dev.candidateInverseDefectEntryBound2600_row_00")
        source = DEV / f"{module}.lean"
        output = library / "ConnesWeilRH/Dev" / f"{module}.olean"
        if not output.is_file() or output.stat().st_size == 0:
            raise ValueError(f"missing compiled object: {module}")
        source_digest = hashlib.sha256(source.read_bytes()).hexdigest()
        olean_digest = hashlib.sha256(output.read_bytes()).hexdigest()
        metrics = parse_successful_log((logs / f"{module}.log").read_text(), theorem,
                                       source_digest, olean_digest)
        stages.append({
            "module": module, "exit_code": 0,
            "source_sha256": source_digest,
            "olean_sha256": olean_digest,
            "olean_bytes": output.stat().st_size,
            **metrics,
        })
    return {
        "record": 2617, "scope": "row zero of the record-2600 static comparison",
        "row": 0, "entries_verified": 30, "matrix_entries": 900,
        "witness_sha256": hashlib.sha256(WITNESS.read_bytes()).hexdigest(),
        "independent_fraction_replay_matches_2351": True,
        "generated_sources_match": True, "audited_axioms": AXIOMS,
        "cell_audits_verified": 30, "row_audit_verified": True,
        "row_static_comparison_verified": True,
        "full_static_comparison_verified": False,
        "upstream_product_cache": "reused; not rebuilt in this run",
        "analytic_interval_soundness": "external_premise_required",
        "actual_coefficient_membership": "not_proved",
        "producer_go": False, "rh_claim": False,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "stages": stages,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--workspace", type=Path, default=ROOT)
    parser.add_argument("--logs", type=Path, default=ROOT / "build-logs/2617")
    parser.add_argument("--library", type=Path)
    parser.add_argument("--lean", default=shutil.which("lean") or str(Path.home() / ".elan/bin/lean"))
    args = parser.parse_args()
    library = args.library or args.workspace / ".lake/build/lib/lean"
    if args.compile:
        library = compile_modules(args.workspace, args.logs, args.lean)
    result = validate(args.logs, library)
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("ROW00_STATIC_COMPARISON_PASS; 30 cell audits and one row audit; full 2600 remains open")


if __name__ == "__main__":
    main()
