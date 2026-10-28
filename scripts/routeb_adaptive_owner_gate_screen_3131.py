#!/usr/bin/env python3
"""Record 3131: fail-closed screen for the adaptive same-owner gate."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "results/3131_routeb_adaptive_owner_gate_screen.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def provenance(owner_path: Path | None) -> dict[str, str | None]:
    return {
        "script": Path(__file__).resolve().relative_to(ROOT).as_posix(),
        "script_sha256": sha256(Path(__file__).resolve()),
        "owner_manifest": owner_path.relative_to(ROOT).as_posix()
        if owner_path is not None and owner_path.is_relative_to(ROOT)
        else (str(owner_path) if owner_path is not None else None),
        "owner_manifest_sha256": sha256(owner_path)
        if owner_path is not None and owner_path.is_file()
        else None,
    }


def fail(output: Path, owner_path: Path | None, failure: str, detail: str) -> int:
    artifact = {
        "record": 3131,
        "status": "CONTROL-FAIL",
        "failure": failure,
        "decision": "Do not claim qw < 0, qw >= 0, a gate margin, Producer GO, SourceRH, or RH.",
        "detail": detail,
        "owner_gate_status": "NOT-RUN",
        "tail_status": "NOT-RUN",
        "provenance": provenance(owner_path),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 2


def validate(data: object) -> tuple[dict[str, object] | None, str | None]:
    if not isinstance(data, dict):
        return None, "owner manifest must be a JSON object"
    required = {"owner_id", "owner_digest", "rho", "lambda", "global_prime_index_set", "both_frequency_signs", "signed_residual_bound", "rounding_allowance", "adaptive_tail_budget"}
    missing = sorted(required - data.keys())
    if missing:
        return None, "missing fields: " + ", ".join(missing)
    return data, None


def run(owner_path: Path | None, output: Path) -> int:
    if owner_path is None:
        return fail(output, None, "OWNER-DATA-MISSING", "No actual adaptive owner manifest was supplied.")
    if not owner_path.is_file():
        return fail(output, owner_path, "OWNER-DATA-MISSING", "The supplied owner manifest does not exist.")
    try:
        data, error = validate(json.loads(owner_path.read_text(encoding="utf-8")))
    except (OSError, json.JSONDecodeError) as exc:
        return fail(output, owner_path, "OWNER-DATA-INVALID", str(exc))
    if error is not None or data is None:
        return fail(output, owner_path, "OWNER-DATA-INVALID", error or "invalid manifest")
    checks = {
        "owner_identity_present": isinstance(data["owner_id"], str) and bool(data["owner_id"]) and isinstance(data["owner_digest"], str) and bool(data["owner_digest"]),
        "complete_global_prime_index_set": isinstance(data["global_prime_index_set"], list) and bool(data["global_prime_index_set"]) and all(isinstance(value, int) for value in data["global_prime_index_set"]),
        "both_frequency_signs_certified": data["both_frequency_signs"] == {"positive": True, "negative": True},
        "signed_residual_bound_present": isinstance(data["signed_residual_bound"], dict) and bool(data["signed_residual_bound"]),
        "rounding_allowance_present": isinstance(data["rounding_allowance"], dict) and bool(data["rounding_allowance"]),
        "adaptive_tail_budget_present": isinstance(data["adaptive_tail_budget"], dict) and bool(data["adaptive_tail_budget"]),
    }
    artifact = {
        "record": 3131,
        "status": "CONTROL-FAIL",
        "failure": None if all(checks.values()) else "OWNER-GATE-PREMISE-MISSING",
        "decision": "A complete owner gate is not promoted by this screen; an independent signed margin and tail theorem remain required.",
        "owner_id": data["owner_id"],
        "lambda": data["lambda"],
        "rho": data["rho"],
        "checks": checks,
        "owner_gate_status": "STRUCTURAL-PASS" if all(checks.values()) else "FAIL",
        "tail_status": "PRESENT" if checks["adaptive_tail_budget_present"] else "MISSING",
        "continuum_status": "NOT-EVALUATED",
        "provenance": provenance(owner_path),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--owner-data", type=Path)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    return run(args.owner_data, args.output)


if __name__ == "__main__":
    raise SystemExit(main())