#!/usr/bin/env python3
"""Record 3136: semantic contract screen for an exact-owner gate certificate.

This validates certificate shape and interval semantics only. It never turns a
JSON manifest into a Lean premise, gate proof, Producer GO, SourceRH, or RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "results/3136_routeb_exact_owner_gate_certificate_contract.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def finite(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def provenance(manifest: Path | None) -> dict[str, str | None]:
    return {
        "script": Path(__file__).resolve().relative_to(ROOT).as_posix(),
        "script_sha256": sha256(Path(__file__).resolve()),
        "owner_manifest": manifest.relative_to(ROOT).as_posix()
        if manifest is not None and manifest.is_relative_to(ROOT)
        else (str(manifest) if manifest is not None else None),
        "owner_manifest_sha256": sha256(manifest)
        if manifest is not None and manifest.is_file()
        else None,
    }


def fail(output: Path, manifest: Path | None, failure: str, detail: str) -> int:
    artifact = {
        "record": 3136,
        "status": "CONTROL-FAIL",
        "failure": failure,
        "detail": detail,
        "certificate_status": "NOT-RUN",
        "decision": "Do not claim a gate margin, Producer GO, SourceRH, or RH.",
        "provenance": provenance(manifest),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 2


def interval(data: Any, *, nonnegative: bool = False) -> bool:
    if not isinstance(data, dict) or data.get("certified") is not True:
        return False
    if not finite(data.get("lower")) or not finite(data.get("upper")):
        return False
    if data["lower"] > data["upper"]:
        return False
    return not nonnegative or data["lower"] >= 0


def validate(data: Any) -> tuple[dict[str, Any] | None, dict[str, bool], str | None]:
    if not isinstance(data, dict):
        return None, {}, "owner manifest must be a JSON object"
    required = {
        "owner_id", "owner_digest", "rho", "lambda", "owner_parameters",
        "global_prime_index_set", "frequency_readback", "signed_residual_bound",
        "rounding_allowance", "adaptive_tail_budget", "gate_margin",
    }
    missing = sorted(required - data.keys())
    if missing:
        return None, {}, "missing fields: " + ", ".join(missing)
    rho = data["rho"]
    params = data["owner_parameters"]
    primes = data["global_prime_index_set"]
    frequencies = data["frequency_readback"]
    checks = {
        "owner_identity": isinstance(data["owner_id"], str) and bool(data["owner_id"])
        and isinstance(data["owner_digest"], str)
        and len(data["owner_digest"]) == 64
        and all(ch in "0123456789abcdefABCDEF" for ch in data["owner_digest"]),
        "rho_and_lambda_finite": isinstance(rho, dict)
        and finite(rho.get("re")) and finite(rho.get("im")) and finite(data["lambda"]),
        "owner_parameters_complete": isinstance(params, dict)
        and finite(params.get("N")) and int(params.get("N", -1)) >= 0
        and finite(params.get("n")) and int(params.get("n", -1)) >= 0
        and isinstance(params.get("route_nodes_digest"), str)
        and bool(params.get("route_nodes_digest")),
        "prime_index_set_complete": isinstance(primes, list) and bool(primes)
        and all(isinstance(value, int) and not isinstance(value, bool) and value > 0 for value in primes)
        and primes == sorted(set(primes)),
        "positive_frequency_enclosure": isinstance(frequencies, dict)
        and interval(frequencies.get("positive")),
        "negative_frequency_enclosure": isinstance(frequencies, dict)
        and interval(frequencies.get("negative")),
        "signed_residual_interval": interval(data["signed_residual_bound"]),
        "rounding_allowance": interval(data["rounding_allowance"], nonnegative=True),
        "adaptive_tail_budget": interval(data["adaptive_tail_budget"], nonnegative=True),
        "gate_margin_lower_bound": interval(data["gate_margin"]),
    }
    return data, checks, None


def run(manifest: Path | None, output: Path) -> int:
    if manifest is None:
        return fail(output, None, "OWNER-DATA-MISSING", "No exact-owner certificate manifest was supplied.")
    if not manifest.is_file():
        return fail(output, manifest, "OWNER-DATA-MISSING", "The supplied manifest does not exist.")
    try:
        data, checks, error = validate(json.loads(manifest.read_text(encoding="utf-8")))
    except (OSError, json.JSONDecodeError) as exc:
        return fail(output, manifest, "OWNER-DATA-INVALID", str(exc))
    if error is not None or data is None:
        return fail(output, manifest, "OWNER-DATA-INVALID", error or "invalid manifest")
    structural_pass = all(checks.values())
    artifact = {
        "record": 3136,
        "status": "PASS" if structural_pass else "CONTROL-FAIL",
        "failure": None if structural_pass else "CERTIFICATE-CONTRACT-INVALID",
        "checks": checks,
        "certificate_status": "CERTIFICATE-READY" if structural_pass else "NOT-RUN",
        "numerical_gate_status": "NOT-EVALUATED",
        "decision": "Structural readiness is not a gate proof; require independent Lean readback and signed margin theorem.",
        "owner_id": data["owner_id"],
        "rho": data["rho"],
        "lambda": data["lambda"],
        "provenance": provenance(manifest),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 0 if structural_pass else 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--owner-data", type=Path)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    return run(args.owner_data, args.output)


if __name__ == "__main__":
    raise SystemExit(main())
