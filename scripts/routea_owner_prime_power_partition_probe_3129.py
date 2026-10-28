#!/usr/bin/env python3
"""Record 3129: validate the owner partition contract and fail closed.

This probe checks only finite owner-data structure.  It does not evaluate a
sampled integral and never promotes a partition check to a continuum residual
certificate.  A complete owner manifest is required before any partition is
checked; absence is an explicit control failure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "results/3129_routea_owner_prime_power_partition_probe.json"
SCRIPT_RELATIVE = Path(__file__).resolve().relative_to(ROOT).as_posix()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def prime_power_base(value: int) -> int | None:
    if value < 2:
        return None
    remaining = value
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            while remaining % prime == 0:
                remaining //= prime
            return prime if remaining == 1 else None
        prime = 3 if prime == 2 else prime + 2
    return value if is_prime(value) else None


def provenance(owner_path: Path | None) -> dict[str, str | None]:
    return {
        "script": SCRIPT_RELATIVE,
        "script_sha256": sha256(Path(__file__).resolve()),
        "owner_manifest": owner_path.relative_to(ROOT).as_posix()
        if owner_path is not None and owner_path.is_relative_to(ROOT)
        else (str(owner_path) if owner_path is not None else None),
        "owner_manifest_sha256": sha256(owner_path)
        if owner_path is not None and owner_path.is_file()
        else None,
    }


def fail_closed(output: Path, owner_path: Path | None, failure: str, detail: str) -> int:
    artifact = {
        "record": 3129,
        "status": "CONTROL-FAIL",
        "failure": failure,
        "decision": "Do not evaluate the owner residual or claim a margin.",
        "detail": detail,
        "partition_status": "NOT-RUN",
        "residual_status": "UNPRICED",
        "continuum_status": "NOT-RUN",
        "provenance": provenance(owner_path),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(artifact, indent=2))
    return 2


def validate_manifest(data: object) -> tuple[dict[str, object] | None, str | None]:
    if not isinstance(data, dict):
        return None, "owner manifest must be a JSON object"
    required = {
        "owner_id",
        "owner_digest",
        "geometry_digest",
        "cutoff_exclusive",
        "global_prime_index_set",
        "route_a_visible_primes",
    }
    missing = sorted(required - data.keys())
    if missing:
        return None, "missing fields: " + ", ".join(missing)
    return data, None


def run(owner_path: Path | None, output: Path) -> int:
    if owner_path is None:
        return fail_closed(
            output,
            None,
            "OWNER-DATA-MISSING",
            "No actual globalPrimeIndexSet manifest was supplied.",
        )
    if not owner_path.is_file():
        return fail_closed(
            output,
            owner_path,
            "OWNER-DATA-MISSING",
            "The supplied actual-owner manifest does not exist.",
        )
    try:
        data, error = validate_manifest(json.loads(owner_path.read_text(encoding="utf-8")))
    except (OSError, json.JSONDecodeError) as exc:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", str(exc))
    if error is not None or data is None:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", error or "invalid manifest")

    owner_id = data["owner_id"]
    owner_digest = data["owner_digest"]
    geometry_digest = data["geometry_digest"]
    cutoff = data["cutoff_exclusive"]
    actual = data["global_prime_index_set"]
    visible = data["route_a_visible_primes"]
    if not isinstance(owner_id, str) or not owner_id:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "owner_id is empty")
    if not isinstance(owner_digest, str) or not owner_digest:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "owner_digest is empty")
    if not isinstance(geometry_digest, str) or not geometry_digest:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "geometry_digest is empty")
    if not isinstance(cutoff, int) or cutoff <= 0:
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "cutoff_exclusive must be positive")
    if not isinstance(actual, list) or not all(isinstance(value, int) for value in actual):
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "global_prime_index_set must be integer list")
    if not isinstance(visible, list) or not all(isinstance(value, int) for value in visible):
        return fail_closed(output, owner_path, "OWNER-DATA-INVALID", "route_a_visible_primes must be integer list")

    actual_set = set(actual)
    visible_set = set(visible)
    duplicate_actual = len(actual_set) != len(actual)
    duplicate_visible = len(visible_set) != len(visible)
    visible_nonprime = sorted(value for value in visible_set if not is_prime(value))
    actual_outside_cutoff = sorted(value for value in actual_set if value >= cutoff)
    actual_not_prime_power = sorted(value for value in actual_set if prime_power_base(value) is None)
    actual_base_not_visible = sorted(
        value
        for value in actual_set
        if prime_power_base(value) is not None and prime_power_base(value) not in visible_set
    )

    closure_within_cutoff: set[int] = set()
    for prime in visible_set:
        if not is_prime(prime):
            continue
        power = prime
        while power < cutoff:
            closure_within_cutoff.add(power)
            power *= prime
    actual_missing_within_cutoff = sorted(closure_within_cutoff - actual_set)
    actual_extra_not_in_closure = sorted(actual_set - closure_within_cutoff)

    checks = {
        "owner_identity_present": bool(owner_id and owner_digest and geometry_digest),
        "visible_primes_are_prime": not visible_nonprime,
        "actual_indices_are_prime_powers": not actual_not_prime_power,
        "actual_indices_inside_cutoff": not actual_outside_cutoff,
        "actual_indices_have_visible_prime_base": not actual_base_not_visible,
        "actual_indices_unique": not duplicate_actual,
        "visible_primes_unique": not duplicate_visible,
        "actual_indices_subset_computed_closure": not actual_extra_not_in_closure,
    }
    structural_pass = all(checks.values())
    failure = None if structural_pass else "OWNER-PARTITION-INVALID"
    if structural_pass:
        failure = "CONTINUUM-CERTIFICATE-MISSING"
    artifact = {
        "record": 3129,
        "status": "CONTROL-FAIL",
        "failure": failure,
        "decision": "Do not claim a signed residual margin from this partition-only probe.",
        "owner_id": owner_id,
        "cutoff_exclusive": cutoff,
        "counts": {
            "actual_owner": len(actual_set),
            "route_a_visible_primes": len(visible_set),
            "closure_within_cutoff": len(closure_within_cutoff),
            "missing_within_cutoff": len(actual_missing_within_cutoff),
        },
        "checks": checks,
        "violations": {
            "visible_nonprime": visible_nonprime,
            "actual_outside_cutoff": actual_outside_cutoff,
            "actual_not_prime_power": actual_not_prime_power,
            "actual_base_not_visible": actual_base_not_visible,
            "actual_extra_not_in_closure": actual_extra_not_in_closure,
        },
        "partition_status": "PASS" if structural_pass else "FAIL",
        "residual_status": "UNPRICED",
        "continuum_status": "MISSING",
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
