"""Fail-closed audit for the Route-A same-owner producer boundary.

This audit inventories evidence; it does not promote numerical payloads into
a Lean certificate. A producer is admissible only when the same owner carries
the signed two-frequency kernel, complete tail, exact support, and a certified
negative aggregate margin after all errors.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> tuple[dict[str, Any], str]:
    raw = path.read_bytes()
    return json.loads(raw.decode("utf-8")), hashlib.sha256(raw).hexdigest()


def flag(payload: dict[str, Any], key: str) -> bool:
    return payload.get(key) is True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3176_routea_same_owner_budget_audit.json",
    )
    args = parser.parse_args()

    paths = {
        "legacy_interval": ROOT / "results/2038_route_a_one_copy_interval_certificate_audit.json",
        "whole_cell": ROOT / "results/2535_whole_cell_enclosure.json",
        "signed_aggregate": ROOT / "results/2539_signed_aggregate_validation.json",
        "tail_supplier": ROOT / "results/2353_same_owner_tail_supplier.json",
    }
    payloads: dict[str, dict[str, Any]] = {}
    hashes: dict[str, str] = {}
    missing = []
    for name, path in paths.items():
        if not path.exists():
            missing.append(str(path.relative_to(ROOT)))
            continue
        payloads[name], hashes[str(path.relative_to(ROOT))] = load_json(path)

    checks = {
        "same_owner_identity": False,
        "signed_plus_and_minus_frequency": False,
        "exact_visible_prime_support": False,
        "source_transform_closed": False,
        "signed_kernel_closed": False,
        "coefficient_enclosure_closed": False,
        "finite_window_error_closed": False,
        "full_line_tail_closed": False,
        "negative_aggregate_margin_closed": False,
        "lean_numeric_certificate_imported": False,
    }
    reasons: list[str] = []

    if missing:
        reasons.append("missing input artifacts: " + ", ".join(missing))
    else:
        legacy = payloads["legacy_interval"]
        whole_cell = payloads["whole_cell"]
        signed = payloads["signed_aggregate"]
        tail = payloads["tail_supplier"]

        owner = legacy.get("owner")
        checks["same_owner_identity"] = owner is not None and owner == "G8-H"
        if not checks["same_owner_identity"]:
            reasons.append("no current artifact proves one exact OrbitG8Geometry owner")

        checks["signed_plus_and_minus_frequency"] = (
            "signed" in str(legacy.get("certificate_target", "")).lower()
            and legacy.get("basis") != "positive-part"
        )
        if not checks["signed_plus_and_minus_frequency"]:
            reasons.append("the legacy payload does not certify both signed frequency contributions")

        checks["exact_visible_prime_support"] = flag(whole_cell, "exact_owner_transfer")
        if not checks["exact_visible_prime_support"]:
            reasons.append("exact owner/support transfer is not certified")

        components = legacy.get("certificate_components", {})
        checks["source_transform_closed"] = components.get("source_transform_interval") == "CLOSED"
        checks["signed_kernel_closed"] = components.get("signed_kernel_interval") == "CLOSED"
        checks["coefficient_enclosure_closed"] = (
            components.get("h1_coefficient_solve_interval") == "CLOSED"
        )
        checks["finite_window_error_closed"] = (
            components.get("finite_window_quadrature_error") == "CLOSED"
        )
        checks["full_line_tail_closed"] = components.get("full_line_tail_bound") == "CLOSED"

        if not checks["source_transform_closed"]:
            reasons.append("source-transform enclosure is not closed")
        if not checks["signed_kernel_closed"]:
            reasons.append("signed physical-kernel enclosure is not closed")
        if not checks["coefficient_enclosure_closed"]:
            reasons.append("coefficient enclosure is not closed")
        if not checks["finite_window_error_closed"]:
            reasons.append("finite-window quadrature error is not closed")
        if not checks["full_line_tail_closed"]:
            reasons.append("full-line tail bound is missing or not closed")

        checks["negative_aggregate_margin_closed"] = (
            flag(whole_cell, "all_fit")
            and flag(whole_cell, "complete_signed_kernel_priced")
            and flag(signed, "lean_numeric_certificate")
            and tail.get("full_signed_kernel_priced") is True
        )
        if not checks["negative_aggregate_margin_closed"]:
            reasons.append("no certified negative aggregate margin survives all error terms")

        checks["lean_numeric_certificate_imported"] = (
            flag(whole_cell, "lean_certificate_imported")
            and flag(signed, "lean_numeric_certificate")
            and tail.get("tail_supplier_imported_in_lean") is True
        )
        if not checks["lean_numeric_certificate_imported"]:
            reasons.append("numeric evidence has not been imported as a Lean certificate")

    status = "GO_TO_LEAN_PRODUCER" if all(checks.values()) and not missing else "STOP_MISSING_PRODUCER_PREMISE"
    result = {
        "record": 3176,
        "status": status,
        "checks": checks,
        "blocking_reasons": reasons,
        "input_sha256": hashes,
        "scope": "same-owner Route-A producer evidence gate; no SourceRH or RH claim",
        "producer_go": status == "GO_TO_LEAN_PRODUCER",
        "rh_claim": False,
        "next_admissible_artifact": (
            "same-owner signed integrand certificate with exact support and full-line tail"
        ),
        "source_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
