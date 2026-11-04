"""Replay the exact arithmetic of a 3314 decomposed block certificate."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def ceil_grid(value: F, places: int = 80) -> F:
    scale = 10**places
    numerator = value.numerator * scale
    return F(-((-numerator) // value.denominator), scale)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    certificate = json.loads(args.certificate.read_text(encoding="utf-8"))
    failures: list[str] = []
    rows = certificate["rows"]
    step = F(certificate["step"])
    if certificate.get("cells") != 256 or len(rows) != 256:
        failures.append("expected exactly 256 cells")
    recomputed_components = {name: F(0) for name in ("endpoint", "second", "fourth", "sixth")}
    recomputed_source = F(0)
    for offset, row in enumerate(rows):
        if row.get("offset") != offset:
            failures.append(f"offset {offset}: row index mismatch")
        inputs = {
            "endpoint": F(row["endpoint_upper"]),
            "second": F(row["second_upper"]),
            "fourth": F(row["fourth_upper"]),
            "sixth": F(row["sixth_upper"]),
        }
        for name in ("second", "fourth"):
            family_values = [F(value) for value in row[f"{name}_family_upper"]]
            if len(family_values) != 30:
                failures.append(f"offset {offset}: {name} family count mismatch")
            if sum(family_values, F(0)) != inputs[name]:
                failures.append(f"offset {offset}: {name} family sum mismatch")
        terms = {
            "endpoint": step * inputs["endpoint"],
            "second": step**3 * inputs["second"] / 24,
            "fourth": step**5 * inputs["fourth"] / 1920,
            "sixth": step**7 * inputs["sixth"] / 322560,
        }
        for name, term in terms.items():
            if term != F(row[f"{name}_term"]):
                failures.append(f"offset {offset}: {name} term mismatch")
        for name, term in terms.items():
            recomputed_components[name] += term
        recomputed_source += sum(terms.values(), F(0))
    for name, value in recomputed_components.items():
        if value != F(certificate["component_sums"][name]):
            failures.append(f"component {name}: sum mismatch")
    if recomputed_source != F(certificate["source"]):
        failures.append("source sum mismatch")
    if F(certificate["block_upper"]) != ceil_grid(recomputed_source):
        failures.append("block upper is not the exact upward rounding of source")
    if F(certificate["block_upper"]) < recomputed_source:
        failures.append("block upper is inward")
    if certificate.get("arb_enclosure_proved") is not False:
        failures.append("certificate must not claim Arb enclosure proof")
    result = {
        "record": 3314,
        "status": "REPLAY_3314_DECOMPOSED_BLOCK_CERTIFICATE",
        "block": certificate.get("block"),
        "cells": len(rows),
        "passed": not failures,
        "failures": failures,
        "arb_enclosure_proved": False,
        "rh_claim": False,
    }
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
