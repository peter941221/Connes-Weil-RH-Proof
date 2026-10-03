"""Validate the structural invariants of the 2530 node payload.

This checker does not certify transcendental evaluations. It verifies source
hashes, exact grid coordinates, node counts, binary-rational ordering, and
that the stored trapezoid replay stays below the frozen base endpoint pin.
"""
from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = ROOT / "results/2530_signed_node_center_error_payload.json"
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
BASE_PIN = Fraction(27790943782, 10_000_000_000)
RADIUS = Fraction(65536001, 10_000_000)
CELLS = 2560
STEP = RADIUS / 1280


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac(text: str) -> Fraction:
    a, b = text.split("/")
    return Fraction(int(a), int(b))


def main() -> None:
    payload = json.loads(PAYLOAD.read_text())
    assert payload["record"] == 2530
    assert payload["cells"] == CELLS
    assert payload["node_count"] == CELLS + 1
    assert payload["repair_sha256"] == sha256(REPAIR)
    assert payload["capture_sha256"] == sha256(CAPTURE)
    for sigma, row in payload["signs"].items():
        nodes = row["nodes"]
        assert len(nodes) == CELLS + 1
        for index, node in enumerate(nodes):
            assert node["index"] == index
            x = frac(node["x_exact"])
            expected_x = -RADIUS + index * STEP
            assert x == expected_x, (sigma, index, x, expected_x)
            upper = frac(node["weighted_upper_binary_rational"])
            assert upper > 0
            assert float(upper) >= float(node["weighted_upper"])
        total = Fraction(0)
        for index in range(CELLS):
            left = frac(nodes[index]["weighted_upper_binary_rational"])
            right = frac(nodes[index + 1]["weighted_upper_binary_rational"])
            total += STEP * (left + right) / 2
        stored = Fraction.from_float(row["node_sum_binary_float"])
        assert float(total) == row["node_sum_binary_float"]
        assert total < BASE_PIN, (sigma, float(total), float(BASE_PIN))
        print(sigma, "nodes=PASS", "sum=", float(total), "margin=", float(BASE_PIN - total))
    print("2530 payload structural checks: PASS")


if __name__ == "__main__":
    main()

