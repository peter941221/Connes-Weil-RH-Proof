"""Validate exact coordinates, cell sums and provenance; not an analytic checker."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check(path):
    data = json.loads(path.read_text())
    assert data["record"] == 2535
    assert data["status"] == "EXTERNAL_WHOLE_CELL_ENCLOSURE_NOT_LEAN"
    source = ROOT / "scripts/routea_owner_whole_cell_2535.py"
    assert data["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    for name, digest in data["input_sha256"].items():
        assert (ROOT/name).resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest
    for flag in ("lean_certificate_imported", "exact_owner_transfer",
                 "complete_signed_kernel_priced", "producer_go", "rh_claim"):
        assert data[flag] is False
    assert [row["sigma_exact"] for row in data["endpoints"]] == ["-1/2", "1/2"]
    radius, pin = Fraction(data["radius_exact"]), Fraction(data["pin_exact"])
    assert radius == Fraction(65536001, 10000000)
    assert pin == Fraction("2.7790943782")
    count = 0
    for endpoint in data["endpoints"]:
        n = endpoint["cells"]
        h = 2*radius/n
        assert len(endpoint["rows"]) == n
        nodes, remainders = Fraction(0), Fraction(0)
        for i, row in enumerate(endpoint["rows"]):
            assert row["index"] == i
            assert Fraction(row["left_exact"]) == -radius+i*h
            assert Fraction(row["right_exact"]) == -radius+(i+1)*h
            node = Fraction(row["node_upper_exact"])
            rem = Fraction(row["remainder_upper_exact"])
            second = Fraction(row["second_upper_exact"])
            assert node >= 0 and second >= 0 and rem >= h**3/12*second
            nodes += node
            remainders += rem
            count += 1
        node_upper = Fraction(endpoint["node_upper_exact"])
        rem_upper = Fraction(endpoint["remainder_upper_exact"])
        total = Fraction(endpoint["total_upper_exact"])
        assert nodes <= node_upper and remainders <= rem_upper
        assert total == node_upper + rem_upper
        assert Fraction(endpoint["margin_lower_exact"]) == pin-total
        assert endpoint["fits_pin"] == (total < pin)
    assert data["all_fit"] == all(row["fits_pin"] for row in data["endpoints"])
    return {"status": "EXACT_PAYLOAD_CHECK_PASS", "cells_checked": count,
            "all_fit": data["all_fit"], "analytic_bounds_checked": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("path", type=Path, nargs="?", default=ROOT/"results/2535_whole_cell_enclosure.json")
    args = parser.parse_args()
    print(json.dumps(check(args.path)), flush=True)
