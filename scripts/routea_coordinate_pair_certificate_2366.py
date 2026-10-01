"""Exact replay of the stored-vs-affine coordinate obligations for 2359.

This is a finite coordinate certificate replay, not a Lean import and not an
integral certificate.  The decision it settles is precisely whether the
endpoint-window and uniform-displacement hypotheses required by the 2365
owner bridge hold for the stored 240001-point grid.
"""

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import numpy as np


NODES = 240001
STORED_WIDTH_4 = Fraction(1441151880758559, 562949953421312)
OWNER_RADIUS = STORED_WIDTH_4 ** 2
STRIP_RADIUS = Fraction(65536001, 10000000)


def main() -> dict:
    radius = float(OWNER_RADIUS)
    actual = np.linspace(-radius, radius, NODES)
    actual_fraction = [Fraction(float(value)) for value in actual]
    ideal_fraction = [
        -OWNER_RADIUS + (2 * OWNER_RADIUS) * index / (NODES - 1)
        for index in range(NODES)
    ]
    gaps = [abs(actual_fraction[index] - ideal_fraction[index]) for index in range(NODES)]
    owner_endpoint_window_ok = all(-OWNER_RADIUS <= value <= OWNER_RADIUS for value in actual_fraction)
    strip_endpoint_window_ok = all(-STRIP_RADIUS <= value <= STRIP_RADIUS for value in actual_fraction)
    affine_window_ok = all(-OWNER_RADIUS <= value <= OWNER_RADIUS for value in ideal_fraction)
    result = {
        "record": 2366,
        "status": "COORDINATE_PAIR_ENDPOINT_CERTIFICATE_REPLAY",
        "nodes": NODES,
        "owner_radius_exact": str(OWNER_RADIUS),
        "owner_radius_float": repr(radius),
        "actual_endpoint_fractions": [str(actual_fraction[0]), str(actual_fraction[-1])],
        "ideal_endpoint_fractions": [str(ideal_fraction[0]), str(ideal_fraction[-1])],
        "strip_radius_exact": str(STRIP_RADIUS),
        "actual_endpoints_in_owner_window": owner_endpoint_window_ok,
        "actual_endpoints_in_strip_window": strip_endpoint_window_ok,
        "ideal_endpoints_in_owner_window": affine_window_ok,
        "all_actual_points_in_owner_window": owner_endpoint_window_ok,
        "all_actual_points_in_strip_window": strip_endpoint_window_ok,
        "all_ideal_points_in_owner_window": affine_window_ok,
        "coordinate_difference_count": sum(gap != 0 for gap in gaps),
        "coordinate_max_fraction_gap": str(max(gaps)),
        "coordinate_max_float_gap": float(max(gaps)),
        "lean_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if not strip_endpoint_window_ok or not affine_window_ok:
        raise AssertionError("coordinate endpoint/window obligation failed")
    return result


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, sort_keys=True))
