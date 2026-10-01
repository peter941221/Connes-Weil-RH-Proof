"""Runtime control for the MPFR-to-binary64 directed term conversion.

The control reuses the 2359 worker without editing it, intercepting only the
point-term ``get_d(RNDU)`` conversion on a 1001-node sequential run.  It
checks the corresponding RNDD/RNDU conversion pair for every channel term.
This is a conversion control, not a proof of the interval evaluator's
mathematical enclosure theorem.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> dict:
    artifact = json.loads(
        (ROOT / "results/2385_shared_geometry_776611.json").read_text())
    worker_path = ROOT / "scripts/routea_nodal_interval_fullgrid_2359.py"
    evaluator_path = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"
    require(artifact["source_sha256"] == sha256(worker_path),
            "2359 source hash mismatch")
    require(artifact["evaluator_source_sha256"] == sha256(evaluator_path),
            "2242 evaluator source hash mismatch")

    nodal = load("nodal_conversion_control_2396", worker_path)
    original_load = nodal.load
    interval = original_load("interval_conversion_control_2396",
                             evaluator_path.name)
    strip = original_load("strip_conversion_control_2396",
                          "routea_corrected_strip_envelope_2303.py")
    captured: list[tuple[float, float]] = []
    original_get_d = interval.M.get_d

    def capture_get_d(self, rounding):
        value = original_get_d(self, rounding)
        point_term = getattr(nodal, "_WORKER_POINT_TERM", None)
        if point_term is self and rounding == interval.RNDU:
            lower = original_get_d(self, interval.RNDD)
            captured.append((lower, value))
        return value

    interval.M.get_d = capture_get_d

    def controlled_load(name: str, filename: str):
        if filename == evaluator_path.name:
            return interval
        if filename == "routea_corrected_strip_envelope_2303.py":
            return strip
        return original_load(name, filename)

    nodal.load = controlled_load
    families, _base, _correction, _ = strip.load_owner()
    radius = max(a * a for a, _theta in families)
    nodes = 1001
    nodal.worker_span((0, nodes, nodes, -0.5, radius, False))

    expected = nodes * 4
    require(len(captured) == expected,
            f"captured {len(captured)} terms, expected {expected}")
    require(all(math.isfinite(lo) and math.isfinite(hi)
                and lo >= 0 and hi >= lo for lo, hi in captured),
            "invalid directed conversion pair")
    result = {
        "record": 2396,
        "status": "DIRECTED_TERM_CONVERSION_CONTROL_PASS",
        "source_hashes_match": True,
        "nodes": nodes,
        "channels": 4,
        "captured_terms": len(captured),
        "expected_terms": expected,
        "all_rndu_ge_rndd": True,
        "all_terms_finite_nonnegative": True,
        "lean_numeric_imported": False,
        "numeric_term_dominance_theorem_proved": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2396_directed_term_conversion_control.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
