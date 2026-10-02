"""Source-level regression audit for the repaired geometry cache."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> dict:
    text = SOURCE.read_text()
    tree = ast.parse(text, filename=str(SOURCE))
    assignments = [node for node in ast.walk(tree)
                   if isinstance(node, ast.Assign)]
    margin = [node for node in assignments
              if any(isinstance(target, ast.Name) and
                     target.id == "GEOMETRY_CACHE_ULPS"
                     for target in node.targets)]
    require(len(margin) == 1, "cache margin must have one named assignment")
    require(isinstance(margin[0].value, ast.Constant) and
            margin[0].value.value == 4, "unexpected cache margin")
    require("def cache_lo(value):" in text and "def cache_hi(value):" in text,
            "directional cache helpers absent")
    require(text.count("cache_lo(") == 6 and text.count("cache_hi(") == 6,
            "not all five geometry lower/upper endpoints use cache helpers")
    require("np.nextafter(result, -np.inf)" in text and
            "np.nextafter(result, np.inf)" in text,
            "outward binary64 directions absent")
    require("PUBLIC_HULL_ULPS = 4" in text and
            "GEOMETRY_CACHE_ULPS = 4" in text,
            "public and cache margins are not separately named")
    result = {
        "record": 2427,
        "status": "GEOMETRY_CACHE_SOURCE_AUDIT_PASS",
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "geometry_cache_ulp_margin": 4,
        "public_hull_ulp_margin": 4,
        "all_five_geometry_endpoints_padded": True,
        "pointwise_mathematical_term_dominance_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2427_geometry_cache_source_audit.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
