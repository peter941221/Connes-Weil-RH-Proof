#!/usr/bin/env python3
"""2132: extend the m=6400 Route-A tail read to locate the trust horizon."""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import routea_c3p_tail_probe_2062 as base  # noqa: E402

OUTPUT = ROOT / "results" / "2132_routea_tail_horizon_extension.json"


def main() -> None:
    rho, fam, xw, corr, support, prime_powers, solve_info = base.build_owner()
    bands = []
    for lo, hi in ((160.0, 180.0), (180.0, 200.0),
                   (200.0, 220.0), (220.0, 240.0)):
        bands.append(base.integrate_band(
            lo, hi, 0.01, fam, xw, corr, rho, prime_powers))
    total_abs = sum(row["absolute"] for row in bands)
    result = {
        "record": 2132,
        "status": "TAIL-HORIZON-EXTENSION-M6400",
        "phi_rule_m": base.PHI_RULE_M,
        "owner": "one-copy G8-H",
        "rho": [float(rho.real), float(rho.imag)],
        "scale": base.SCALE,
        "support": float(support),
        "book_size": len(prime_powers),
        "solve": solve_info,
        "bands": bands,
        "tail_160_to_240_absolute": total_abs,
        "tail_160_to_240_over_q1600": total_abs / 3.406049871881275e12,
        "nonclaims": [
            "measured tail only; not an interval enclosure",
            "no extrapolation beyond |xi| = 240",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "source_tail_probe": "scripts/routea_c3p_tail_probe_2062.py",
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
