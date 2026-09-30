#!/usr/bin/env python3
"""Audit the rounding direction of the Route A multiplicity proxy.

Record 2274 corrects the project's doubled-xi normalization. The original
record-2273 pi/6 diagnostic is retained separately as superseded evidence.
This computation does not supply the independently checked Lean proof.
"""
import hashlib
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results/2273_multiplicity_proxy_audit.json"
SOURCES = (
    "ConnesWeilRH/Dev/C1SpectralSummability.lean",
    "ConnesWeilRH/Source/CC20ZetaCounting.lean",
    "ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean",
    "ConnesWeilRH/Dev/C1RouteAMultiplicityBound.lean",
)


def compute_audit(precision_digits=100):
    if precision_digits < 40:
        raise ValueError("The rounding diagnostic requires at least 40 digits")
    with mp.workdps(precision_digits):
        return _compute_audit(precision_digits)


def _compute_audit(precision_digits):
    pi = mp.pi
    tail = 2 / (1 - mp.exp(-pi))
    small = (1 / pi) ** (mp.mpf(1) / 4) * mp.gamma(mp.mpf(1) / 4)
    fixed = 2 * tail * (small + 1)
    xi_two = pi / 3
    value = (fixed + 1 + abs(mp.log(xi_two)) + 72) / mp.log(2)
    historical_standard_value = (fixed + 1 + abs(mp.log(pi / 6)) + 72) / mp.log(2)
    old_proxy = mp.mpf("128.70692502980964")
    corrected_proxy = mp.mpf("128.70692502981")
    result = {
        "record": 2273,
        "correction_record": 2274,
        "precision_digits": precision_digits,
        "mpmath_version": mp.__version__,
        "source_hash_convention": "UTF-8 text with LF line endings",
        "source_sha256": {
            source: hashlib.sha256(
                (ROOT / source).read_text(encoding="utf-8").encode("utf-8")
            ).hexdigest()
            for source in SOURCES
        },
        "xi_two_convention": (
            "completedRiemannXi(2) = pi/3; "
            "proved separately in C1RouteAMultiplicityBound.lean"
        ),
        "values": {
            "kernel_tail": mp.nstr(tail, 90),
            "kernel_small_moment": mp.nstr(small, 90),
            "xi_growth_fixed": mp.nstr(fixed, 90),
            "completed_xi_two": mp.nstr(xi_two, 90),
            "spectral_multiplicity": mp.nstr(value, 90),
            "historical_standard_multiplicity": mp.nstr(historical_standard_value, 90),
            "old_proxy": mp.nstr(old_proxy, 90),
            "corrected_proxy": mp.nstr(corrected_proxy, 90),
            "old_proxy_minus_value": mp.nstr(old_proxy - value, 90),
            "corrected_proxy_minus_value": mp.nstr(corrected_proxy - value, 90),
        },
        "status": ("BOTH-PROXIES-COVER-PROJECT-NORMALIZATION"
                   if value < old_proxy < corrected_proxy and value < mp.mpf("128.65")
                   else "AUDIT-REQUIRES-REVIEW"),
        "nonclaims": [
            "This is an independent high-precision rounding audit, not a Lean proof.",
            "Lean proves hmult separately; this diagnostic supplies no analytic certificate.",
            "No producer GO, no gate sign change, no RH claim.",
        ],
    }
    return result


def main():
    result = compute_audit()
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"status": result["status"], **result["values"]}, indent=2))
    if result["status"] != "BOTH-PROXIES-COVER-PROJECT-NORMALIZATION":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
