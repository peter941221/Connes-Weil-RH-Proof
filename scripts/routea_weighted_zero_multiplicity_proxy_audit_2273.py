#!/usr/bin/env python3
"""Audit the rounding direction of the Route A multiplicity proxy.

This is an independent high-precision diagnostic. It does not certify the
Lean inequality; it detects whether the decimal proxy is even on the safe
side before formal bounds are attempted.
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
    xi_two = pi / 6
    exact = (fixed + 1 + abs(mp.log(xi_two)) + 72) / mp.log(2)
    old_proxy = mp.mpf("128.70692502980964")
    corrected_proxy = mp.mpf("128.70692502981")
    result = {
        "record": 2273,
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
            "completedRiemannXi(2) = pi/6; "
            "the identity is not proved by this diagnostic"
        ),
        "values": {
            "kernel_tail": mp.nstr(tail, 90),
            "kernel_small_moment": mp.nstr(small, 90),
            "xi_growth_fixed": mp.nstr(fixed, 90),
            "completed_xi_two": mp.nstr(xi_two, 90),
            "spectral_multiplicity": mp.nstr(exact, 90),
            "old_proxy": mp.nstr(old_proxy, 90),
            "corrected_proxy": mp.nstr(corrected_proxy, 90),
            "old_proxy_minus_exact": mp.nstr(old_proxy - exact, 90),
            "corrected_proxy_minus_exact": mp.nstr(corrected_proxy - exact, 90),
        },
        "status": ("OLD-PROXY-UNDER-ROUNDS" if old_proxy < exact
                   and corrected_proxy > exact else "AUDIT-REQUIRES-REVIEW"),
        "nonclaims": [
            "This is an independent high-precision rounding audit, not a Lean proof.",
            "The corrected proxy still requires formal analytic upper bounds before hmult is closed.",
            "No producer GO, no gate sign change, no RH claim.",
        ],
    }
    return result


def main():
    result = compute_audit()
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                      newline="\n")
    print(json.dumps({"status": result["status"], **result["values"]}, indent=2))
    if result["status"] != "OLD-PROXY-UNDER-ROUNDS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
