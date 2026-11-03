"""3298: diagnostic tight-tail and real-projection endpoint probe.

This is still external Decimal evidence.  It tests the proposed repair for the
3289 rectangle loss: use a t-dependent scaled Taylor tail and project each
complex family to a real interval before summing.  No result is imported into
Lean.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from pathlib import Path

import routea_rational_endpoint_decimal_probe_3297 as base


ROOT = Path(__file__).resolve().parents[1]


def improved_bump_interval(radius: Decimal, position: Decimal) -> base.Interval:
    if not position < radius:
        return Decimal(0), Decimal(0)
    t = Decimal(30) - Decimal(30) / (Decimal(1) - (position / radius) ** 2)
    base_interval = base.interval_pow(
        base.rational_taylor_interval(Decimal(-1) / Decimal(2)), 60
    )
    if abs(t / Decimal(8)) <= Decimal(1):
        return base.interval_mul(
            base_interval,
            base.interval_pow(base.rational_taylor_interval(t / Decimal(8)), 8),
        )
    for denominator, cutoff in (
        (16, Decimal(-16)),
        (32, Decimal(-32)),
        (64, Decimal(-64)),
    ):
        if t >= cutoff:
            return base.interval_mul(
                base_interval,
                base.interval_pow(
                    base.rational_taylor_interval(t / Decimal(denominator)),
                    denominator,
                ),
            )
    # The remaining tail is bounded by exp(-94).  The lower endpoint is zero;
    # this branch is only used where the omitted negative contribution is tiny.
    return Decimal(0), Decimal(-94).exp()


def real_endpoint(
    index: int,
    modulations: list,
    widths: list,
    coefficients: list,
) -> Decimal:
    x = base.dfrac(base.center(index))
    aggregate: base.Interval = (Decimal(0), Decimal(0))
    for modulation, width, coefficient in zip(modulations, widths, coefficients):
        bump = improved_bump_interval(base.dfrac(width) ** 2, abs(x))
        phase = base.phase_pow(base.dfrac(modulation) * x)
        coefficient_re = base.dfrac(coefficient[0])
        coefficient_im = base.dfrac(coefficient[1])
        phase_re = (
            coefficient_re * phase[0] - coefficient_im * phase[3],
            coefficient_re * phase[1] - coefficient_im * phase[2],
        )
        aggregate = base.interval_add(
            aggregate,
            base.interval_mul(bump, phase_re),
        )
    weight = base.interval_pow(
        base.rational_taylor_interval(-x / Decimal(120)), 60
    )
    return base.interval_mul(weight, aggregate)[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--indices",
        type=int,
        nargs="+",
        default=[8192, 12000, 15000, 16000, 16500, 16923, 30000, 40959],
    )
    parser.add_argument("--precision", type=int, default=80)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results/3298_routea_tight_real_endpoint_probe.json",
    )
    args = parser.parse_args()

    with localcontext() as context:
        context.prec = args.precision
        modulations = base.parse_modulations()
        widths = base.parse_widths()
        coefficients = base.parse_coefficients()
        rows = []
        for index in args.indices:
            endpoint = real_endpoint(index, modulations, widths, coefficients)
            arb_upper = base.parse_sidecar(index)
            rows.append(
                {
                    "index": index,
                    "tight_real_endpoint_decimal_probe": str(endpoint),
                    "arb_value_upper": str(arb_upper),
                    "endpoint_minus_arb": str(endpoint - arb_upper),
                    "diagnostic_dominates": endpoint >= arb_upper,
                }
            )

    result = {
        "record": 3298,
        "status": "DIAGNOSTIC_TIGHT_TAIL_REAL_PROJECTION_NOT_CERTIFIED",
        "precision_digits": args.precision,
        "rows": rows,
        "lean_imported": False,
        "exact_rational_replay": False,
        "producer_go": False,
        "rh_claim": False,
        "nonclaims": [
            "Decimal arithmetic is not directed rounding",
            "rows do not prove endpoint dominance",
            "rows do not prove any Lean theorem",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
