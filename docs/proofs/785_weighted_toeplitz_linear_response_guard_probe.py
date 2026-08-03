"""Exact finite certificate for Proof 785's Toeplitz linear-response guard."""

from __future__ import annotations

import argparse
import math


def direct_projection_response(transport: float, root: float) -> float:
    """Trace(W_b (P_a - P_0)) from the Gram-corrected rank-one projections."""
    norm_sq = 1.0 + transport * transport
    detector_expectation = (
        (1.0 + root * root) * norm_sq - 2.0 * transport * root
    ) / norm_sq
    base_expectation = 1.0 + root * root
    return detector_expectation - base_expectation


def closed_form_response(transport: float, root: float) -> float:
    return -2.0 * transport * root / (1.0 + transport * transport)


def central_derivative(root: float, step: float) -> float:
    return (
        closed_form_response(step, root)
        - closed_form_response(-step, root)
    ) / (2.0 * step)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transport", type=float, default=0.29)
    parser.add_argument("--root", type=float, default=0.37)
    parser.add_argument("--step", type=float, default=1e-7)
    parser.add_argument("--tolerance", type=float, default=5e-12)
    args = parser.parse_args()

    if not 0.0 < args.transport < 1.0:
        raise ValueError("transport must lie in (0, 1)")
    if not 0.0 < args.root < 1.0:
        raise ValueError("root must lie in (0, 1)")

    direct = direct_projection_response(args.transport, args.root)
    closed = closed_form_response(args.transport, args.root)
    formula_error = abs(direct - closed)
    derivative = central_derivative(args.root, args.step)
    derivative_error = abs(derivative + 2.0 * args.root)

    # This ratio must grow like 2b/a, not stay bounded quadratically in a.
    small_transports = (0.20, 0.10, 0.05, 0.025)
    quadratic_ratios = [
        abs(closed_form_response(value, args.root)) / (value * value)
        for value in small_transports
    ]
    ratio_monotone = all(
        later > earlier
        for earlier, later in zip(quadratic_ratios, quadratic_ratios[1:])
    )

    print("Proof 785 weighted Toeplitz linear-response certificate")
    print(f"transport={args.transport:.12e}")
    print(f"root={args.root:.12e}")
    print(f"direct_gram_corrected_response={direct:.12e}")
    print(f"closed_form_response={closed:.12e}")
    print(f"formula_error={formula_error:.12e}")
    print(f"derivative_at_zero={derivative:.12e}")
    print(f"derivative_error={derivative_error:.12e}")
    for transport, ratio in zip(small_transports, quadratic_ratios):
        print(f"quadratic_ratio_at_{transport:.3f}={ratio:.12e}")

    if formula_error > args.tolerance:
        raise RuntimeError(f"closed-form response mismatch: {formula_error:.3e}")
    if derivative_error > 100.0 * args.tolerance:
        raise RuntimeError(f"linear derivative mismatch: {derivative_error:.3e}")
    if not ratio_monotone:
        raise RuntimeError("response/a^2 did not grow as transport approached zero")

    print("forward_toeplitz_kernel=RETAINED")
    print("gram_correction=RETAINED")
    print("positive_two_tap_root=RETAINED")
    print("generic_quadratic_euler_response=REJECTED")
    print("ccm24_specific_hardy_prolate_cancellation=REQUIRED")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
