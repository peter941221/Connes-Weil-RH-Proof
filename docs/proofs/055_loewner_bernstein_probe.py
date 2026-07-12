#!/usr/bin/env python3
"""Reject an operator-monotone explanation of the finite Weil matrices.

For the odd divided-difference source psi, the positive-frequency even block
is twice the Loewner kernel of Phi(x)=sqrt(x)psi(sqrt(x)) on squared nodes.
Arb checks that identity off diagonal and certifies Phi(1/4)>Phi(1), which is
incompatible with scalar monotonicity and hence with complete Bernstein or
operator-monotone structure.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def total_source_at(upstream, c: int, t, prec: int):
    """The odd source whose divided-difference matrix is W02-WR-Wp."""
    from flint import arb, acb

    log_c = arb(c).log()
    pi = arb.pi()
    frequency = 2 * pi * t / log_c
    geometric_s, _, _, _ = upstream._geom_sums(t, log_c, prec)
    digamma_argument = acb(arb("0.25"), pi * t / log_c)
    source_s = (
        arb("0.5") * digamma_argument.digamma().imag
        - frequency * geometric_s
    )

    prime_source = arb(0)
    for prime_power, prime in upstream.prime_powers_up_to(c):
        weight = arb(prime).log() * (arb(prime_power) ** arb("-0.5"))
        phase = 2 * pi * t * arb(prime_power).log() / log_c
        prime_source += weight * phase.sin()

    beta_squared = (log_c / (4 * pi)) ** 2
    pole_constant = (
        log_c
        * (arb(c).sqrt() + arb(1) / arb(c).sqrt() - 2)
        / (2 * pi * pi)
    )
    pole_source = pole_constant * t / (t * t + beta_squared)
    return pole_source + (source_s + prime_source) / pi


def phi_at(upstream, c: int, t, prec: int):
    """Evaluate Phi(t^2)=t*psi(t) for positive t."""
    return t * total_source_at(upstream, c, t, prec)


def even_positive_entry(matrix, N: int, left: int, right: int):
    """Contract the full +/- frequency matrix against even basis vectors."""
    from flint import arb

    inverse_two = arb(1) / 2
    indices_left = (N - left, N + left)
    indices_right = (N - right, N + right)
    result = arb(0)
    for row in indices_left:
        for column in indices_right:
            result += inverse_two * matrix[row, column]
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=4)
    parser.add_argument("--prec", type=int, default=512)
    args = parser.parse_args()

    from flint import arb, ctx

    if args.N < 2:
        raise ValueError("N must be at least 2")
    ctx.prec = args.prec
    upstream = load_module("arb_ldlt_upstream", args.upstream)
    matrix, _ = upstream.build_arb_tau(args.c, args.N, args.prec)

    checked_entries = 0
    for left in range(1, args.N + 1):
        phi_left = phi_at(upstream, args.c, arb(left), args.prec)
        for right in range(left + 1, args.N + 1):
            phi_right = phi_at(upstream, args.c, arb(right), args.prec)
            expected = (
                2
                * (phi_left - phi_right)
                / arb(left * left - right * right)
            )
            actual = even_positive_entry(matrix, args.N, left, right)
            if not (actual - expected).contains(0):
                raise AssertionError(
                    f"Loewner identity mismatch at ({left},{right}): "
                    f"actual={actual}, expected={expected}"
                )
            checked_entries += 1

    phi_quarter = phi_at(upstream, args.c, arb("0.5"), args.prec)
    phi_one = phi_at(upstream, args.c, arb(1), args.prec)
    decrease = phi_quarter - phi_one
    secant = (phi_one - phi_quarter) / arb("0.75")

    print(
        f"c={args.c} N={args.N} Arb_bits={args.prec} "
        f"loewner_offdiagonal_entries_checked={checked_entries}"
    )
    print(f"Phi(1/4)={phi_quarter.str(25)}")
    print(f"Phi(1)={phi_one.str(25)}")
    print(f"Phi(1/4)-Phi(1)={decrease.str(25)}")
    print(f"secant_[1/4,1]={secant.str(25)}")

    if not decrease > 0:
        raise AssertionError("expected a certified violation of monotonicity")
    if not secant < 0:
        raise AssertionError("expected a certified negative secant slope")
    print("operator_monotone_complete_bernstein_route=rejected")


if __name__ == "__main__":
    main()
