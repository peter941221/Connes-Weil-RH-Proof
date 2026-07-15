#!/usr/bin/env python3
"""Certificate for the fixed-S trace-class gate.

The matrix layer checks the identities used to pull a transported projection
crossing back to its base crossing.  It also checks the inverse-commutator
identity which transports a trace-class root commutator through a compressed
metric inverse.

The scalar layer compares the fixed-S prime-power crossing majorant with its
closed geometric formula.  The certificate proves finite-dimensional algebra
and scalar summability only.  CC20's trace-class commutator theorem and the
continuous finite-interval crossing factorization supply the operator-ideal
inputs in the accompanying proof.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def relative_error(actual: complex | np.ndarray, expected: complex | np.ndarray) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1e-15)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def cyclic_shift(size: int, amount: int) -> np.ndarray:
    identity = np.eye(size, dtype=complex)
    return np.roll(identity, amount, axis=0)


def coordinate_projection(size: int, rank: int) -> np.ndarray:
    if not 0 < rank < size:
        raise ValueError("projection rank must lie strictly between zero and size")
    projection = np.zeros((size, size), dtype=complex)
    indices = np.arange(rank)
    projection[indices, indices] = 1.0
    return projection


def circulant_root(size: int) -> np.ndarray:
    kernel = np.zeros(size, dtype=complex)
    kernel[0] = 1.0
    kernel[1] = 0.3 - 0.1j
    kernel[-1] = -0.2 + 0.15j
    return np.column_stack([np.roll(kernel, column) for column in range(size)])


def transported_projection_data(
    source_projection: np.ndarray,
    transport: np.ndarray,
    generator: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    identity = np.eye(source_projection.shape[0], dtype=complex)
    metric = transport.conj().T @ transport
    extended_compression = (
        source_projection @ metric @ source_projection
        + identity
        - source_projection
    )
    compressed_inverse = np.linalg.inv(extended_compression)
    transported_projection = (
        transport
        @ source_projection
        @ compressed_inverse
        @ source_projection
        @ transport.conj().T
    )
    current_crossing = (
        (identity - transported_projection)
        @ generator
        @ transported_projection
    )
    pulled_crossing = (
        (identity - transported_projection)
        @ transport
        @ (identity - source_projection)
        @ generator
        @ source_projection
        @ compressed_inverse
        @ source_projection
        @ transport.conj().T
    )
    return (
        extended_compression,
        compressed_inverse,
        transported_projection,
        current_crossing,
        pulled_crossing,
    )


def transported_crossing_certificate(
    size: int,
    time: float,
) -> dict[str, float]:
    if size < 8 or size % 4:
        raise ValueError("size must be divisible by four and at least eight")
    if not 0.0 <= time <= 1.0:
        raise ValueError("time must lie in [0,1]")

    identity = np.eye(size, dtype=complex)
    shifts = (cyclic_shift(size, 1), cyclic_shift(size, 3))
    weights = (1.0 / math.sqrt(2.0), 1.0 / math.sqrt(3.0))

    factors = [identity - time * weight * shift for weight, shift in zip(weights, shifts)]
    transport = factors[0] @ factors[1]
    transport_derivative = (
        (-weights[0] * shifts[0]) @ factors[1]
        + factors[0] @ (-weights[1] * shifts[1])
    )
    generator = transport_derivative @ np.linalg.inv(transport)

    outer_projection = coordinate_projection(size, 3 * size // 4)
    inner_projection = coordinate_projection(size, size // 4)
    root = circulant_root(size)

    outer_data = transported_projection_data(
        outer_projection, transport, generator
    )
    inner_data = transported_projection_data(
        inner_projection, transport, generator
    )
    (
        outer_compression,
        outer_inverse,
        transported_outer,
        outer_crossing,
        pulled_outer_crossing,
    ) = outer_data
    (
        inner_compression,
        inner_inverse,
        transported_inner,
        inner_crossing,
        pulled_inner_crossing,
    ) = inner_data

    transported_band = transported_outer - transported_inner
    lower_flow = (
        (identity - transported_outer) @ generator @ transported_band
        - transported_inner @ generator.conj().T @ transported_band
    )
    crossing_flow = (
        outer_crossing - inner_crossing.conj().T
    ) @ transported_band
    band_derivative = (
        outer_crossing
        + outer_crossing.conj().T
        - inner_crossing
        - inner_crossing.conj().T
    )
    detector = root.conj().T @ root
    real_generator = 0.5 * (generator + generator.conj().T)
    direct_trace = np.trace(root @ band_derivative @ root.conj().T)
    dirichlet_trace = np.trace(
        commutator(detector, transported_outer).conj().T
        @ commutator(real_generator, transported_outer)
    ) - np.trace(
        commutator(detector, transported_inner).conj().T
        @ commutator(real_generator, transported_inner)
    )

    inverse_errors = []
    transported_commutator_errors = []
    for source_projection, compression, inverse, transported in (
        (
            outer_projection,
            outer_compression,
            outer_inverse,
            transported_outer,
        ),
        (
            inner_projection,
            inner_compression,
            inner_inverse,
            transported_inner,
        ),
    ):
        inverse_errors.append(
            relative_error(
                commutator(root, inverse),
                -inverse @ commutator(root, compression) @ inverse,
            )
        )
        transported_commutator_errors.append(
            relative_error(
                commutator(root, transported),
                transport
                @ commutator(
                    root,
                    source_projection @ inverse @ source_projection,
                )
                @ transport.conj().T,
            )
        )

    return {
        "root_transport_commutator": float(
            np.linalg.norm(commutator(root, transport), ord="fro")
        ),
        "root_generator_commutator": float(
            np.linalg.norm(commutator(root, generator), ord="fro")
        ),
        "outer_projection_error": relative_error(
            transported_outer @ transported_outer, transported_outer
        ),
        "inner_projection_error": relative_error(
            transported_inner @ transported_inner, transported_inner
        ),
        "nestedness_error": relative_error(
            transported_inner @ transported_outer, transported_inner
        ),
        "outer_crossing_pullback_error": relative_error(
            pulled_outer_crossing, outer_crossing
        ),
        "inner_crossing_pullback_error": relative_error(
            pulled_inner_crossing, inner_crossing
        ),
        "inverse_commutator_error": max(inverse_errors),
        "transported_commutator_error": max(transported_commutator_errors),
        "complete_lower_flow_error": relative_error(
            crossing_flow, lower_flow
        ),
        "band_derivative_error": relative_error(
            lower_flow + lower_flow.conj().T, band_derivative
        ),
        "dirichlet_trace_error": relative_error(
            dirichlet_trace, direct_trace
        ),
    }


def parse_primes(raw: str) -> list[int]:
    primes = [int(piece.strip()) for piece in raw.split(",") if piece.strip()]
    if not primes or any(prime < 2 for prime in primes):
        raise ValueError("primes must be a comma-separated list of integers at least two")
    return primes


def fixed_s_majorant(
    primes: list[int], time: float, modes: int
) -> tuple[list[dict[str, float]], float]:
    ledger: list[dict[str, float]] = []
    maximum_error = 0.0
    for prime in primes:
        weight = prime ** -0.5
        log_prime = math.log(prime)
        ratio = time * weight
        exact = weight / (1.0 - ratio) + log_prime * weight / (1.0 - ratio) ** 2
        partial = sum(
            time ** (mode - 1)
            * weight**mode
            * (1.0 + mode * log_prime)
            for mode in range(1, modes + 1)
        )
        tail_error = abs(exact - partial)
        maximum_error = max(maximum_error, tail_error)
        uniform = weight / (1.0 - weight) + log_prime * weight / (1.0 - weight) ** 2
        ledger.append(
            {
                "prime": float(prime),
                "partial": partial,
                "exact": exact,
                "tail_error": tail_error,
                "uniform": uniform,
            }
        )
    return ledger, maximum_error


def print_report(
    algebra: dict[str, float], ledger: list[dict[str, float]], tail_error: float
) -> None:
    print("fixed-S transported-crossing algebra")
    print("+--------------------------------------+---------------+")
    print("| check                                | error         |")
    print("+--------------------------------------+---------------+")
    for label, value in algebra.items():
        print(f"| {label:<36} | {value:>13.6e} |")
    print("+--------------------------------------+---------------+")

    print()
    print("prime-power S1 majorant")
    print("+-------+-------------+-------------+-------------+-------------+")
    print("| prime | partial     | exact       | tail error  | t<=1 bound  |")
    print("+-------+-------------+-------------+-------------+-------------+")
    for row in ledger:
        print(
            f"| {int(row['prime']):>5} "
            f"| {row['partial']:>11.5e} "
            f"| {row['exact']:>11.5e} "
            f"| {row['tail_error']:>11.5e} "
            f"| {row['uniform']:>11.5e} |"
        )
    print("+-------+-------------+-------------+-------------+-------------+")
    print(f"fixed-S exact majorant: {sum(row['exact'] for row in ledger):.8f}")
    print(f"maximum truncated-tail error: {tail_error:.6e}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--time", type=float, default=0.63)
    parser.add_argument("--primes", default="2,3,5,7,11")
    parser.add_argument("--modes", type=int, default=80)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    primes = parse_primes(args.primes)
    algebra = transported_crossing_certificate(args.size, args.time)
    ledger, tail_error = fixed_s_majorant(primes, args.time, args.modes)
    print_report(algebra, ledger, tail_error)

    maximum_error = max(max(algebra.values()), tail_error)
    print(f"maximum checked error: {maximum_error:.6e}")
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
