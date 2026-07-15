#!/usr/bin/env python3
"""Certificate for the shorted Markov boundary gate in Proof 254.

The normalized inverse Euler product is a probability average of one-sided
translations, and its metric inverse is the corresponding two-sided average.
Compact autocorrelation makes a single half-line crossing vanish outside the
difference support.  Compression does not preserve that probability formula:
the inverse compressed metric is a shorted operator with a nontrivial defect.

The default certificate verifies these exact finite-dimensional identities and
an analytic two-mode obstruction.  ``--finite-section`` additionally runs a
large-S Fourier diagnostic; that diagnostic is not a continuous theorem.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_253() -> ModuleType:
    path = Path(__file__).with_name(
        "253_nested_berezin_synchronized_flow_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_253", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_factors(raw: str) -> list[tuple[float, int]]:
    factors: list[tuple[float, int]] = []
    for item in raw.split(","):
        prime_text, shift_text = item.split(":", maxsplit=1)
        prime = int(prime_text)
        shift = int(shift_text)
        if prime < 2 or shift <= 0:
            raise ValueError("factor primes and integer shifts must be positive")
        factors.append((prime ** -0.5, shift))
    if not factors:
        raise ValueError("at least one factor is required")
    return factors


def geometric_cutoff(ratio: float, tail_tolerance: float) -> int:
    if not 0.0 < ratio < 1.0:
        raise ValueError("geometric ratio must lie in (0,1)")
    return max(0, math.ceil(math.log(tail_tolerance) / math.log(ratio)) - 1)


def one_sided_law(
    factors: list[tuple[float, int]], tail_tolerance: float
) -> np.ndarray:
    law = np.ones(1, dtype=float)
    for ratio, shift in factors:
        cutoff = geometric_cutoff(ratio, tail_tolerance / len(factors))
        local = np.zeros(cutoff * shift + 1, dtype=float)
        local[::shift] = (1.0 - ratio) * ratio ** np.arange(cutoff + 1)
        law = np.convolve(law, local)
    return law


def characteristic(values: np.ndarray, theta: np.ndarray) -> np.ndarray:
    indices = np.arange(len(values), dtype=float)
    return np.exp(1j * theta[:, None] * indices[None, :]) @ values


def exact_one_sided_characteristic(
    factors: list[tuple[float, int]], theta: np.ndarray
) -> np.ndarray:
    result = np.ones_like(theta, dtype=complex)
    for ratio, shift in factors:
        result *= (1.0 - ratio) / (
            1.0 - ratio * np.exp(1j * shift * theta)
        )
    return result


def autocorrelation(sequence: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    values = np.correlate(sequence, sequence, mode="full")
    shifts = np.arange(-(len(sequence) - 1), len(sequence))
    return shifts, values


def compact_root(radius: int) -> tuple[np.ndarray, np.ndarray]:
    coordinates = np.arange(-radius, radius + 1, dtype=float)
    scaled = coordinates / (radius + 1.0)
    bump = np.exp(-1.0 / (1.0 - scaled**2))
    modulation = np.exp(0.37j * coordinates + 0.013j * coordinates**2)
    root = bump * modulation
    root /= np.linalg.norm(root)
    return coordinates.astype(int), root


def zero_fill_translation(coordinates: np.ndarray, shift: int) -> np.ndarray:
    index = {int(value): position for position, value in enumerate(coordinates)}
    matrix = np.zeros((len(coordinates), len(coordinates)), dtype=complex)
    for source, coordinate in enumerate(coordinates):
        destination = index.get(int(coordinate + shift))
        if destination is not None:
            matrix[destination, source] = 1.0
    return matrix


def crossing_trace_certificate(
    radius: int, maximum_shift: int
) -> tuple[float, dict[int, complex], float]:
    _, root = compact_root(radius)
    correlation_shifts, correlation_values = autocorrelation(root)
    correlation = {
        int(shift): value
        for shift, value in zip(correlation_shifts, correlation_values)
    }

    half_width = radius + maximum_shift + 4
    coordinates = np.arange(-half_width, half_width + 1)
    projection = np.diag((coordinates >= 0).astype(float))
    convolution = np.empty(
        (len(coordinates), len(coordinates)), dtype=complex
    )
    for row, x_value in enumerate(coordinates):
        for column, y_value in enumerate(coordinates):
            convolution[row, column] = correlation.get(
                int(x_value - y_value), 0.0
            )

    maximum_error = 0.0
    crossing_values: dict[int, complex] = {}
    for shift in range(-maximum_shift, maximum_shift + 1):
        translation = zero_fill_translation(coordinates, shift)
        commutator = projection @ translation - translation @ projection
        actual = np.trace(convolution @ commutator)
        expected = shift * correlation.get(-shift, 0.0)
        maximum_error = max(maximum_error, abs(actual - expected))
        crossing_values[shift] = actual
    return maximum_error, crossing_values, float(np.vdot(root, root).real)


def cyclic_translation(size: int, shift: int) -> np.ndarray:
    return np.roll(np.eye(size, dtype=complex), shift, axis=0)


def normalized_product(
    size: int, factors: list[tuple[float, int]]
) -> tuple[np.ndarray, np.ndarray]:
    identity = np.eye(size, dtype=complex)
    transport = identity.copy()
    inverse_transport = identity.copy()
    for ratio, shift in factors:
        translation = cyclic_translation(size, shift)
        transport = transport @ (
            (identity - ratio * translation) / (1.0 - ratio)
        )
        inverse_transport = inverse_transport @ (
            (1.0 - ratio)
            * np.linalg.inv(identity - ratio * translation)
        )
    return transport, inverse_transport


def selector_basis(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def shorting_certificate(
    size: int, factors: list[tuple[float, int]]
) -> dict[str, float]:
    transport, inverse_transport = normalized_product(size, factors)
    metric = transport.conj().T @ transport
    inverse_metric = np.linalg.inv(metric)
    markov_metric = inverse_transport @ inverse_transport.conj().T

    rank = size // 2
    selected = selector_basis(size, 0, rank)
    complement = selector_basis(size, rank, size)
    compressed_metric = selected.conj().T @ metric @ selected
    compressed_inverse = np.linalg.inv(compressed_metric)
    selected_markov = selected.conj().T @ inverse_metric @ selected
    cross_markov = selected.conj().T @ inverse_metric @ complement
    complement_markov = complement.conj().T @ inverse_metric @ complement
    defect = (
        cross_markov
        @ np.linalg.inv(complement_markov)
        @ cross_markov.conj().T
    )
    shorted = selected_markov - defect

    r_rank = size // 4
    r_basis = selector_basis(size, 0, r_rank)
    b_basis = selector_basis(size, r_rank, rank)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    e_inverse = np.linalg.inv(e_basis.conj().T @ metric @ e_basis)
    nested_inverse = e_inverse[r_rank:, r_rank:]
    b_markov = b_basis.conj().T @ inverse_metric @ b_basis
    bc_markov = b_basis.conj().T @ inverse_metric @ complement
    nested_defect = (
        bc_markov
        @ np.linalg.inv(complement_markov)
        @ bc_markov.conj().T
    )
    nested_shorted = b_markov - nested_defect

    return {
        "inverse_product_error": float(
            np.linalg.norm(
                inverse_transport @ transport - np.eye(size), ord=2
            )
        ),
        "markov_metric_error": float(
            np.linalg.norm(inverse_metric - markov_metric, ord=2)
        ),
        "shorting_error": float(
            np.linalg.norm(compressed_inverse - shorted, ord=2)
        ),
        "nested_shorting_error": float(
            np.linalg.norm(nested_inverse - nested_shorted, ord=2)
        ),
        "minimum_shorted_eigenvalue": float(
            np.linalg.eigvalsh((shorted + shorted.conj().T) / 2.0).min()
        ),
        "minimum_defect_eigenvalue": float(
            np.linalg.eigvalsh((defect + defect.conj().T) / 2.0).min()
        ),
        "minimum_nested_defect_eigenvalue": float(
            np.linalg.eigvalsh(
                (nested_defect + nested_defect.conj().T) / 2.0
            ).min()
        ),
        "jensen_violation": float(
            max(
                np.linalg.eigvalsh(
                    (
                        compressed_inverse
                        - selected_markov
                        + (compressed_inverse - selected_markov).conj().T
                    )
                    / 2.0
                ).max(),
                0.0,
            )
        ),
        "metric_log_condition": float(
            math.log(np.linalg.cond(metric))
        ),
    }


def two_mode_response(ratio: float, epsilon: float) -> dict[str, float]:
    kappa = (1.0 + ratio) / (1.0 - ratio)
    inverse_odd_eigenvalue = kappa**-2
    markov_identity = (1.0 + inverse_odd_eigenvalue) / 2.0
    markov_swap = (1.0 - inverse_odd_eigenvalue) / 2.0

    vector = np.array(
        [math.sqrt(1.0 - epsilon**2), epsilon], dtype=complex
    )
    transported = np.array([vector[0], kappa * vector[1]])
    transported /= np.linalg.norm(transported)
    projection = np.outer(vector, vector.conj())
    transported_projection = np.outer(transported, transported.conj())
    detector = np.diag([0.0, 1.0])
    band_change = -(transported_projection - projection)
    response = float(np.trace(detector @ band_change).real)
    expected_response = epsilon**2 - (
        kappa**2
        * epsilon**2
        / (1.0 - epsilon**2 + kappa**2 * epsilon**2)
    )
    fourier = np.array([[1.0, 1.0], [1.0, -1.0]]) / math.sqrt(2.0)
    physical_inverse_metric = (
        fourier
        @ np.diag([1.0, inverse_odd_eigenvalue])
        @ fourier.conj().T
    )
    swap = np.array([[0.0, 1.0], [1.0, 0.0]])
    expected_markov_metric = markov_identity * np.eye(2) + markov_swap * swap
    commutator = detector @ projection - projection @ detector
    return {
        "kappa": kappa,
        "epsilon": epsilon,
        "markov_identity": markov_identity,
        "markov_swap": markov_swap,
        "response": response,
        "response_formula_error": abs(response - expected_response),
        "markov_matrix_error": float(
            np.linalg.norm(
                physical_inverse_metric - expected_markov_metric, ord=2
            )
        ),
        "base_commutator_norm": float(np.linalg.norm(commutator, ord=2)),
    }


def fast_product_projection(
    basis: np.ndarray, primes: list[int], size: int, step: float
) -> tuple[np.ndarray, float]:
    frequencies = np.fft.fftfreq(size, d=step)
    logarithm = np.zeros(size, dtype=complex)
    for prime in primes:
        amplitude = prime ** -0.5
        phase = np.exp(2j * np.pi * frequencies * math.log(prime))
        logarithm += np.log(1.0 - amplitude * phase)
    log_condition = float(logarithm.real.max() - logarithm.real.min())
    multiplier = np.exp(logarithm - logarithm.real.max())
    columns = np.fft.ifft(
        multiplier[:, None] * np.fft.fft(basis, axis=0), axis=0
    )
    columns, _ = np.linalg.qr(columns, mode="reduced")
    return columns @ columns.conj().T, log_condition


def parse_configurations(raw: str) -> list[tuple[int, float]]:
    result: list[tuple[int, float]] = []
    for item in raw.split(","):
        size_text, step_text = item.split(":", maxsplit=1)
        size = int(size_text)
        step = float(step_text)
        if size < 64 or size % 2 or step <= 0.0:
            raise ValueError("finite-section configurations must be even and positive")
        result.append((size, step))
    return result


def finite_section_rows(
    cutoff: int,
    configurations: list[tuple[int, float]],
    root_width: float,
    intersection_tolerance: float,
) -> list[dict[str, float]]:
    proof_253 = load_proof_253()
    proof_252 = proof_253.PROOF_252
    proof_251 = proof_253.PROOF_251
    primes = proof_252.primes_up_to(cutoff)
    rows: list[dict[str, float]] = []
    for size, step in configurations:
        half_domain = size * step / 2.0
        if math.log(cutoff) + root_width >= half_domain:
            raise ValueError("finite-section domain is too small for the cutoff")
        coordinates = (np.arange(size) - size // 2) * step
        outer_basis = proof_251.halfline_basis(coordinates)
        inner_basis, _ = proof_251.sonin_basis(
            size, step, intersection_tolerance
        )
        outer_base = outer_basis @ outer_basis.conj().T
        inner_base = inner_basis @ inner_basis.conj().T
        outer_endpoint, outer_condition = fast_product_projection(
            outer_basis, primes, size, step
        )
        inner_endpoint, inner_condition = fast_product_projection(
            inner_basis, primes, size, step
        )
        endpoint_change = (
            outer_endpoint - inner_endpoint - outer_base + inner_base
        )
        root_size = int(round(root_width / step)) + 1
        root = proof_251.root_operator(endpoint_change, root_size, step)
        root = (root + root.conj().T) / 2.0
        eigenvalues = np.linalg.eigvalsh(root)
        witness, row_residual = proof_251.four_mode_row_witness(
            root_size, step
        )
        rows.append(
            {
                "size": float(size),
                "step": step,
                "half_domain": half_domain,
                "frequency_step": 2.0 * math.pi / (size * step),
                "inner_rank": float(inner_basis.shape[1]),
                "log_condition": max(outer_condition, inner_condition),
                "root_norm": float(np.linalg.norm(root, ord=2)),
                "root_minimum": float(eigenvalues.min()),
                "root_maximum": float(eigenvalues.max()),
                "witness_quadratic": float(np.vdot(witness, root @ witness).real),
                "witness_row_residual": row_residual,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--factors", default="2:1,3:3,5:7")
    parser.add_argument("--tail-tolerance", type=float, default=1e-14)
    parser.add_argument("--root-radius", type=int, default=9)
    parser.add_argument("--maximum-shift", type=int, default=24)
    parser.add_argument("--cyclic-size", type=int, default=32)
    parser.add_argument("--finite-section", action="store_true")
    parser.add_argument("--finite-cutoff", type=int, default=100000)
    parser.add_argument(
        "--finite-configurations",
        default="384:0.08,512:0.08,640:0.08,768:0.08",
    )
    parser.add_argument("--root-width", type=float, default=0.96)
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    args = parser.parse_args()

    if not 0.0 < args.tail_tolerance < 1.0:
        raise ValueError("tail-tolerance must lie in (0,1)")
    if args.root_radius < 2 or args.maximum_shift <= 2 * args.root_radius:
        raise ValueError(
            "maximum-shift must extend beyond the root difference support"
        )
    if args.cyclic_size < 16 or args.cyclic_size % 4:
        raise ValueError("cyclic-size must be a multiple of four at least 16")

    factors = parse_factors(args.factors)
    one_sided = one_sided_law(factors, args.tail_tolerance)
    two_sided = np.correlate(one_sided, one_sided, mode="full")
    two_sided_shifts = np.arange(-(len(one_sided) - 1), len(one_sided))
    theta = np.linspace(-math.pi, math.pi, 257)
    one_actual = characteristic(one_sided, theta)
    one_expected = exact_one_sided_characteristic(factors, theta)
    two_actual = (
        np.exp(1j * theta[:, None] * two_sided_shifts[None, :])
        @ two_sided
    )
    two_expected = np.abs(one_expected) ** 2
    one_error = float(np.max(np.abs(one_actual - one_expected)))
    two_error = float(np.max(np.abs(two_actual - two_expected)))
    probability_mass_error = max(
        abs(float(one_sided.sum()) - 1.0),
        abs(float(two_sided.sum()) - 1.0),
    )

    crossing_error, crossing_values, root_norm_squared = (
        crossing_trace_certificate(args.root_radius, args.maximum_shift)
    )
    correlation_shifts, correlation_values = autocorrelation(
        compact_root(args.root_radius)[1]
    )
    correlation = {
        int(shift): value
        for shift, value in zip(correlation_shifts, correlation_values)
    }
    one_sided_average_crossing = sum(
        probability
        * shift
        * correlation.get(-int(shift), 0.0)
        for shift, probability in enumerate(one_sided)
    )
    two_sided_average_crossing = sum(
        probability
        * shift
        * correlation.get(-int(shift), 0.0)
        for shift, probability in zip(two_sided_shifts, two_sided)
    )
    support_bound = 2.0 * args.root_radius * root_norm_squared
    average_bound_ratio = abs(one_sided_average_crossing) / support_bound
    outside_crossing = max(
        (
            abs(value)
            for shift, value in crossing_values.items()
            if abs(shift) > 2 * args.root_radius
        ),
        default=0.0,
    )

    shorting = shorting_certificate(args.cyclic_size, factors)
    ratios = [0.5, 0.8, 0.95, 0.99, 0.999]
    fixed_rows = [two_mode_response(ratio, 0.1) for ratio in ratios]
    adaptive_rows = [
        two_mode_response(
            ratio,
            math.sqrt((1.0 - ratio) / (1.0 + ratio)),
        )
        for ratio in ratios
    ]

    print("identity=shorted Markov compact-boundary gate")
    print("status=exact ambient survivor plus abstract compression obstruction")
    print(f"one_sided_support={len(one_sided) - 1}")
    print(f"one_sided_mass={one_sided.sum():.16e}")
    print(f"two_sided_mass={two_sided.sum():.16e}")
    print(f"probability_mass_error={probability_mass_error:.3e}")
    print(f"one_sided_characteristic_error={one_error:.3e}")
    print(f"two_sided_characteristic_error={two_error:.3e}")
    print(f"crossing_trace_error={crossing_error:.3e}")
    print(f"outside_support_crossing={outside_crossing:.3e}")
    print(
        "one_sided_average_crossing="
        f"{one_sided_average_crossing.real:.12e}"
        f"{one_sided_average_crossing.imag:+.12e}i"
    )
    print(
        "two_sided_average_crossing="
        f"{two_sided_average_crossing.real:.12e}"
        f"{two_sided_average_crossing.imag:+.12e}i"
    )
    print(
        "one_sided_average_crossing_abs="
        f"{abs(one_sided_average_crossing):.12e}"
    )
    print(f"compact_support_bound={support_bound:.12e}")
    print(f"average_bound_ratio={average_bound_ratio:.12e}")
    for key, value in shorting.items():
        print(f"{key}={value:.12e}")

    print("two_mode_fixed_projection_table=BEGIN")
    for ratio, row in zip(ratios, fixed_rows):
        print(
            f"ratio={ratio:.6f} "
            f"kappa={row['kappa']:.6e} "
            f"markov_identity={row['markov_identity']:.12e} "
            f"markov_swap={row['markov_swap']:.12e} "
            f"epsilon={row['epsilon']:.12e} "
            f"response={row['response']:.12e} "
            f"commutator_norm={row['base_commutator_norm']:.12e}"
        )
    print("two_mode_fixed_projection_table=END")
    print("two_mode_adaptive_projection_table=BEGIN")
    for ratio, row in zip(ratios, adaptive_rows):
        print(
            f"ratio={ratio:.6f} "
            f"kappa={row['kappa']:.6e} "
            f"epsilon={row['epsilon']:.12e} "
            f"response={row['response']:.12e} "
            f"commutator_norm={row['base_commutator_norm']:.12e}"
        )
    print("two_mode_adaptive_projection_table=END")

    maximum_two_mode_formula_error = max(
        max(row["response_formula_error"], row["markov_matrix_error"])
        for row in fixed_rows + adaptive_rows
    )
    print(
        "maximum_two_mode_formula_error="
        f"{maximum_two_mode_formula_error:.12e}"
    )

    if args.finite_section:
        configurations = parse_configurations(args.finite_configurations)
        rows = finite_section_rows(
            args.finite_cutoff,
            configurations,
            args.root_width,
            args.intersection_tolerance,
        )
        print("finite_section_table=BEGIN")
        for row in rows:
            print(
                f"cutoff={args.finite_cutoff} "
                f"size={int(row['size'])} "
                f"step={row['step']:.8f} "
                f"half_domain={row['half_domain']:.8f} "
                f"frequency_step={row['frequency_step']:.8f} "
                f"inner_rank={int(row['inner_rank'])} "
                f"log_condition={row['log_condition']:.12e} "
                f"root_norm={row['root_norm']:.12e} "
                f"root_minimum={row['root_minimum']:.12e} "
                f"root_maximum={row['root_maximum']:.12e} "
                f"witness={row['witness_quadratic']:.12e} "
                f"row_residual={row['witness_row_residual']:.3e}"
            )
        print("finite_section_table=END")

    maximum_algebra_error = max(
        probability_mass_error,
        one_error,
        two_error,
        crossing_error,
        outside_crossing,
        shorting["inverse_product_error"],
        shorting["markov_metric_error"],
        shorting["shorting_error"],
        shorting["nested_shorting_error"],
        shorting["jensen_violation"],
        max(-shorting["minimum_shorted_eigenvalue"], 0.0),
        max(-shorting["minimum_defect_eigenvalue"], 0.0),
        max(-shorting["minimum_nested_defect_eigenvalue"], 0.0),
        maximum_two_mode_formula_error,
    )
    if maximum_algebra_error > 2e-9:
        raise RuntimeError(f"algebra certificate failed: {maximum_algebra_error}")
    if average_bound_ratio > 1.0 + 1e-12:
        raise RuntimeError("compact-support probability bound failed")
    if fixed_rows[-1]["response"] > -0.98:
        raise RuntimeError("fixed two-mode Markov obstruction did not survive")
    if adaptive_rows[-1]["response"] > -0.99:
        raise RuntimeError("adaptive two-mode Markov obstruction did not survive")

    print("certificate=PASS")
    print("one_sided_markov_inverse_verdict=EXACT")
    print("two_sided_markov_metric_verdict=EXACT")
    print("compact_root_crossing_clipping_verdict=UNIFORM")
    print("compressed_inverse_shorting_verdict=EXACT_NONTRIVIAL_DEFECT")
    print("markov_only_projection_bound_verdict=REJECTED")
    print("sonin_shorted_boundary_bound=OPEN")
    print("detector_specific_integrated_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
