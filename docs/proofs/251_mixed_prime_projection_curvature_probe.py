#!/usr/bin/env python3
"""Death test for mixed-prime curvature of the nested Sonin complement.

For a fixed orthogonal projection J and commuting translations U, V, let

    J_(a,b) = projection onto (I-aU)(I-bV) Ran(J).

The script evaluates the exact mixed Hessian d_a d_b J_(0,0), verifies it
against an independent finite difference, and then applies the same trace
diagonal and pre-root differential used by the complete-central probe.  The
finite periodic Sonin section is diagnostic only.  A route verdict still
requires a continuous kernel theorem.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


LANCZOS_COEFFICIENTS = np.array(
    [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278998905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ]
)


def parse_pairs(raw: str) -> list[tuple[float, float]]:
    pairs: list[tuple[float, float]] = []
    for item in raw.split(","):
        if not item.strip():
            continue
        left, right = item.split(":", maxsplit=1)
        pairs.append((float(left), float(right)))
    return pairs


def log_gamma_lanczos(values: np.ndarray) -> np.ndarray:
    shifted = values - 1.0
    series = np.full_like(values, LANCZOS_COEFFICIENTS[0], dtype=complex)
    for index, coefficient in enumerate(
        LANCZOS_COEFFICIENTS[1:], start=1
    ):
        series += coefficient / (shifted + index)
    tail = shifted + 7.5
    return (
        0.5 * np.log(2.0 * np.pi)
        + (shifted + 0.5) * np.log(tail)
        - tail
        + np.log(series)
    )


def archimedean_scattering(frequencies: np.ndarray) -> np.ndarray:
    arguments = 0.25 + 0.5j * frequencies
    log_gamma = log_gamma_lanczos(arguments)
    return np.exp(
        -1j * frequencies * math.log(math.pi)
        + log_gamma
        - np.conj(log_gamma)
    )


def sonin_basis(
    size: int, step: float, intersection_tolerance: float
) -> tuple[np.ndarray, np.ndarray]:
    coordinates = (np.arange(size) - size // 2) * step
    frequencies = 2.0 * np.pi * np.fft.fftfreq(size, d=step)
    scattering = archimedean_scattering(frequencies)

    positive_indices = np.flatnonzero(coordinates >= 0.0)
    positive_basis = np.zeros(
        (size, len(positive_indices)), dtype=complex
    )
    positive_basis[positive_indices, np.arange(len(positive_indices))] = 1.0
    scattering_image = np.fft.ifft(
        scattering[:, None] * np.fft.fft(positive_basis, axis=0),
        axis=0,
    )
    scattering_image[coordinates >= 0.0, :] = 0.0
    angle = scattering_image.conj().T @ scattering_image
    angle = (angle + angle.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(angle)
    selected = eigenvalues > 1.0 - intersection_tolerance

    basis = np.zeros((size, int(selected.sum())), dtype=complex)
    basis[positive_indices, :] = eigenvectors[:, selected]
    return basis, eigenvalues


def halfline_basis(coordinates: np.ndarray) -> np.ndarray:
    positive_indices = np.flatnonzero(coordinates >= 0.0)
    basis = np.zeros(
        (len(coordinates), len(positive_indices)), dtype=complex
    )
    basis[positive_indices, np.arange(len(positive_indices))] = 1.0
    return basis


def translation_matrix(
    size: int, displacement: int, shift_mode: str
) -> np.ndarray:
    if not 0 <= displacement < size:
        raise ValueError("translation displacement must lie in [0,size)")
    identity = np.eye(size, dtype=complex)
    if shift_mode == "periodic":
        return np.roll(identity, -displacement, axis=0)
    translated = np.zeros_like(identity)
    if displacement == 0:
        translated[:] = identity
    else:
        translated[:-displacement, displacement:] = np.eye(
            size - displacement, dtype=complex
        )
    return translated


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    basis, _ = np.linalg.qr(columns, mode="reduced")
    return basis @ basis.conj().T


def transformed_projection(
    basis: np.ndarray,
    first_translation: np.ndarray,
    second_translation: np.ndarray,
    first_parameter: float,
    second_parameter: float,
) -> np.ndarray:
    transformed = (
        basis
        - first_parameter * (first_translation @ basis)
        - second_parameter * (second_translation @ basis)
        + first_parameter
        * second_parameter
        * (first_translation @ second_translation @ basis)
    )
    return orthogonal_projection(transformed)


def projection_mixed_hessian(
    projection: np.ndarray,
    first_translation: np.ndarray,
    second_translation: np.ndarray,
) -> np.ndarray:
    """Exact d_a d_b projection onto (I-aU)(I-bV) Ran(P) at zero."""
    identity = np.eye(len(projection), dtype=complex)
    complement = identity - projection
    first_crossing = complement @ first_translation @ projection
    second_crossing = complement @ second_translation @ projection
    mixed_graph = (
        complement @ first_translation @ second_translation @ projection
        - complement
        @ first_translation
        @ projection
        @ second_translation
        @ projection
        - complement
        @ second_translation
        @ projection
        @ first_translation
        @ projection
    )
    hessian = (
        mixed_graph
        + mixed_graph.conj().T
        + first_crossing @ second_crossing.conj().T
        + second_crossing @ first_crossing.conj().T
        - first_crossing.conj().T @ second_crossing
        - second_crossing.conj().T @ first_crossing
    )
    return (hessian + hessian.conj().T) / 2.0


def projection_mixed_finite_difference(
    basis: np.ndarray,
    zero_projection: np.ndarray,
    first_translation: np.ndarray,
    second_translation: np.ndarray,
    finite_difference_step: float,
) -> np.ndarray:
    first = transformed_projection(
        basis,
        first_translation,
        second_translation,
        finite_difference_step,
        0.0,
    )
    second = transformed_projection(
        basis,
        first_translation,
        second_translation,
        0.0,
        finite_difference_step,
    )
    mixed = transformed_projection(
        basis,
        first_translation,
        second_translation,
        finite_difference_step,
        finite_difference_step,
    )
    return (
        mixed - first - second + zero_projection
    ) / finite_difference_step**2


def trace_diagonal_toeplitz(
    matrix: np.ndarray, root_size: int
) -> np.ndarray:
    values: dict[int, complex] = {}
    for offset in range(-(root_size - 1), root_size):
        values[offset] = np.trace(matrix, offset=offset)
    toeplitz = np.empty((root_size, root_size), dtype=complex)
    for row in range(root_size):
        for column in range(root_size):
            toeplitz[row, column] = values[column - row]
    return toeplitz


def root_differential(root_size: int, step: float) -> np.ndarray:
    differential = 0.5 * np.eye(root_size, dtype=complex)
    for index in range(root_size):
        if index + 1 < root_size:
            differential[index, index + 1] += 1.0 / (2.0 * step)
        if index - 1 >= 0:
            differential[index, index - 1] -= 1.0 / (2.0 * step)
    return differential


def root_operator(
    matrix: np.ndarray, root_size: int, step: float
) -> np.ndarray:
    toeplitz = trace_diagonal_toeplitz(matrix, root_size)
    differential = root_differential(root_size, step)
    operator = step**2 * differential.conj().T @ toeplitz @ differential
    return (operator + operator.conj().T) / 2.0


def pre_root_constraint_basis(root_size: int, step: float) -> np.ndarray:
    coordinates = (
        np.arange(root_size) - (root_size - 1) / 2.0
    ) * step
    rows = np.column_stack(
        [np.ones(root_size, dtype=complex), np.exp(coordinates)]
    )
    complete_basis, _ = np.linalg.qr(rows, mode="complete")
    return complete_basis[:, 2:]


def constrained_dirichlet_galerkin_basis(
    root_size: int, step: float, mode_count: int
) -> np.ndarray:
    coordinates = (
        np.arange(root_size) - (root_size - 1) / 2.0
    ) * step
    interval_length = coordinates[-1] - coordinates[0]
    raw_basis = np.column_stack(
        [
            np.sin(
                mode
                * np.pi
                * (coordinates - coordinates[0])
                / interval_length
            )
            for mode in range(1, mode_count + 1)
        ]
    )
    galerkin_basis, _ = np.linalg.qr(raw_basis, mode="reduced")
    row_vectors = np.column_stack(
        [np.ones(root_size, dtype=complex), np.exp(coordinates)]
    )
    constraints = row_vectors.conj().T @ galerkin_basis
    singular_values = np.linalg.svd(constraints, compute_uv=False)
    rank_threshold = max(constraints.shape) * np.finfo(float).eps
    constraint_rank = int(
        np.count_nonzero(
            singular_values > rank_threshold * singular_values[0]
        )
    )
    complete_basis, _ = np.linalg.qr(
        constraints.conj().T, mode="complete"
    )
    return galerkin_basis @ complete_basis[:, constraint_rank:]


def four_mode_row_witness(
    root_size: int, step: float
) -> tuple[np.ndarray, float]:
    interval_length = (root_size - 1) * step
    coordinates = np.arange(root_size) * step
    exponential_endpoint = math.exp(interval_length)

    def moment_coefficient(mode: int) -> float:
        frequency = mode * math.pi / interval_length
        parity = -1.0 if mode % 2 else 1.0
        return (
            frequency
            * (1.0 - parity * exponential_endpoint)
            / (1.0 + frequency**2)
        )

    coefficients = {
        1: -8.0 / 15.0,
        3: 1.0,
        5: 1.0,
    }
    coefficients[2] = -sum(
        coefficient * moment_coefficient(mode)
        for mode, coefficient in coefficients.items()
    ) / moment_coefficient(2)
    witness = sum(
        coefficient
        * math.sqrt(2.0 / interval_length)
        * np.sin(mode * math.pi * coordinates / interval_length)
        for mode, coefficient in coefficients.items()
    ).astype(complex)
    witness /= np.linalg.norm(witness)
    row_residual = max(
        abs(step * np.sum(witness)),
        abs(step * np.sum(np.exp(coordinates) * witness)),
    )
    return witness, float(row_residual)


def operator_norm(matrix: np.ndarray) -> float:
    return float(np.max(np.abs(np.linalg.eigvalsh(matrix))))


def mixed_row(
    outer_basis: np.ndarray,
    inner_basis: np.ndarray,
    outer_projection: np.ndarray,
    inner_projection: np.ndarray,
    root_constraint_basis: np.ndarray,
    galerkin_constraint_basis: np.ndarray,
    four_mode_witness: np.ndarray,
    four_mode_row_residual: float,
    size: int,
    step: float,
    root_size: int,
    first_length: float,
    second_length: float,
    shift_mode: str,
    finite_difference_step: float,
    verify_finite_difference: bool,
) -> dict[str, float]:
    first_displacement = int(round(first_length / step))
    second_displacement = int(round(second_length / step))
    realized_first = first_displacement * step
    realized_second = second_displacement * step
    first_translation = translation_matrix(
        size, first_displacement, shift_mode
    )
    second_translation = translation_matrix(
        size, second_displacement, shift_mode
    )

    outer_hessian = projection_mixed_hessian(
        outer_projection, first_translation, second_translation
    )
    inner_hessian = projection_mixed_hessian(
        inner_projection, first_translation, second_translation
    )
    exact_hessian = outer_hessian - inner_hessian
    exact_root = root_operator(exact_hessian, root_size, step)
    outer_root = root_operator(outer_hessian, root_size, step)
    inner_root = root_operator(inner_hessian, root_size, step)
    constrained_root = (
        root_constraint_basis.conj().T
        @ exact_root
        @ root_constraint_basis
    )
    galerkin_root = (
        galerkin_constraint_basis.conj().T
        @ exact_root
        @ galerkin_constraint_basis
    )
    eigenvalues = np.linalg.eigvalsh(exact_root)
    constrained_eigenvalues = np.linalg.eigvalsh(constrained_root)
    galerkin_eigenvalues = np.linalg.eigvalsh(galerkin_root)
    four_mode_quadratic = float(
        np.vdot(four_mode_witness, exact_root @ four_mode_witness).real
    )
    coefficient_norm = operator_norm(exact_root)
    euler_product = math.exp(
        -(realized_first + realized_second) / 2.0
    )
    physical_norm = euler_product * coefficient_norm
    ambient_finite_difference_relative_error = 0.0
    root_finite_difference_relative_error = 0.0
    if verify_finite_difference:
        finite_difference = projection_mixed_finite_difference(
            outer_basis,
            outer_projection,
            first_translation,
            second_translation,
            finite_difference_step,
        ) - projection_mixed_finite_difference(
            inner_basis,
            inner_projection,
            first_translation,
            second_translation,
            finite_difference_step,
        )
        finite_difference_root = root_operator(
            finite_difference, root_size, step
        )
        ambient_scale = max(
            float(np.linalg.norm(exact_hessian, ord="fro")), 1e-15
        )
        root_scale = max(coefficient_norm, 1e-15)
        ambient_finite_difference_relative_error = float(
            np.linalg.norm(
                finite_difference - exact_hessian, ord="fro"
            )
            / ambient_scale
        )
        root_finite_difference_relative_error = float(
            operator_norm(finite_difference_root - exact_root) / root_scale
        )
    return {
        "first_length": realized_first,
        "second_length": realized_second,
        "coefficient_norm": coefficient_norm,
        "outer_coefficient_norm": operator_norm(outer_root),
        "inner_coefficient_norm": operator_norm(inner_root),
        "physical_norm": physical_norm,
        "scaled_half": physical_norm
        * math.exp((realized_first + realized_second) / 2.0),
        "scaled_full": physical_norm
        * math.exp(realized_first + realized_second),
        "minimum": float(eigenvalues[0]),
        "maximum": float(eigenvalues[-1]),
        "constrained_minimum": float(constrained_eigenvalues[0]),
        "constrained_maximum": float(constrained_eigenvalues[-1]),
        "galerkin_minimum": float(galerkin_eigenvalues[0]),
        "galerkin_maximum": float(galerkin_eigenvalues[-1]),
        "galerkin_norm": float(
            np.max(np.abs(galerkin_eigenvalues))
        ),
        "four_mode_quadratic": four_mode_quadratic,
        "four_mode_row_residual": four_mode_row_residual,
        "self_adjoint_error": float(
            np.linalg.norm(exact_hessian - exact_hessian.conj().T, ord="fro")
        ),
        "trace_error": float(abs(np.trace(exact_hessian))),
        "finite_difference_verified": float(verify_finite_difference),
        "ambient_finite_difference_relative_error": (
            ambient_finite_difference_relative_error
        ),
        "root_finite_difference_relative_error": (
            root_finite_difference_relative_error
        ),
    }


def fitted_slope(rows: list[dict[str, float]]) -> float:
    total_lengths = np.array(
        [row["first_length"] + row["second_length"] for row in rows]
    )
    logarithms = np.log(
        np.array([row["physical_norm"] for row in rows])
    )
    return float(np.polyfit(total_lengths, logarithms, 1)[0])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=512)
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--root-width", type=float, default=1.0)
    parser.add_argument("--galerkin-modes", type=int, default=8)
    parser.add_argument(
        "--pairs",
        default="2.5:3,3:3.5,3.5:4,4:4.5,4.5:5,5:5.5",
    )
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument(
        "--finite-difference-step", type=float, default=2e-4
    )
    parser.add_argument("--finite-difference-pairs", type=int, default=1)
    parser.add_argument(
        "--shift-mode", choices=("zero", "periodic"), default="zero"
    )
    parser.add_argument("--max-self-adjoint-error", type=float, default=2e-10)
    parser.add_argument("--max-trace-error", type=float, default=2e-8)
    parser.add_argument(
        "--max-outer-halfline-norm", type=float, default=2e-8
    )
    parser.add_argument(
        "--max-ambient-finite-difference-error", type=float, default=5e-3
    )
    parser.add_argument(
        "--max-root-finite-difference-error", type=float, default=5e-3
    )
    parser.add_argument(
        "--min-indefinite-eigenvalue", type=float, default=1e-4
    )
    parser.add_argument(
        "--min-surviving-coefficient-norm", type=float, default=1e-3
    )
    args = parser.parse_args()

    if args.size < 256 or args.size % 2 != 0:
        raise ValueError("size must be an even integer at least 256")
    if args.step <= 0.0:
        raise ValueError("step must be positive")
    if args.root_width <= 4.0 * args.step:
        raise ValueError("root-width is too small")
    if args.galerkin_modes < 4:
        raise ValueError("galerkin-modes must be at least four")
    if not 0.0 < args.finite_difference_step < 0.01:
        raise ValueError("finite-difference-step must lie in (0,0.01)")
    pairs = parse_pairs(args.pairs)
    if len(pairs) < 3:
        raise ValueError("pairs must contain at least three length pairs")
    if not 1 <= args.finite_difference_pairs <= len(pairs):
        raise ValueError(
            "finite-difference-pairs must lie between one and the pair count"
        )

    coordinates = (np.arange(args.size) - args.size // 2) * args.step
    half_domain = args.size * args.step / 2.0
    if max(max(pair) for pair in pairs) + args.root_width >= half_domain:
        raise ValueError("domain is too small for the requested translations")
    inner_basis, angle_eigenvalues = sonin_basis(
        args.size, args.step, args.intersection_tolerance
    )
    if inner_basis.shape[1] == 0:
        raise RuntimeError("finite section found no near-Sonin directions")
    outer_basis = halfline_basis(coordinates)
    outer_projection = orthogonal_projection(outer_basis)
    inner_projection = orthogonal_projection(inner_basis)
    root_size = int(round(args.root_width / args.step))
    constraint_basis = pre_root_constraint_basis(root_size, args.step)
    galerkin_constraint_basis = constrained_dirichlet_galerkin_basis(
        root_size, args.step, args.galerkin_modes
    )
    four_mode_witness, four_mode_row_residual = four_mode_row_witness(
        root_size, args.step
    )
    rows = [
        mixed_row(
            outer_basis,
            inner_basis,
            outer_projection,
            inner_projection,
            constraint_basis,
            galerkin_constraint_basis,
            four_mode_witness,
            four_mode_row_residual,
            args.size,
            args.step,
            root_size,
            first_length,
            second_length,
            args.shift_mode,
            args.finite_difference_step,
            index < args.finite_difference_pairs,
        )
        for index, (first_length, second_length) in enumerate(pairs)
    ]
    slope = fitted_slope(rows)

    print("identity=exact mixed-prime nested projection curvature")
    print(f"size={args.size} step={args.step:.8f}")
    print(f"domain_half_width={half_domain:.8f}")
    print(f"root_width={args.root_width:.8f}")
    print(f"galerkin_modes={args.galerkin_modes}")
    print(
        "constrained_galerkin_dimension="
        f"{galerkin_constraint_basis.shape[1]}"
    )
    print(f"shift_mode={args.shift_mode}")
    print(f"near_sonin_rank={inner_basis.shape[1]}")
    print(f"angle_max={float(angle_eigenvalues[-1]):.12e}")
    print(
        "angle_selected_min="
        f"{float(angle_eigenvalues[-inner_basis.shape[1]]):.12e}"
    )
    print("mixed_curvature_table=BEGIN")
    for row in rows:
        print(
            f"L={row['first_length']:.8f} "
            f"M={row['second_length']:.8f} "
            f"coefficient_norm={row['coefficient_norm']:.12e} "
            f"outer_norm={row['outer_coefficient_norm']:.3e} "
            f"inner_norm={row['inner_coefficient_norm']:.12e} "
            f"physical_norm={row['physical_norm']:.12e} "
            f"scaled_half={row['scaled_half']:.12e} "
            f"scaled_full={row['scaled_full']:.12e} "
            f"minimum={row['minimum']:.12e} "
            f"maximum={row['maximum']:.12e} "
            f"constrained_minimum={row['constrained_minimum']:.12e} "
            f"constrained_maximum={row['constrained_maximum']:.12e} "
            f"galerkin_minimum={row['galerkin_minimum']:.12e} "
            f"galerkin_maximum={row['galerkin_maximum']:.12e} "
            f"galerkin_norm={row['galerkin_norm']:.12e} "
            f"four_mode_quadratic={row['four_mode_quadratic']:.12e} "
            f"four_mode_row_residual={row['four_mode_row_residual']:.3e} "
            f"finite_difference_verified="
            f"{int(row['finite_difference_verified'])} "
            "ambient_fd_relative_error="
            f"{row['ambient_finite_difference_relative_error']:.3e} "
            "root_fd_relative_error="
            f"{row['root_finite_difference_relative_error']:.3e}"
        )
    print("mixed_curvature_table=END")
    print(f"log_physical_norm_slope_per_total_log={slope:.12e}")

    if max(row["self_adjoint_error"] for row in rows) > args.max_self_adjoint_error:
        raise RuntimeError("mixed Hessian lost self-adjointness")
    if max(row["trace_error"] for row in rows) > args.max_trace_error:
        raise RuntimeError("mixed projection Hessian lost constant rank")
    if (
        max(row["outer_coefficient_norm"] for row in rows)
        > args.max_outer_halfline_norm
    ):
        raise RuntimeError("outer half-line curvature did not cancel")
    verified_rows = [
        row for row in rows if row["finite_difference_verified"] == 1.0
    ]
    if (
        max(
            row["ambient_finite_difference_relative_error"]
            for row in verified_rows
        )
        > args.max_ambient_finite_difference_error
    ):
        raise RuntimeError("ambient finite difference did not verify Hessian")
    if (
        max(
            row["root_finite_difference_relative_error"]
            for row in verified_rows
        )
        > args.max_root_finite_difference_error
    ):
        raise RuntimeError("root finite difference did not verify Hessian")

    distinct_rows = [
        row
        for row in rows
        if abs(row["first_length"] - row["second_length"]) > args.step / 2.0
    ]
    if not distinct_rows:
        raise RuntimeError("at least one distinct translation pair is required")
    if not any(
        row["constrained_minimum"] < -args.min_indefinite_eigenvalue
        and row["constrained_maximum"] > args.min_indefinite_eigenvalue
        for row in distinct_rows
    ):
        raise RuntimeError("mixed curvature did not exhibit both constrained signs")
    if not any(
        row["galerkin_minimum"] < -args.min_indefinite_eigenvalue
        and row["galerkin_maximum"] > args.min_indefinite_eigenvalue
        for row in distinct_rows
    ):
        raise RuntimeError(
            "fixed Galerkin mixed curvature did not exhibit both signs"
        )
    if (
        max(row["coefficient_norm"] for row in distinct_rows)
        < args.min_surviving_coefficient_norm
    ):
        raise RuntimeError("mixed curvature coefficient vanished in the probe")

    print("certificate=PASS")
    print("analytic_mixed_hessian_verdict=PASS")
    print("finite_difference_verdict=PASS")
    print("outer_halfline_curvature_cancellation_verdict=PASS")
    print("two_mellin_row_indefiniteness_verdict=PASS")
    print("fixed_galerkin_indefiniteness_verdict=PASS")
    if slope > -0.75:
        print("mixed_scaling_diagnostic=SURVIVING_HALF_POWER_PRODUCT")
    else:
        print("mixed_scaling_diagnostic=EXTRA_PRODUCT_GAIN")
    print("continuous_mixed_curvature_theorem=OPEN")
    print("finite_S_absolute_smallness=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
