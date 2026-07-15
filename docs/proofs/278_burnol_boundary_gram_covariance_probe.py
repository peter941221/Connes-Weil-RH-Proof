#!/usr/bin/env python3
"""Certificate for Proof 278's Burnol boundary Gram covariance.

The certificate has two finite-dimensional layers.  The first checks the
complementary-subspace Jacobi identity and its mixed logarithmic derivative.
The second realizes the Sonin complement as the span of a support space and
its image under a self-adjoint Fourier surrogate.  It then checks the
plus/minus Gram reduction, the prolate spectrum, and the complete
outer/second-support/prolate commutator recombination.

Finite matrices certify the algebra only.  They do not prove the continuous
trace-class domain or the Gate 3U estimate.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    unitary, diagonal = np.linalg.qr(matrix)
    phases = np.diag(diagonal)
    phases = np.where(np.abs(phases) > 0.0, phases / np.abs(phases), 1.0)
    return unitary @ np.diag(np.conj(phases))


def hermitian_involution(
    size: int, rng: np.random.Generator
) -> np.ndarray:
    basis = random_unitary(size, rng)
    signs = np.ones(size)
    signs[size // 2 :] = -1.0
    return basis @ np.diag(signs) @ basis.conj().T


def inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    hermitian = (matrix + matrix.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    if float(eigenvalues[0]) <= 0.0:
        raise ValueError("matrix is not positive definite")
    return eigenvectors @ np.diag(eigenvalues**-0.5) @ eigenvectors.conj().T


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def projection_basis(projection: np.ndarray) -> np.ndarray:
    hermitian = (projection + projection.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    return eigenvectors[:, eigenvalues > 0.5]


def relative_error(left: complex, right: complex) -> float:
    return float(abs(left - right) / max(1.0, abs(left), abs(right)))


def log_positive_determinant(matrix: np.ndarray) -> float:
    hermitian = (matrix + matrix.conj().T) / 2.0
    sign, logarithm = np.linalg.slogdet(hermitian)
    if abs(sign - 1.0) > 1e-8:
        raise ValueError("compressed exponential is not positive definite")
    return float(logarithm)


def assemble_source_model(
    transform: np.ndarray, support_rank: int
) -> dict[str, np.ndarray]:
    size = transform.shape[0]
    support_basis = np.eye(size, support_rank, dtype=complex)
    support = support_basis @ support_basis.conj().T
    graph = np.concatenate(
        [support_basis, transform @ support_basis], axis=1
    )
    gram = graph.conj().T @ graph
    minimum_gram = float(np.linalg.eigvalsh(gram)[0])
    if minimum_gram < 1e-3:
        raise ValueError("source graph is numerically too close to singular")
    gram_inverse = np.linalg.inv(gram)
    complement = graph @ gram_inverse @ graph.conj().T
    sonin = np.eye(size, dtype=complex) - complement
    outer = np.eye(size, dtype=complex) - support
    second = transform @ outer @ transform
    prolate = outer @ second @ outer - sonin
    truncated_transform = support_basis.conj().T @ transform @ support_basis
    return {
        "transform": transform,
        "support_basis": support_basis,
        "support": support,
        "graph": graph,
        "gram": gram,
        "gram_inverse": gram_inverse,
        "complement": complement,
        "sonin": sonin,
        "outer": outer,
        "second": second,
        "prolate": prolate,
        "truncated_transform": truncated_transform,
    }


def build_source_model(
    size: int, support_rank: int, rng: np.random.Generator
) -> dict[str, np.ndarray]:
    return assemble_source_model(
        hermitian_involution(size, rng), support_rank
    )


def build_zero_prolate_model(
    size: int, support_rank: int
) -> dict[str, np.ndarray]:
    transform = np.eye(size, dtype=complex)
    for index in range(support_rank):
        paired = support_rank + index
        transform[index, index] = 0.0
        transform[paired, paired] = 0.0
        transform[index, paired] = 1.0
        transform[paired, index] = 1.0
    for index in range(2 * support_rank, size):
        transform[index, index] = 1.0 if index % 2 == 0 else -1.0
    return assemble_source_model(transform, support_rank)


def build_commuting_multipliers(
    size: int, rng: np.random.Generator
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    basis = random_unitary(size, rng)
    detector_values = np.linspace(0.35, 1.65, size)
    detector_values += 0.03 * rng.normal(size=size)
    generator_values = np.sin(np.linspace(-1.3, 1.7, size))
    generator_values += 0.04 * rng.normal(size=size)
    detector = basis @ np.diag(detector_values) @ basis.conj().T
    generator = basis @ np.diag(generator_values) @ basis.conj().T
    return detector, generator, basis, detector_values, generator_values


def multiplier_exponential(
    basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    detector_parameter: float,
    generator_parameter: float,
) -> np.ndarray:
    values = np.exp(
        detector_parameter * detector_values
        + generator_parameter * generator_values
    )
    return basis @ np.diag(values) @ basis.conj().T


def jacobi_checks(
    model: dict[str, np.ndarray],
    detector: np.ndarray,
    generator: np.ndarray,
    multiplier_basis: np.ndarray,
    detector_values: np.ndarray,
    generator_values: np.ndarray,
    determinant_parameter: float,
    derivative_step: float,
) -> dict[str, float]:
    graph = model["graph"]
    gram = model["gram"]
    gram_inverse = model["gram_inverse"]
    complement = model["complement"]
    sonin = model["sonin"]
    outer = model["outer"]
    support_basis = model["support_basis"]
    sonin_basis = projection_basis(sonin)
    outer_basis = projection_basis(outer)
    complement_basis = graph @ inverse_square_root(gram)

    exponential = multiplier_exponential(
        multiplier_basis,
        detector_values,
        generator_values,
        determinant_parameter,
        -0.7 * determinant_parameter,
    )
    exponential_inverse = np.linalg.inv(exponential)
    compressed = sonin_basis.conj().T @ exponential @ sonin_basis
    left_determinant = np.linalg.det(compressed)
    boundary_block = gram_inverse @ (
        graph.conj().T @ exponential_inverse @ graph
    )
    right_determinant = np.linalg.det(exponential) * np.linalg.det(
        boundary_block
    )
    outer_determinant = np.linalg.det(
        outer_basis.conj().T @ exponential @ outer_basis
    )
    outer_boundary_determinant = np.linalg.det(
        support_basis.conj().T @ exponential_inverse @ support_basis
    )
    sonin_boundary_determinant = np.linalg.det(
        complement_basis.conj().T
        @ exponential_inverse
        @ complement_basis
    )
    relative_compressed_determinant = outer_determinant / left_determinant
    relative_boundary_determinant = (
        outer_boundary_determinant / sonin_boundary_determinant
    )

    def compressed_logdet(
        detector_parameter: float, generator_parameter: float
    ) -> float:
        matrix = multiplier_exponential(
            multiplier_basis,
            detector_values,
            generator_values,
            detector_parameter,
            generator_parameter,
        )
        return log_positive_determinant(
            sonin_basis.conj().T @ matrix @ sonin_basis
        )

    def relative_compressed_logdet(
        detector_parameter: float, generator_parameter: float
    ) -> float:
        matrix = multiplier_exponential(
            multiplier_basis,
            detector_values,
            generator_values,
            detector_parameter,
            generator_parameter,
        )
        return log_positive_determinant(
            outer_basis.conj().T @ matrix @ outer_basis
        ) - log_positive_determinant(
            sonin_basis.conj().T @ matrix @ sonin_basis
        )

    def relative_boundary_logdet(
        detector_parameter: float, generator_parameter: float
    ) -> float:
        matrix_inverse = multiplier_exponential(
            multiplier_basis,
            detector_values,
            generator_values,
            -detector_parameter,
            -generator_parameter,
        )
        return log_positive_determinant(
            support_basis.conj().T @ matrix_inverse @ support_basis
        ) - log_positive_determinant(
            complement_basis.conj().T
            @ matrix_inverse
            @ complement_basis
        )

    step = derivative_step
    mixed_derivative = (
        compressed_logdet(step, step)
        - compressed_logdet(step, -step)
        - compressed_logdet(-step, step)
        + compressed_logdet(-step, -step)
    ) / (4.0 * step**2)
    relative_mixed_derivative = (
        relative_compressed_logdet(step, step)
        - relative_compressed_logdet(step, -step)
        - relative_compressed_logdet(-step, step)
        + relative_compressed_logdet(-step, -step)
    ) / (4.0 * step**2)
    boundary_relative_mixed_derivative = (
        relative_boundary_logdet(step, step)
        - relative_boundary_logdet(step, -step)
        - relative_boundary_logdet(-step, step)
        + relative_boundary_logdet(-step, -step)
    ) / (4.0 * step**2)

    covariance = np.trace(
        sonin @ detector @ complement @ generator @ sonin
    )
    boundary_covariance = np.trace(
        gram_inverse
        @ (
            graph.conj().T @ generator @ detector @ graph
            - graph.conj().T
            @ generator
            @ graph
            @ gram_inverse
            @ graph.conj().T
            @ detector
            @ graph
        )
    )
    outer_covariance = np.trace(
        outer
        @ detector
        @ (np.eye(outer.shape[0], dtype=complex) - outer)
        @ generator
        @ outer
    )
    relative_covariance = outer_covariance - covariance
    return {
        "Jacobi complementary determinant error": relative_error(
            left_determinant, right_determinant
        ),
        "mixed log-determinant derivative error": float(
            abs(mixed_derivative - covariance.real)
        ),
        "relative E/R determinant error": relative_error(
            relative_compressed_determinant, relative_boundary_determinant
        ),
        "relative E/R mixed derivative error": float(
            abs(relative_mixed_derivative - relative_covariance.real)
        ),
        "boundary relative mixed derivative error": float(
            abs(
                boundary_relative_mixed_derivative
                - relative_covariance.real
            )
        ),
        "boundary covariance error": float(
            abs(boundary_covariance - covariance)
        ),
        "covariance imaginary residue": float(abs(covariance.imag)),
        "covariance magnitude": float(abs(covariance)),
        "relative E/R covariance magnitude": float(abs(relative_covariance)),
    }


def source_checks(
    model: dict[str, np.ndarray],
    detector: np.ndarray,
    generator: np.ndarray,
) -> tuple[dict[str, float], dict[str, float]]:
    transform = model["transform"]
    support_basis = model["support_basis"]
    graph = model["graph"]
    gram = model["gram"]
    complement = model["complement"]
    sonin = model["sonin"]
    outer = model["outer"]
    second = model["second"]
    prolate = model["prolate"]
    truncated_transform = model["truncated_transform"]
    size = transform.shape[0]
    support_rank = support_basis.shape[1]

    identity = np.eye(size, dtype=complex)
    small_identity = np.eye(support_rank, dtype=complex)
    block_hadamard = np.block(
        [[small_identity, small_identity], [small_identity, -small_identity]]
    ) / math.sqrt(2.0)
    expected_diagonal_gram = np.block(
        [
            [small_identity + truncated_transform, np.zeros_like(small_identity)],
            [np.zeros_like(small_identity), small_identity - truncated_transform],
        ]
    )

    inverse_difference = np.linalg.inv(
        small_identity + truncated_transform
    ) - np.linalg.inv(small_identity - truncated_transform)
    inverse_difference_expected = (
        -2.0
        * truncated_transform
        @ np.linalg.inv(
            small_identity - truncated_transform @ truncated_transform
        )
    )

    prolate_eigenvalues = np.linalg.eigvalsh(
        (prolate + prolate.conj().T) / 2.0
    )
    prolate_channel = np.sort(
        np.maximum(prolate_eigenvalues[-support_rank:], 0.0)
    )
    expected_prolate = np.sort(
        np.linalg.eigvalsh(
            truncated_transform @ truncated_transform
        )
    )

    covariance = np.trace(
        sonin @ detector @ complement @ generator @ sonin
    )
    toeplitz_basis = projection_basis(sonin)
    toeplitz_product = np.trace(
        toeplitz_basis.conj().T
        @ detector
        @ generator
        @ toeplitz_basis
        - (toeplitz_basis.conj().T @ detector @ toeplitz_basis)
        @ (toeplitz_basis.conj().T @ generator @ toeplitz_basis)
    )
    dirichlet = np.trace(
        commutator(detector, sonin).conj().T
        @ commutator(generator, sonin)
    )

    outer_left = outer @ second @ commutator(outer, generator)
    second_branch = outer @ commutator(second, generator) @ outer
    outer_right = commutator(outer, generator) @ second @ outer
    prolate_branch = -commutator(prolate, generator)
    branch_sum = outer_left + second_branch + outer_right + prolate_branch
    direct_sonin_commutator = commutator(sonin, generator)
    branch_dirichlet = np.trace(
        commutator(detector, sonin).conj().T @ (-branch_sum)
    )
    branch_norm_sum = sum(
        np.linalg.norm(branch, ord="fro")
        for branch in (
            outer_left,
            second_branch,
            outer_right,
            prolate_branch,
        )
    )
    complete_branch_norm = np.linalg.norm(branch_sum, ord="fro")

    algebra = {
        "Fourier surrogate involution error": float(
            np.linalg.norm(transform @ transform - identity, ord=2)
        ),
        "graph Gram block error": float(
            np.linalg.norm(
                gram
                - np.block(
                    [
                        [small_identity, truncated_transform],
                        [truncated_transform, small_identity],
                    ]
                ),
                ord=2,
            )
        ),
        "minimum graph Gram eigenvalue": float(
            np.linalg.eigvalsh(gram)[0]
        ),
        "complement projection error": float(
            np.linalg.norm(complement @ complement - complement, ord=2)
        ),
        "Sonin graph annihilation error": float(
            np.linalg.norm(graph.conj().T @ sonin, ord=2)
        ),
        "Sonin outer nesting error": float(
            np.linalg.norm(outer @ sonin - sonin, ord=2)
        ),
        "Sonin second-support nesting error": float(
            np.linalg.norm(second @ sonin - sonin, ord=2)
        ),
        "plus/minus Gram diagonalization error": float(
            np.linalg.norm(
                block_hadamard.conj().T @ gram @ block_hadamard
                - expected_diagonal_gram,
                ord=2,
            )
        ),
        "odd resolvent identity error": float(
            np.linalg.norm(
                inverse_difference - inverse_difference_expected, ord=2
            )
        ),
        "prolate spectrum error": float(
            np.max(np.abs(prolate_channel - expected_prolate))
        ),
    }
    covariance_checks = {
        "Toeplitz covariance error": float(abs(toeplitz_product - covariance)),
        "Dirichlet pairing error": float(abs(dirichlet - 2.0 * covariance)),
        "three-branch commutator error": float(
            np.linalg.norm(branch_sum - direct_sonin_commutator, ord=2)
        ),
        "three-branch Dirichlet error": float(
            abs(branch_dirichlet - dirichlet)
        ),
        "branch cancellation ratio": float(
            branch_norm_sum / max(complete_branch_norm, 1e-15)
        ),
        "complete branch norm": float(complete_branch_norm),
    }
    return algebra, covariance_checks


def print_checks(title: str, checks: dict[str, float]) -> None:
    width = max(len(label) for label in checks)
    border = f"+-{'-' * width}-+----------------+"
    print(title)
    print(border)
    print(f"| {'check':<{width}} | value          |")
    print(border)
    for label, value in checks.items():
        print(f"| {label:<{width}} | {value:>14.6e} |")
    print(border)


def zero_prolate_guard(
    size: int, support_rank: int, rng: np.random.Generator
) -> dict[str, float]:
    model = build_zero_prolate_model(size, support_rank)
    detector, generator, _, _, _ = build_commuting_multipliers(size, rng)
    sonin = model["sonin"]
    complement = model["complement"]
    outer = model["outer"]
    covariance = np.trace(
        sonin @ detector @ complement @ generator @ sonin
    )
    outer_covariance = np.trace(
        outer
        @ detector
        @ (np.eye(size, dtype=complex) - outer)
        @ generator
        @ outer
    )
    _, branch_checks = source_checks(model, detector, generator)
    return {
        "truncated Fourier norm": float(
            np.linalg.norm(model["truncated_transform"], ord=2)
        ),
        "prolate correction norm": float(
            np.linalg.norm(model["prolate"], ord=2)
        ),
        "Sonin covariance magnitude": float(abs(covariance)),
        "relative E/R covariance magnitude": float(
            abs(outer_covariance - covariance)
        ),
        "three-branch commutator error": branch_checks[
            "three-branch commutator error"
        ],
        "branch cancellation ratio": branch_checks[
            "branch cancellation ratio"
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=28)
    parser.add_argument("--support-rank", type=int, default=7)
    parser.add_argument("--seed", type=int, default=1278)
    parser.add_argument("--determinant-parameter", type=float, default=0.17)
    parser.add_argument("--derivative-step", type=float, default=7e-4)
    parser.add_argument("--algebra-tolerance", type=float, default=2e-10)
    parser.add_argument("--derivative-tolerance", type=float, default=2e-6)
    args = parser.parse_args()

    if args.size < 8:
        raise ValueError("size must be at least eight")
    if args.support_rank < 1 or 2 * args.support_rank >= args.size:
        raise ValueError("support-rank must satisfy 1 <= 2 rank < size")

    rng = np.random.default_rng(args.seed)
    model = build_source_model(args.size, args.support_rank, rng)
    (
        detector,
        generator,
        multiplier_basis,
        detector_values,
        generator_values,
    ) = build_commuting_multipliers(args.size, rng)

    algebra, covariance = source_checks(model, detector, generator)
    jacobi = jacobi_checks(
        model,
        detector,
        generator,
        multiplier_basis,
        detector_values,
        generator_values,
        args.determinant_parameter,
        args.derivative_step,
    )
    guard = zero_prolate_guard(
        args.size, args.support_rank, np.random.default_rng(args.seed + 991)
    )
    commuting_error = float(
        np.linalg.norm(commutator(detector, generator), ord=2)
    )
    algebra["multiplier commutation error"] = commuting_error

    print("identity=Burnol boundary Gram covariance and Jacobi complement")
    print("status=exact finite-dimensional algebra; continuous estimate open")
    print_checks("Source graph checks", algebra)
    print()
    print_checks("Covariance and physical-branch checks", covariance)
    print()
    print_checks("Jacobi determinant checks", jacobi)
    print()
    print_checks("Zero-prolate ownership guard", guard)

    algebra_errors = [
        value
        for label, value in algebra.items()
        if label != "minimum graph Gram eigenvalue"
    ]
    covariance_errors = [
        value
        for label, value in covariance.items()
        if label not in {"branch cancellation ratio", "complete branch norm"}
    ]
    exact_error = max(algebra_errors + covariance_errors)
    derivative_error = jacobi["mixed log-determinant derivative error"]
    relative_derivative_error = max(
        jacobi["relative E/R mixed derivative error"],
        jacobi["boundary relative mixed derivative error"],
    )
    determinant_error = max(
        jacobi["Jacobi complementary determinant error"],
        jacobi["relative E/R determinant error"],
        jacobi["boundary covariance error"],
        jacobi["covariance imaginary residue"],
    )
    print(f"maximum exact algebra error={exact_error:.12e}")
    print(f"maximum determinant identity error={determinant_error:.12e}")
    print(f"mixed derivative error={derivative_error:.12e}")
    print(f"relative mixed derivative error={relative_derivative_error:.12e}")

    if exact_error > args.algebra_tolerance:
        raise SystemExit(
            f"boundary Gram algebra failed: {exact_error:.6e}"
        )
    if determinant_error > args.algebra_tolerance:
        raise SystemExit(
            f"Jacobi determinant identity failed: {determinant_error:.6e}"
        )
    if derivative_error > args.derivative_tolerance:
        raise SystemExit(
            f"mixed determinant derivative failed: {derivative_error:.6e}"
        )
    if relative_derivative_error > args.derivative_tolerance:
        raise SystemExit(
            "relative mixed determinant derivative failed: "
            f"{relative_derivative_error:.6e}"
        )
    if guard["truncated Fourier norm"] > args.algebra_tolerance:
        raise SystemExit("zero-prolate guard has a nonzero truncated transform")
    if guard["prolate correction norm"] > args.algebra_tolerance:
        raise SystemExit("zero-prolate guard has a nonzero prolate correction")
    if guard["Sonin covariance magnitude"] < 1e-4:
        raise SystemExit("zero-prolate guard failed to retain a covariance")

    print("burnol_complement_projection=EXACT")
    print("boundary_gram_covariance=EXACT")
    print("jacobi_complementary_determinant=EXACT")
    print("relative_E_over_R_ambient_determinant_cancellation=EXACT")
    print("toeplitz_covariance_as_mixed_log_derivative=EXACT")
    print("outer_second_prolate_recombination=EXACT")
    print("prolate_only_extra_factor=REJECTED_BY_ZERO_PROLATE_GUARD")
    print("continuous_root_sandwiched_trace_domain=OPEN")
    print("relative_wiener_hopf_bogc=OPEN")
    print("complete_prime_telescope_through_boundary_gram=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
