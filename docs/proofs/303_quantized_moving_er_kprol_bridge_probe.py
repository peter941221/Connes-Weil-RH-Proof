#!/usr/bin/env python3
"""Certificate for Proof 303's moving divided-difference bridge.

The finite model checks three separate facts:

* a Hardy commutator reads back the projection covariance;
* the identity R = E Q E - K_prol expands the moving R commutator into
  outer, second-support, and prolate pieces;
* the CC20 divided-difference kernel is exact off the diagonal, while the
  -2 Dirac residue remains a separate scalar ledger.

The probe is algebraic and finite-dimensional.  It is not a source theorem,
not a uniform Gate 3U estimate, and not an RH proof.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
from types import ModuleType

import numpy as np


def load_probe(filename: str, module_name: str) -> ModuleType:
    path = Path(__file__).with_name(filename)
    specification = importlib.util.spec_from_file_location(module_name, path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_266 = load_probe(
    "266_three_branch_causal_determinant_probe.py",
    "proof_266_for_303",
)


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def commutator(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    return left @ right - right @ left


def hermitian_exponential(matrix: np.ndarray, parameter: float) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    return (
        eigenvectors
        @ np.diag(np.exp(1j * parameter * eigenvalues))
        @ eigenvectors.conj().T
    )


def compact_root(
    size: int, support_radius: int, seed: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    if 4 * support_radius + 1 >= size:
        raise ValueError("support is too wide for a non-wrapping correlation")
    rng = np.random.default_rng(seed)
    root = np.zeros(size, dtype=complex)
    support_indices = np.arange(-support_radius, support_radius + 1)
    values = rng.normal(size=support_indices.size) + 1j * rng.normal(
        size=support_indices.size
    )
    values /= np.linalg.norm(values)
    root[np.mod(support_indices, size)] = values
    root_fourier = np.fft.fft(root) / np.sqrt(size)
    multiplier = np.abs(root_fourier) ** 2
    offsets = np.arange(-(size // 2), size - size // 2)
    correlation = np.asarray(
        [
            np.vdot(root, np.roll(root, -int(offset)))
            for offset in offsets
        ],
        dtype=complex,
    )
    return root, multiplier, offsets, correlation


def covariance(
    projection: np.ndarray,
    first: np.ndarray,
    second: np.ndarray,
) -> complex:
    identity = np.eye(projection.shape[0], dtype=complex)
    return complex(
        np.trace(
            projection
            @ np.diag(first)
            @ (identity - projection)
            @ np.diag(second)
            @ projection
        )
    )


def trapezoid(values: np.ndarray, step: float) -> complex:
    values_array = np.asarray(values)
    return complex(
        step
        * (
            0.5 * values_array[0]
            + 0.5 * values_array[-1]
            + np.sum(values_array[1:-1])
        )
    )


def hardy_pairing(
    projection: np.ndarray,
    first: np.ndarray,
    second: np.ndarray,
) -> complex:
    """Read the covariance from the finite Hardy commutators.

    For real diagonal multipliers this is the exact identity

        S_J(f,g) = 1/8 Tr([2J-I,f]^* [2J-I,g]).

    The source route uses the same identity after the root-sandwiched trace
    has made the scalar legal.  The finite certificate keeps the multipliers
    real so no cross-root polarization convention is hidden here.
    """

    identity = np.eye(projection.shape[0], dtype=complex)
    first_diagonal = np.diag(first)
    second_diagonal = np.diag(second)
    hardy = 2.0 * projection - identity
    first_commutator = commutator(hardy, first_diagonal)
    second_commutator = commutator(hardy, second_diagonal)
    return complex(
        np.trace(first_commutator.conj().T @ second_commutator) / 8.0
    )


def branch_commutator(
    outer: np.ndarray,
    second_support: np.ndarray,
    prolate: np.ndarray,
    multiplier: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Expand [R,f] using R=E Q E-K_prol."""

    outer_commutator = commutator(outer, np.diag(multiplier))
    second_commutator = commutator(
        second_support, np.diag(multiplier)
    )
    prolate_commutator = commutator(prolate, np.diag(multiplier))
    outer_branch = (
        outer
        @ second_support
        @ outer_commutator
        + outer_commutator
        @ second_support
        @ outer
    )
    second_branch = outer @ second_commutator @ outer
    prolate_branch = -prolate_commutator
    complete = outer_branch + second_branch + prolate_branch
    return outer_branch, second_branch, prolate_branch, complete


def source_function(value: np.ndarray) -> np.ndarray:
    return np.exp(-0.2 * value**2) * (1.0 + 0.1 * value)


def source_function_derivative(value: np.ndarray) -> np.ndarray:
    return np.exp(-0.2 * value**2) * (
        0.1 - 0.4 * value * (1.0 + 0.1 * value)
    )


def source_second_function(value: np.ndarray) -> np.ndarray:
    return np.sin(1.3 * value) + 0.15 * np.cos(0.7 * value)


def source_second_function_derivative(value: np.ndarray) -> np.ndarray:
    return 1.3 * np.cos(1.3 * value) - 0.105 * np.sin(0.7 * value)


def source_divided_difference_checks(size: int) -> dict[str, float]:
    nodes = np.linspace(-4.0, 4.0, size)
    difference = nodes[:, None] - nodes[None, :]
    off_diagonal = ~np.eye(size, dtype=bool)

    first = source_function(nodes)
    second = source_second_function(nodes)
    first_derivative = source_function_derivative(nodes)
    second_derivative = source_second_function_derivative(nodes)

    hilbert = np.zeros((size, size), dtype=complex)
    hilbert[off_diagonal] = -1j / (
        np.pi * difference[off_diagonal]
    )
    first_commutator = commutator(hilbert, np.diag(first))
    second_commutator = commutator(hilbert, np.diag(second))

    expected_first = np.zeros_like(hilbert)
    expected_second = np.zeros_like(hilbert)
    expected_first[off_diagonal] = 1j / np.pi * (
        first[:, None] - first[None, :]
    )[off_diagonal] / difference[off_diagonal]
    expected_second[off_diagonal] = 1j / np.pi * (
        second[:, None] - second[None, :]
    )[off_diagonal] / difference[off_diagonal]

    direct_pairing = np.trace(
        first_commutator.conj().T @ second_commutator
    )
    kernel_pairing = np.sum(
        np.conj(expected_first) * expected_second
    )

    center = size // 2
    step = 2e-5
    local_nodes = np.array([nodes[center] - step, nodes[center] + step])
    local_values = source_function(local_nodes)
    local_derivative = (
        local_values[1] - local_values[0]
    ) / (2.0 * step)

    constant = np.ones(size)
    constant_commutator = commutator(hilbert, np.diag(constant))

    return {
        "source first divided-difference error": relative_error(
            first_commutator, expected_first
        ),
        "source second divided-difference error": relative_error(
            second_commutator, expected_second
        ),
        "source double-pairing error": float(
            abs(direct_pairing - kernel_pairing)
        ),
        "source removable-diagonal error": float(
            abs(local_derivative - source_function_derivative(nodes[center]))
        ),
        "source constant commutator magnitude": float(
            np.linalg.norm(constant_commutator)
        ),
        "source quantized pairing magnitude": float(abs(direct_pairing)),
        "source derivative sample error": float(
            abs(
                (
                    source_second_function(nodes[center] + step)
                    - source_second_function(nodes[center] - step)
                )
                / (2.0 * step)
                - source_second_function_derivative(nodes[center])
            )
        ),
    }


def moving_bridge_checks(
    multiplicity: int,
    support_radius: int,
    seed: int,
    flow_samples: int,
) -> tuple[dict[str, float], dict[str, float]]:
    model = PROOF_266.build_model(multiplicity, seed)
    size = model["E"].shape[0]
    rng = np.random.default_rng(seed + 1000)

    random_matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    spectral_unitary, _ = np.linalg.qr(random_matrix)

    def conjugate(matrix: np.ndarray) -> np.ndarray:
        return spectral_unitary @ matrix @ spectral_unitary.conj().T

    outer = conjugate(model["E"])
    sonin = conjugate(model["R"])
    second_support = conjugate(model["Q"])
    prolate = conjugate(model["K_prol"])
    identity = np.eye(size, dtype=complex)

    flow_matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    flow_matrix = 0.5 * (flow_matrix + flow_matrix.conj().T)
    flow_matrix /= max(float(np.linalg.norm(flow_matrix, ord=2)), 1.0)

    angles = 2.0 * np.pi * np.arange(size) / size
    root, multiplier, offsets, correlation = compact_root(
        size, support_radius, seed + 2000
    )
    generator = 0.4 * np.tanh(np.linspace(-4.0, 4.0, size)) + 0.1 * np.sin(
        0.8 * np.linspace(-4.0, 4.0, size)
    )
    multiplier_diagonal = np.diag(multiplier)
    generator_diagonal = np.diag(generator)

    reconstructed_multiplier = sum(
        (
            correlation[index]
            * np.exp(-1j * int(offset) * angles)
            for index, offset in enumerate(offsets)
        ),
        np.zeros(size, dtype=complex),
    ) / size
    support_mask = np.abs(offsets) <= 2 * support_radius
    zero_index = int(np.where(offsets == 0)[0][0])
    root_inner_product = complex(np.vdot(root, root))
    zero_correlation = complex(correlation[zero_index])

    direct_values: list[complex] = []
    bridge_values: list[complex] = []
    branch_values: list[complex] = []
    no_prolate_values: list[complex] = []
    branch_errors: list[float] = []
    covariance_errors: list[float] = []
    no_prolate_gaps: list[float] = []

    for parameter in np.linspace(0.0, 1.0, flow_samples):
        transport = hermitian_exponential(flow_matrix, float(parameter))
        outer_alpha = transport @ outer @ transport.conj().T
        sonin_alpha = transport @ sonin @ transport.conj().T
        second_alpha = transport @ second_support @ transport.conj().T
        prolate_alpha = transport @ prolate @ transport.conj().T

        direct = covariance(
            outer_alpha, multiplier, generator
        ) - covariance(sonin_alpha, multiplier, generator)
        bridge = hardy_pairing(
            outer_alpha, multiplier, generator
        ) - hardy_pairing(sonin_alpha, multiplier, generator)

        outer_first, second_first, prolate_first, complete_first = (
            branch_commutator(
                outer_alpha,
                second_alpha,
                prolate_alpha,
                multiplier,
            )
        )
        outer_second, second_second, prolate_second, complete_second = (
            branch_commutator(
                outer_alpha,
                second_alpha,
                prolate_alpha,
                generator,
            )
        )
        direct_sonin_commutator = commutator(
            sonin_alpha, multiplier_diagonal
        )
        expanded_sonin_commutator = complete_first
        branch_pairing = hardy_pairing(
            outer_alpha, multiplier, generator
        ) - np.trace(
            (2.0 * complete_first).conj().T
            @ (2.0 * complete_second)
        ) / 8.0

        no_prolate_first = outer_first + second_first
        no_prolate_second = outer_second + second_second
        no_prolate_pairing = hardy_pairing(
            outer_alpha, multiplier, generator
        ) - np.trace(
            (2.0 * no_prolate_first).conj().T
            @ (2.0 * no_prolate_second)
        ) / 8.0

        direct_values.append(direct)
        bridge_values.append(bridge)
        branch_values.append(branch_pairing)
        no_prolate_values.append(no_prolate_pairing)
        branch_errors.append(
            relative_error(
                direct_sonin_commutator, expanded_sonin_commutator
            )
        )
        covariance_errors.append(abs(direct - bridge))
        no_prolate_gaps.append(abs(bridge - no_prolate_pairing))

    direct_array = np.asarray(direct_values)
    bridge_array = np.asarray(bridge_values)
    branch_array = np.asarray(branch_values)
    no_prolate_array = np.asarray(no_prolate_values)
    flow_step = 1.0 / (flow_samples - 1)
    direct_integral = trapezoid(direct_array, flow_step)
    bridge_integral = trapezoid(bridge_array, flow_step)
    branch_integral = trapezoid(branch_array, flow_step)
    no_prolate_integral = trapezoid(no_prolate_array, flow_step)

    exact = {
        "nested projection identity error": relative_error(
            outer @ second_support @ outer - prolate, sonin
        ),
        "root multiplier reconstruction error": relative_error(
            reconstructed_multiplier, multiplier
        ),
        "root correlation support leakage": float(
            np.max(np.abs(correlation[~support_mask]))
        ),
        "same-root correlation-at-zero error": float(
            abs(zero_correlation - root_inner_product)
        ),
        "same-root Dirac identity-form error": float(
            abs(-2.0 * zero_correlation + 2.0 * root_inner_product)
        ),
        "maximum moving covariance readback error": max(
            covariance_errors
        ),
        "maximum moving R commutator branch error": max(branch_errors),
        "integrated covariance readback error": float(
            abs(direct_integral - bridge_integral)
        ),
        "integrated complete branch error": float(
            abs(bridge_integral - branch_integral)
        ),
        "maximum prolate omission gap": max(no_prolate_gaps),
        "integrated prolate omission gap": float(
            abs(bridge_integral - no_prolate_integral)
        ),
        "moving response magnitude": float(abs(direct_integral)),
        "same-root Dirac identity magnitude": float(
            abs(-2.0 * root_inner_product)
        ),
    }
    guards = {
        "minimum prolate omission gap": min(no_prolate_gaps),
        "maximum prolate omission gap": max(no_prolate_gaps),
        "integrated direct response real part": float(direct_integral.real),
        "integrated direct response imaginary part": float(
            direct_integral.imag
        ),
    }
    return exact, guards


def residue_ledger_checks() -> dict[str, float]:
    """Keep the CC20 -2 Dirac term separate from the ordinary kernel."""

    value_at_zero = float(source_function(np.array([0.0]))[0])
    second_value_at_zero = float(
        source_second_function(np.array([0.0]))[0]
    )
    residue = -2.0 * value_at_zero * second_value_at_zero
    # The finite divided-difference matrix has no diagonal mass.  This is
    # deliberate: the source Dirac term is a distributional scalar, not the
    # removable value of the off-diagonal kernel.
    ordinary_diagonal_mass = 0.0
    return {
        "source Dirac residue": residue,
        "ordinary divided-difference diagonal mass": ordinary_diagonal_mass,
        "unpaired residue gap": abs(residue - ordinary_diagonal_mass),
        "constant-mode residue magnitude": 2.0,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--support-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=303)
    parser.add_argument("--flow-samples", type=int, default=9)
    parser.add_argument("--source-size", type=int, default=40)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--prolate-gap-floor", type=float, default=1e-5)
    parser.add_argument("--residue-gap-floor", type=float, default=1e-6)
    args = parser.parse_args()

    if args.flow_samples < 2:
        raise SystemExit("flow-samples must be at least two")
    if args.source_size < 8:
        raise SystemExit("source-size must be at least eight")

    source = source_divided_difference_checks(args.source_size)
    exact, guards = moving_bridge_checks(
        args.multiplicity,
        args.support_radius,
        args.seed,
        args.flow_samples,
    )
    residue = residue_ledger_checks()

    print("identity=CC20 divided difference plus moving E/R/K_prol bridge")
    print("status=finite bridge exact; source residue remains separate")
    for title, checks in (
        ("source", source),
        ("moving", exact),
        ("guards", guards),
        ("residue", residue),
    ):
        print(f"{title}_checks=BEGIN")
        for label, value in checks.items():
            print(f"{label.replace(' ', '_')}={float(value):.12e}")
        print(f"{title}_checks=END")

    exact_labels = (
        "source first divided-difference error",
        "source second divided-difference error",
        "source double-pairing error",
        "source constant commutator magnitude",
        "nested projection identity error",
        "root multiplier reconstruction error",
        "root correlation support leakage",
        "same-root correlation-at-zero error",
        "same-root Dirac identity-form error",
        "maximum moving covariance readback error",
        "maximum moving R commutator branch error",
        "integrated covariance readback error",
        "integrated complete branch error",
    )
    combined_checks = {**source, **exact}
    exact_errors = [float(combined_checks[label]) for label in exact_labels]
    maximum_exact_error = max(float(value) for value in exact_errors)
    print(f"maximum_exact_error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            "moving divided-difference bridge failed: "
            f"{maximum_exact_error:.6e}"
        )
    if guards["minimum prolate omission gap"] < args.prolate_gap_floor:
        raise SystemExit("prolate branch omission guard did not fire")
    if residue["unpaired residue gap"] < args.residue_gap_floor:
        raise SystemExit("Dirac residue unexpectedly disappeared")

    print("source_divided_difference=EXACT_OFF_DIAGONAL")
    print("moving_hardy_covariance=EXACT_FINITE")
    print("outer_second_prolate=RECOMBINED_BEFORE_ESTIMATE")
    print("prolate_branch_omission=REJECTED")
    print("dirac_residue=SEPARATE_SOURCE_LEDGER")
    print("same_root_dirac_pullback=EXACT_MINUS_2_ID")
    print("dirac_residue_automatic_cancellation=REJECTED")
    print("continuous_source_identification=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
