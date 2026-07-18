"""Finite certificate for Proof 388's Gram/Julia alignment audit."""

from __future__ import annotations

import argparse

import numpy as np


def positive_inverse_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) <= 1e-12:
        raise ValueError("matrix is not strictly positive")
    return eigenvectors @ np.diag(eigenvalues**-0.5) @ eigenvectors.conj().T


def positive_square_root(matrix: np.ndarray) -> np.ndarray:
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    if float(np.min(eigenvalues)) < -1e-10:
        raise ValueError("matrix is not positive semidefinite")
    eigenvalues = np.maximum(eigenvalues, 0.0)
    return eigenvectors @ np.diag(np.sqrt(eigenvalues)) @ eigenvectors.conj().T


def orthogonal_complement(basis: np.ndarray) -> np.ndarray:
    _, _, right = np.linalg.svd(basis.conj().T, full_matrices=True)
    return right.conj().T[:, basis.shape[1] :]


def relative_error(actual: np.ndarray | complex, expected: np.ndarray | complex) -> float:
    return float(
        np.linalg.norm(np.asarray(actual) - np.asarray(expected))
        / max(1.0, float(np.linalg.norm(np.asarray(expected))))
    )


def graph_step(
    unitary: np.ndarray,
    basis: np.ndarray,
    coefficient: float,
) -> dict[str, np.ndarray]:
    complement = orthogonal_complement(basis)
    u_00 = basis.conj().T @ unitary @ basis
    u_01 = basis.conj().T @ unitary @ complement
    u_10 = complement.conj().T @ unitary @ basis
    u_11 = complement.conj().T @ unitary @ complement
    resolvent_times_u10 = np.linalg.solve(
        np.eye(u_11.shape[0], dtype=complex) - coefficient * u_11,
        u_10,
    )
    graph = coefficient * resolvent_times_u10
    transfer = u_00 + coefficient * u_01 @ resolvent_times_u10
    cosine = positive_inverse_square_root(
        np.eye(basis.shape[1], dtype=complex) + graph.conj().T @ graph
    )
    sine = graph @ cosine
    next_basis = basis @ cosine + complement @ sine
    defect = positive_square_root(
        np.eye(basis.shape[1], dtype=complex) - transfer.conj().T @ transfer
    )
    inverse_factor = np.linalg.inv(
        np.eye(unitary.shape[0], dtype=complex) - coefficient * unitary
    )
    return {
        "graph": graph,
        "transfer": transfer,
        "cosine": cosine,
        "sine": sine,
        "next basis": next_basis,
        "defect": defect,
        "inverse factor": inverse_factor,
    }


def normalized_prefix(prefix: np.ndarray, source: np.ndarray) -> np.ndarray:
    raw = prefix @ source
    gram = raw.conj().T @ raw
    return raw @ positive_inverse_square_root(gram)


def generic_cohort(size: int, rank: int, seed: int) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    source_raw = (
        rng.normal(size=(size, rank)) + 1j * rng.normal(size=(size, rank))
    )
    source, _ = np.linalg.qr(source_raw)

    spectral_basis, _ = np.linalg.qr(
        rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    )
    frequencies = np.linspace(-1.7, 2.1, size)

    def translation(time: float) -> np.ndarray:
        return (
            spectral_basis
            @ np.diag(np.exp(1j * time * frequencies))
            @ spectral_basis.conj().T
        )

    primes = [2, 3, 5, 7]
    graph_basis = source.copy()
    prefix = np.eye(size, dtype=complex)
    psi = np.eye(rank, dtype=complex)
    root_input = (
        rng.normal(size=(rank, rank + 1))
        + 1j * rng.normal(size=(rank, rank + 1))
    ) / np.sqrt(2.0 * rank)

    maximum_graph_error = 0.0
    maximum_range_error = 0.0
    maximum_cocycle_error = 0.0
    maximum_cocycle_unitary_error = 0.0
    maximum_isometry_error = 0.0
    maximum_bessel_violation = 0.0
    maximum_right_leg_mismatch = 0.0
    defect_energy = 0.0

    for prime in primes:
        direct_frame = normalized_prefix(prefix, source)
        cocycle = graph_basis.conj().T @ direct_frame
        maximum_range_error = max(
            maximum_range_error,
            relative_error(
                graph_basis @ graph_basis.conj().T,
                direct_frame @ direct_frame.conj().T,
            ),
        )
        maximum_cocycle_error = max(
            maximum_cocycle_error,
            relative_error(direct_frame, graph_basis @ cocycle),
        )
        maximum_cocycle_unitary_error = max(
            maximum_cocycle_unitary_error,
            relative_error(
                cocycle.conj().T @ cocycle,
                np.eye(rank, dtype=complex),
            ),
        )

        coefficient = prime**-0.5
        step = graph_step(translation(np.log(prime)), graph_basis, coefficient)
        transfer = step["transfer"]
        graph = step["graph"]
        defect = step["defect"]
        sine = step["sine"]
        defect_square = np.eye(rank) - transfer.conj().T @ transfer
        graph_expected = (
            coefficient**2 / (1.0 - coefficient**2) * defect_square
        )
        maximum_graph_error = max(
            maximum_graph_error,
            relative_error(graph.conj().T @ graph, graph_expected),
        )

        physical_right = sine @ cocycle @ root_input
        julia_right = sine @ psi @ root_input
        maximum_right_leg_mismatch = max(
            maximum_right_leg_mismatch,
            float(np.linalg.norm(physical_right - julia_right, "fro")),
        )

        defect_slot = defect @ psi @ root_input
        defect_energy += float(np.linalg.norm(defect_slot, "fro") ** 2)
        weighted_range_energy = (prime - 1.0) * float(
            np.linalg.norm(julia_right, "fro") ** 2
        )
        maximum_bessel_violation = max(
            maximum_bessel_violation,
            weighted_range_energy
            - float(np.linalg.norm(defect_slot, "fro") ** 2),
        )

        psi = transfer @ psi
        graph_basis = step["next basis"]
        prefix = step["inverse factor"] @ prefix
        maximum_isometry_error = max(
            maximum_isometry_error,
            relative_error(
                graph_basis.conj().T @ graph_basis,
                np.eye(rank, dtype=complex),
            ),
        )

    defect_energy += float(np.linalg.norm(psi @ root_input, "fro") ** 2)
    telescope_error = relative_error(
        defect_energy,
        np.linalg.norm(root_input, "fro") ** 2,
    )

    return {
        "generic graph defect error": maximum_graph_error,
        "generic direct range error": maximum_range_error,
        "generic cocycle identity error": maximum_cocycle_error,
        "generic cocycle unitary error": maximum_cocycle_unitary_error,
        "generic graph frame isometry error": maximum_isometry_error,
        "generic Julia telescope error": telescope_error,
        "generic Julia Bessel violation": max(0.0, maximum_bessel_violation),
        "generic maximum right leg mismatch": maximum_right_leg_mismatch,
        "generic Psi isometry defect": float(
            np.linalg.norm(np.eye(rank) - psi.conj().T @ psi, 2)
        ),
    }


def exact_kernel_guard() -> dict[str, float]:
    coefficient_two = 2.0**-0.5
    complement = np.sqrt(1.0 - coefficient_two**2)
    first_translation = np.array(
        [
            [-coefficient_two, complement],
            [complement, coefficient_two],
        ],
        dtype=complex,
    )
    eigenvalues, eigenvectors = np.linalg.eigh(first_translation)
    frequencies = np.where(eigenvalues < 0.0, np.pi / np.log(2.0), 0.0)

    def translation(time: float) -> np.ndarray:
        return (
            eigenvectors
            @ np.diag(np.exp(1j * time * frequencies))
            @ eigenvectors.conj().T
        )

    source = np.array([[1.0], [0.0]], dtype=complex)
    first = graph_step(translation(np.log(2.0)), source, coefficient_two)
    first_basis = first["next basis"]
    first_prefix = first["inverse factor"]
    first_direct_frame = normalized_prefix(first_prefix, source)
    first_cocycle = first_basis.conj().T @ first_direct_frame

    second = graph_step(
        translation(np.log(3.0)),
        first_basis,
        3.0**-0.5,
    )
    physical_right = second["sine"] @ first_cocycle
    julia_right = second["sine"] @ first["transfer"]

    return {
        "guard first translation error": relative_error(
            translation(np.log(2.0)),
            first_translation,
        ),
        "guard first transfer norm": float(np.linalg.norm(first["transfer"], 2)),
        "guard first cocycle unitary error": relative_error(
            first_cocycle.conj().T @ first_cocycle,
            np.ones((1, 1), dtype=complex),
        ),
        "guard Julia second leg norm": float(np.linalg.norm(julia_right, 2)),
        "guard physical second leg norm": float(np.linalg.norm(physical_right, 2)),
        "guard Douglas kernel leakage": float(np.linalg.norm(physical_right, 2)),
        "guard second sine norm": float(np.linalg.norm(second["sine"], 2)),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--rank", type=int, default=5)
    parser.add_argument("--seed", type=int, default=388)
    parser.add_argument("--tolerance", type=float, default=5e-10)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    checks = generic_cohort(args.size, args.rank, args.seed)
    checks.update(exact_kernel_guard())
    print("Proof 388 Gram/Julia prefix alignment audit certificate")
    for label, value in checks.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")

    exact_labels = [
        "generic graph defect error",
        "generic direct range error",
        "generic cocycle identity error",
        "generic cocycle unitary error",
        "generic graph frame isometry error",
        "generic Julia telescope error",
        "generic Julia Bessel violation",
        "guard first translation error",
        "guard first transfer norm",
        "guard first cocycle unitary error",
        "guard Julia second leg norm",
    ]
    maximum_error = max(checks[label] for label in exact_labels)
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Gram/Julia audit failed: {maximum_error:.3e}")

    if checks["generic maximum right leg mismatch"] <= 1e-5:
        raise RuntimeError("generic physical/Julia mismatch is too small")
    if checks["generic Psi isometry defect"] <= 1e-5:
        raise RuntimeError("generic Julia prefix is accidentally unitary")
    if checks["guard physical second leg norm"] <= 1e-5:
        raise RuntimeError("exact guard has no physical kernel leakage")

    print(f"maximum_exact_error_or_violation={maximum_error:.12e}")
    print("gram_to_sequential_frame_cocycle=UNITARY")
    print("automatic_gram_to_julia_alignment=REJECTED")
    print("abstract_julia_douglas_kernel_condition=REJECTED")
    print("source_specific_causal_insertion=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
