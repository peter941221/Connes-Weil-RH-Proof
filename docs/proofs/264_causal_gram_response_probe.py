#!/usr/bin/env python3
"""Certificate for the causal Gram endpoint response.

Proof 264 combines the nested Schur frame from Proof 255 with the one-sided
coframe collapse from Proof 256.  For the causal inverse A = T^-1, put

    K = E A B,  Gamma = K* K.

The exact fixed-S response is

    Tr_B(K* W K Gamma^-1 - B W B).

The first certificate checks the generic shorted-covariance identities.  The
second checks the causal factorization with an exact triangular spectral
factor.  The third checks the complete response on a finite normal model where
the preserved complement is reducing.  No finite normal matrix can model the
source's nonreducing invariant half-line, so these layers are deliberately
separate.

The final certificate guards against an invalid infinite-dimensional polar
cycle.  Finite unilateral-shift sections have zero total trace, while their
left boundary converges to the nonzero trace of the infinite similarity
difference and the artificial right boundary carries the opposite mass.
"""

from __future__ import annotations

import argparse

import numpy as np


def basis_block(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    denominator = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / denominator)


def positive_matrix(
    rng: np.random.Generator, size: int, floor: float = 0.8
) -> np.ndarray:
    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    return random.conj().T @ random / size + floor * np.eye(size)


def stable_invertible(
    rng: np.random.Generator, size: int, scale: float
) -> np.ndarray:
    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    random /= max(float(np.linalg.norm(random, ord=2)), 1e-15)
    return np.eye(size, dtype=complex) + scale * random


def inverse_sqrt(operator: np.ndarray) -> np.ndarray:
    hermitian = (operator + operator.conj().T) / 2.0
    eigenvalues, eigenvectors = np.linalg.eigh(hermitian)
    if float(eigenvalues.min()) <= 0.0:
        raise ValueError("inverse square root requires positivity")
    return (
        eigenvectors
        * (1.0 / np.sqrt(eigenvalues))
    ) @ eigenvectors.conj().T


def metric_projection(
    source: np.ndarray, transport: np.ndarray, metric: np.ndarray
) -> np.ndarray:
    identity = np.eye(source.shape[0], dtype=complex)
    inverse = np.linalg.inv(source @ metric @ source + identity - source)
    return transport @ source @ inverse @ source @ transport.conj().T


def generic_shorted_certificate(size: int, seed: int) -> dict[str, float]:
    if size < 12:
        raise ValueError("generic certificate size must be at least 12")

    rng = np.random.default_rng(seed)
    c_rank = size // 3
    r_rank = size // 4
    b_rank = size - c_rank - r_rank
    c_basis = basis_block(size, 0, c_rank)
    r_basis = basis_block(size, c_rank, c_rank + r_rank)
    b_basis = basis_block(size, c_rank + r_rank, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)

    metric = positive_matrix(rng, size)
    inverse_metric = np.linalg.inv(metric)
    c_covariance = c_basis.conj().T @ inverse_metric @ c_basis
    shorted_covariance = (
        e_basis.conj().T @ inverse_metric @ e_basis
        - e_basis.conj().T
        @ inverse_metric
        @ c_basis
        @ np.linalg.solve(
            c_covariance,
            c_basis.conj().T @ inverse_metric @ e_basis,
        )
    )
    s_rb = shorted_covariance[:r_rank, r_rank:]
    s_bb = shorted_covariance[r_rank:, r_rank:]

    h_rr = r_basis.conj().T @ metric @ r_basis
    h_rb = r_basis.conj().T @ metric @ b_basis
    graph = np.linalg.solve(h_rr, h_rb)
    source_frame = b_basis - r_basis @ graph
    schur = source_frame.conj().T @ metric @ source_frame

    shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        c_covariance,
        c_basis.conj().T @ inverse_metric @ b_basis,
    )
    coframe = metric @ source_frame @ np.linalg.inv(schur)

    return {
        "graph_covariance_error": relative_error(
            graph, -s_rb @ np.linalg.inv(s_bb)
        ),
        "schur_covariance_error": relative_error(
            schur, np.linalg.inv(s_bb)
        ),
        "coframe_covariance_error": relative_error(
            shorted_coframe.conj().T
            @ inverse_metric
            @ shorted_coframe,
            s_bb,
        ),
        "coframe_frame_error": relative_error(shorted_coframe, coframe),
        "frame_covariance_error": relative_error(
            source_frame,
            inverse_metric @ shorted_coframe @ np.linalg.inv(s_bb),
        ),
    }


def triangular_causal_certificate(size: int, seed: int) -> dict[str, float]:
    if size < 12:
        raise ValueError("causal certificate size must be at least 12")

    rng = np.random.default_rng(seed + 1)
    c_rank = size // 3
    r_rank = size // 4
    b_rank = size - c_rank - r_rank
    e_rank = r_rank + b_rank
    c_basis = basis_block(size, 0, c_rank)
    r_basis = basis_block(size, c_rank, c_rank + r_rank)
    b_basis = basis_block(size, c_rank + r_rank, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    e_projection = projection(e_basis)

    a_c = stable_invertible(rng, c_rank, 0.18)
    a_e = stable_invertible(rng, e_rank, 0.16)
    crossing = rng.normal(size=(c_rank, e_rank)) + 1j * rng.normal(
        size=(c_rank, e_rank)
    )
    crossing *= 0.12 / max(float(np.linalg.norm(crossing, ord=2)), 1e-15)
    causal_inverse = np.block(
        [
            [a_c, crossing],
            [np.zeros((e_rank, c_rank), dtype=complex), a_e],
        ]
    )
    transport = np.linalg.inv(causal_inverse)
    inverse_metric = causal_inverse.conj().T @ causal_inverse
    metric = np.linalg.inv(inverse_metric)

    c_covariance = c_basis.conj().T @ inverse_metric @ c_basis
    shorted_covariance = (
        e_basis.conj().T @ inverse_metric @ e_basis
        - e_basis.conj().T
        @ inverse_metric
        @ c_basis
        @ np.linalg.solve(
            c_covariance,
            c_basis.conj().T @ inverse_metric @ e_basis,
        )
    )
    killed_factor = e_projection @ causal_inverse @ e_basis
    expected_covariance = killed_factor.conj().T @ killed_factor
    killed_band = e_projection @ causal_inverse @ b_basis
    s_bb = shorted_covariance[r_rank:, r_rank:]

    shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        c_covariance,
        c_basis.conj().T @ inverse_metric @ b_basis,
    )
    causal_coframe = transport @ e_projection @ causal_inverse @ b_basis

    h_rr = r_basis.conj().T @ metric @ r_basis
    graph = np.linalg.solve(
        h_rr, r_basis.conj().T @ metric @ b_basis
    )
    source_frame = b_basis - r_basis @ graph
    schur = source_frame.conj().T @ metric @ source_frame

    return {
        "preserved_complement_error": float(
            np.linalg.norm(e_basis.conj().T @ causal_inverse @ c_basis)
        ),
        "causal_covariance_error": relative_error(
            shorted_covariance, expected_covariance
        ),
        "band_gram_error": relative_error(s_bb, killed_band.conj().T @ killed_band),
        "causal_coframe_error": relative_error(
            shorted_coframe, causal_coframe
        ),
        "causal_schur_error": relative_error(schur, np.linalg.inv(s_bb)),
    }


def normal_response_certificate(size: int, seed: int) -> dict[str, float]:
    if size < 12:
        raise ValueError("normal response size must be at least 12")

    rng = np.random.default_rng(seed + 2)
    c_rank = size // 4
    e_rank = size - c_rank
    r_rank = e_rank // 3
    b_rank = e_rank - r_rank
    c_basis = basis_block(size, 0, c_rank)
    e_basis = basis_block(size, c_rank, size)
    c_projection = projection(c_basis)
    e_projection = projection(e_basis)

    random_e = rng.normal(size=(e_rank, e_rank)) + 1j * rng.normal(
        size=(e_rank, e_rank)
    )
    e_unitary, _ = np.linalg.qr(random_e)
    r_basis = e_basis @ e_unitary[:, :r_rank]
    b_basis = e_basis @ e_unitary[:, r_rank:]
    r_projection = projection(r_basis)
    b_projection = projection(b_basis)

    amplitudes = np.linspace(0.8, 1.4, size)
    phases = np.linspace(-0.7, 0.9, size)
    diagonal = amplitudes * np.exp(1j * phases)
    transport = np.diag(diagonal)
    causal_inverse = np.diag(1.0 / diagonal)
    metric = transport.conj().T @ transport
    inverse_metric = np.linalg.inv(metric)
    detector_values = np.linspace(-0.4, 1.1, size) ** 2 + 0.3
    detector = np.diag(detector_values)

    transported_outer = metric_projection(e_projection, transport, metric)
    transported_inner = metric_projection(r_projection, transport, metric)
    transported_band = transported_outer - transported_inner
    direct_response = np.trace(
        detector @ (transported_band - b_projection)
    )

    h_rr = r_basis.conj().T @ metric @ r_basis
    graph = np.linalg.solve(
        h_rr, r_basis.conj().T @ metric @ b_basis
    )
    source_frame = b_basis - r_basis @ graph
    schur = source_frame.conj().T @ metric @ source_frame
    coframe = metric @ source_frame @ np.linalg.inv(schur)
    detector_b = b_basis.conj().T @ detector @ b_basis
    intrinsic_response = np.trace(
        coframe.conj().T
        @ (detector @ source_frame - source_frame @ detector_b)
    )

    killed_band = e_projection @ causal_inverse @ b_basis
    gram = killed_band.conj().T @ killed_band
    gram_response = np.trace(
        killed_band.conj().T
        @ detector
        @ killed_band
        @ np.linalg.inv(gram)
        - detector_b
    )
    polar_isometry = killed_band @ inverse_sqrt(gram)
    polar_response = np.trace(
        polar_isometry.conj().T
        @ detector
        @ polar_isometry
        - detector_b
    )

    shorted_coframe = b_basis - c_basis @ np.linalg.solve(
        c_basis.conj().T @ inverse_metric @ c_basis,
        c_basis.conj().T @ inverse_metric @ b_basis,
    )
    causal_coframe = transport @ e_projection @ causal_inverse @ b_basis

    return {
        "normality_error": float(
            np.linalg.norm(
                transport.conj().T @ transport
                - transport @ transport.conj().T
            )
        ),
        "detector_commutator_error": float(
            np.linalg.norm(detector @ transport - transport @ detector)
        ),
        "reducing_complement_error": float(
            np.linalg.norm(e_projection @ causal_inverse @ c_projection)
        ),
        "normal_coframe_error": relative_error(
            shorted_coframe, causal_coframe
        ),
        "intrinsic_response_error": relative_error(
            intrinsic_response, direct_response
        ),
        "gram_response_error": relative_error(
            gram_response, direct_response
        ),
        "finite_polar_cycle_error": relative_error(
            polar_response, gram_response
        ),
    }


def similarity_anomaly_rows(
    sizes: list[int], time: float
) -> tuple[list[dict[str, float]], float]:
    if not sizes or any(size < 24 for size in sizes):
        raise ValueError("anomaly sizes must all be at least 24")
    if time <= 0.0:
        raise ValueError("anomaly time must be positive")

    rows: list[dict[str, float]] = []
    maximum_error = 0.0
    target = -0.5j * time
    for size in sizes:
        shift = np.zeros((size, size), dtype=complex)
        shift[1:, :-1] = np.eye(size - 1)
        real_part = (shift + shift.conj().T) / 2.0
        imaginary_part = (shift - shift.conj().T) / (2.0j)
        detector = imaginary_part + 2.0 * np.eye(size)

        eigenvalues, eigenvectors = np.linalg.eigh(real_part)
        similarity = (
            eigenvectors * np.exp(time * eigenvalues)
        ) @ eigenvectors.conj().T
        inverse_similarity = (
            eigenvectors * np.exp(-time * eigenvalues)
        ) @ eigenvectors.conj().T
        difference = similarity @ detector @ inverse_similarity - detector

        third = size // 3
        left_trace = np.trace(difference[:third, :third])
        middle_trace = np.trace(difference[third:-third, third:-third])
        right_trace = np.trace(difference[-third:, -third:])
        total_trace = np.trace(difference)
        positivity_floor = float(np.linalg.eigvalsh(detector).min())

        errors = (
            abs(total_trace),
            abs(left_trace - target),
            abs(right_trace + target),
            abs(middle_trace),
            max(0.0, 1.0 - positivity_floor),
        )
        maximum_error = max(maximum_error, *errors)
        rows.append(
            {
                "size": float(size),
                "left": float(left_trace.imag),
                "middle": float(middle_trace.imag),
                "right": float(right_trace.imag),
                "total": float(abs(total_trace)),
                "positive_floor": positivity_floor,
            }
        )
    return rows, maximum_error


def print_error_table(title: str, values: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------+---------------+")
    print("| check                                | error         |")
    print("+--------------------------------------+---------------+")
    for label, value in values.items():
        print(f"| {label:<36} | {value:>13.6e} |")
    print("+--------------------------------------+---------------+")


def print_anomaly_table(rows: list[dict[str, float]], time: float) -> None:
    print("similarity trace-anomaly boundary guard")
    print("+------+-----------+-----------+-----------+-----------+-----------+")
    print("| size | left Im   | middle Im | right Im  | total     | W floor   |")
    print("+------+-----------+-----------+-----------+-----------+-----------+")
    for row in rows:
        print(
            f"| {int(row['size']):>4} "
            f"| {row['left']:>9.5f} "
            f"| {row['middle']:>9.2e} "
            f"| {row['right']:>9.5f} "
            f"| {row['total']:>9.2e} "
            f"| {row['positive_floor']:>9.5f} |"
        )
    print("+------+-----------+-----------+-----------+-----------+-----------+")
    print(f"infinite left-boundary target: {-0.5 * time:.8f} i")


def parse_sizes(raw: str) -> list[int]:
    sizes = [int(item) for item in raw.split(",") if item.strip()]
    if not sizes:
        raise ValueError("expected at least one anomaly size")
    return sizes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=264)
    parser.add_argument("--anomaly-sizes", default="32,64,96,128")
    parser.add_argument("--anomaly-time", type=float, default=0.7)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    generic = generic_shorted_certificate(args.size, args.seed)
    causal = triangular_causal_certificate(args.size, args.seed)
    normal = normal_response_certificate(args.size, args.seed)
    anomaly, anomaly_error = similarity_anomaly_rows(
        parse_sizes(args.anomaly_sizes), args.anomaly_time
    )

    print_error_table("generic shorted-covariance algebra", generic)
    print()
    print_error_table("causal triangular factorization", causal)
    print()
    print_error_table("normal causal-Gram response", normal)
    print()
    print_anomaly_table(anomaly, args.anomaly_time)

    algebra_error = max(*generic.values(), *causal.values(), *normal.values())
    print(f"maximum algebra error: {algebra_error:.6e}")
    print(f"maximum anomaly guard error: {anomaly_error:.6e}")
    maximum_error = max(algebra_error, anomaly_error)
    if maximum_error > args.tolerance:
        raise SystemExit(
            f"certificate failed: {maximum_error:.6e} > {args.tolerance:.6e}"
        )


if __name__ == "__main__":
    main()
