"""Certificate for Proof 350's Julia graph prime-square gain.

The finite matrices verify exact Hilbert-space identities.  The cluster table
compares the universal post-Gram angle budget with Proof 348's prematurely
localized crossing Gram.  It does not prove the source detector Bessel bound or
Gate 3U.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(size=(size, size))
    q, r = np.linalg.qr(matrix)
    phases = np.diag(r)
    phases = phases / np.maximum(np.abs(phases), 1e-15)
    return q @ np.diag(np.conj(phases))


def projection_from_frame(frame: np.ndarray) -> np.ndarray:
    gram = frame.conj().T @ frame
    return frame @ np.linalg.inv(gram) @ frame.conj().T


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def one_factor_checks(
    size: int, rank: int, prime: int, rng: np.random.Generator
) -> dict[str, float]:
    complement_rank = size - rank
    unitary = random_unitary(size, rng)
    coefficient = prime ** -0.5

    u00 = unitary[:rank, :rank]
    u01 = unitary[:rank, rank:]
    u10 = unitary[rank:, :rank]
    u11 = unitary[rank:, rank:]

    complement_resolvent = np.linalg.inv(
        np.eye(complement_rank, dtype=complex) - coefficient * u11
    )
    graph = coefficient * complement_resolvent @ u10
    graph_frame = np.vstack([np.eye(rank, dtype=complex), graph])
    graph_projection = projection_from_frame(graph_frame)

    transport = np.linalg.inv(
        np.eye(size, dtype=complex) - coefficient * unitary
    )
    source_frame = np.vstack(
        [
            np.eye(rank, dtype=complex),
            np.zeros((complement_rank, rank), dtype=complex),
        ]
    )
    direct_frame = transport @ source_frame
    direct_projection = projection_from_frame(direct_frame)

    transfer = u00 + coefficient * u01 @ complement_resolvent @ u10
    transfer_defect = np.eye(rank, dtype=complex) - transfer.conj().T @ transfer
    resolvent_defect = (
        (1.0 - coefficient * coefficient)
        * u10.conj().T
        @ complement_resolvent.conj().T
        @ complement_resolvent
        @ u10
    )
    graph_square = graph.conj().T @ graph
    predicted_graph_square = (
        coefficient
        * coefficient
        / (1.0 - coefficient * coefficient)
        * transfer_defect
    )

    gram = np.eye(rank, dtype=complex) + graph_square
    eigenvalues, eigenvectors = np.linalg.eigh(gram)
    inverse_square_root = (
        eigenvectors
        @ np.diag(eigenvalues ** -0.5)
        @ eigenvectors.conj().T
    )
    cosine = inverse_square_root
    sine = graph @ inverse_square_root
    normalized_frame = np.vstack([cosine, sine])
    sine_square = sine.conj().T @ sine
    bound = coefficient * coefficient / (1.0 - coefficient * coefficient)
    maximum_sine_eigenvalue = float(np.max(np.linalg.eigvalsh(sine_square)))

    test_vector = rng.normal(size=rank) + 1j * rng.normal(size=rank)
    state = complement_resolvent @ u10 @ test_vector
    colligation_left = unitary @ np.concatenate(
        [test_vector, coefficient * state]
    )
    colligation_right = np.concatenate([transfer @ test_vector, state])

    return {
        "graph projection error": relative_error(
            graph_projection, direct_projection
        ),
        "normalized frame projection error": relative_error(
            normalized_frame @ normalized_frame.conj().T,
            direct_projection,
        ),
        "normalized isometry error": relative_error(
            normalized_frame.conj().T @ normalized_frame,
            np.eye(rank),
        ),
        "colligation relation error": relative_error(
            colligation_left, colligation_right
        ),
        "transfer defect error": relative_error(
            transfer_defect, resolvent_defect
        ),
        "graph square error": relative_error(
            graph_square, predicted_graph_square
        ),
        "sine square bound violation": max(0.0, maximum_sine_eigenvalue - bound),
    }


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for candidate in range(2, math.isqrt(limit) + 1):
        if not sieve[candidate]:
            continue
        start = candidate * candidate
        count = (limit - start) // candidate + 1
        sieve[start : limit + 1 : candidate] = b"\x00" * count
    return [value for value in range(2, limit + 1) if sieve[value]]


def cluster_statistics(
    lower: int,
    epsilon: float,
    root_half_width: float,
    all_primes: list[int],
    block_size: int = 512,
) -> tuple[int, float, float]:
    upper = (1.0 + epsilon) * lower
    cluster = np.asarray(
        [prime for prime in all_primes if lower <= prime <= upper], dtype=float
    )
    if cluster.size == 0:
        return 0, 0.0, 0.0

    logs = np.log(cluster)
    weights = cluster ** -0.5
    julia_budget = float(np.sum(logs / (cluster - 1.0)))

    gram = 0.0
    for start in range(0, cluster.size, block_size):
        stop = min(start + block_size, cluster.size)
        row_logs = logs[start:stop, None]
        differences = logs[None, :] - row_logs
        correlations = np.maximum(
            0.0, 1.0 - np.abs(differences) / (2.0 * root_half_width)
        )
        gram += float(
            np.sum(
                weights[start:stop, None]
                * weights[None, :]
                * np.minimum(row_logs, logs[None, :])
                * correlations
            )
        )
    return int(cluster.size), julia_budget, gram


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=26)
    parser.add_argument("--rank", type=int, default=11)
    parser.add_argument("--seed", type=int, default=350)
    parser.add_argument("--tolerance", type=float, default=2e-10)
    parser.add_argument("--scales", default="100,1000,10000,100000,1000000")
    parser.add_argument("--epsilon", type=float, default=0.1)
    parser.add_argument("--root-half-width", type=float, default=0.5)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if not 0 < args.rank < args.size:
        raise ValueError("rank must lie strictly between zero and size")
    rng = np.random.default_rng(args.seed)

    aggregate: dict[str, float] = {}
    for prime in [2, 3, 5, 11, 101]:
        checks = one_factor_checks(args.size, args.rank, prime, rng)
        for label, value in checks.items():
            aggregate[label] = max(aggregate.get(label, 0.0), value)

    print("Proof 350 Julia graph prime-square gain certificate")
    for label, value in aggregate.items():
        print(f"maximum_{label.replace(' ', '_')}={value:.12e}")
    maximum_error = max(aggregate.values())
    if maximum_error > args.tolerance:
        raise RuntimeError(f"Julia graph identity check failed: {maximum_error:.3e}")

    scales = [int(value) for value in args.scales.split(",")]
    prime_limit = math.ceil((1.0 + args.epsilon) * max(scales))
    all_primes = primes_up_to(prime_limit)

    print()
    print(
        "X          primes   Julia_budget    raw_Gram_S2^2  "
        "Gram/budget"
    )
    for lower in scales:
        count, budget, gram = cluster_statistics(
            lower,
            args.epsilon,
            args.root_half_width,
            all_primes,
        )
        ratio = gram / budget if budget else float("nan")
        print(
            f"{lower:9d}  "
            f"{count:7d}  "
            f"{budget: .8e}  "
            f"{gram: .8e}  "
            f"{ratio: .8e}"
        )

    print()
    print(f"maximum_exact_error={maximum_error:.12e}")
    print("one_factor_graph_owner=EXACT")
    print("post_gram_prime_square_gain=EXACT")
    print("complete_detector_innovation_bessel_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
