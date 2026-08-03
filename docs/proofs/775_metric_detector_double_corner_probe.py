"""Finite certificate for Proof 775's commuting double-boundary guard."""

from __future__ import annotations

import numpy as np


def block_diagonal(block: np.ndarray, multiplicity: int) -> np.ndarray:
    return np.kron(np.eye(multiplicity), block)


def source_inclusion(multiplicity: int) -> np.ndarray:
    inclusion = np.zeros((2 * multiplicity, multiplicity))
    for index in range(multiplicity):
        inclusion[2 * index, index] = 1.0
    return inclusion


def certify_block(h: float, multiplicity: int) -> tuple[float, float, float, float]:
    projection = np.array([[1.0, 0.0], [0.0, 0.0]])
    vector = np.array([1.0, 1.0]) / np.sqrt(2.0)
    weight = np.outer(vector, vector)
    metric = h * weight + (np.eye(2) - weight)

    r = block_diagonal(projection, multiplicity)
    w = block_diagonal(weight, multiplicity)
    h_metric = block_diagonal(metric, multiplicity)
    j = source_inclusion(multiplicity)
    complement = np.eye(2 * multiplicity) - r

    metric_boundary = r @ h_metric - h_metric @ r
    detector_boundary = w @ r - r @ w
    gram = j.T @ h_metric @ j
    target = np.linalg.inv(gram) @ j.T @ metric_boundary @ detector_boundary @ j
    first_corner = r @ h_metric @ complement @ w @ r
    second_corner = complement @ h_metric @ r @ w @ complement

    scalar = (h - 1.0) / (2.0 * (h + 1.0))
    expected_target = scalar * np.eye(multiplicity)
    algebra_error = max(
        np.linalg.norm(metric_boundary @ detector_boundary - first_corner - second_corner),
        np.linalg.norm(target - expected_target),
        np.linalg.norm(h_metric @ w - w @ h_metric),
    )
    inverse_gram_norm = np.linalg.norm(np.linalg.inv(gram), ord=2)
    detector_norm = np.linalg.norm(w, ord=2)
    trace = float(np.trace(target))
    return algebra_error, inverse_gram_norm, detector_norm, trace


def main() -> None:
    maximum_error = 0.0
    maximum_inverse_gram_norm = 0.0
    maximum_detector_norm = 0.0
    rows: list[tuple[float, int, float, float]] = []

    for h in (2.0, 5.0, 19.0, 1_000.0):
        scalar = (h - 1.0) / (2.0 * (h + 1.0))
        for multiplicity in (1, 2, 8, 32):
            error, inverse_gram_norm, detector_norm, trace = certify_block(h, multiplicity)
            maximum_error = max(maximum_error, error)
            maximum_inverse_gram_norm = max(maximum_inverse_gram_norm, inverse_gram_norm)
            maximum_detector_norm = max(maximum_detector_norm, detector_norm)
            rows.append((h, multiplicity, trace, scalar))

    assert maximum_error < 1e-11, maximum_error
    assert maximum_inverse_gram_norm <= 1.0 + 1e-12, maximum_inverse_gram_norm
    assert maximum_detector_norm <= 1.0 + 1e-12, maximum_detector_norm

    print(f"maximum algebra error          {maximum_error:.2e}")
    print(f"maximum inverse-Gram norm      {maximum_inverse_gram_norm:.6f}")
    print(f"maximum detector norm          {maximum_detector_norm:.6f}")
    print("h       copies  trace       trace/copy")
    for h, multiplicity, trace, scalar in rows:
        print(f"{h:7.1f} {multiplicity:7d} {trace:10.6f} {scalar:12.6f}")


if __name__ == "__main__":
    main()
