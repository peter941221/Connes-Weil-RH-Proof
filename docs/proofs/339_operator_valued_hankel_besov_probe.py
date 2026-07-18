#!/usr/bin/env python3
"""Finite guard for the operator-valued Hankel/Besov Gate 3U interface.

The probe checks the exact Hankel emission corner from Proof 294 and compares
its finite trace norm with an S1-valued dyadic B^1_1 symbol norm.  It is not a
proof of the continuous source estimate or Gate 3U.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_proof_270():
    path = Path(__file__).with_name(
        "270_renewal_observability_collapse_probe.py"
    )
    specification = importlib.util.spec_from_file_location("proof_270_for_339", path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_270 = load_proof_270()


def positive_function(operator: np.ndarray, function) -> np.ndarray:
    values, vectors = np.linalg.eigh(0.5 * (operator + operator.conj().T))
    return vectors @ np.diag(function(values)) @ vectors.conj().T


def trace_norm(operator: np.ndarray) -> float:
    return float(np.linalg.svd(operator, compute_uv=False).sum())


def dyadic_weight(level: int, index: int) -> float:
    if level == 0:
        return 1.0 if index <= 1 else 0.0
    lower = 2 ** (level - 1)
    middle = 2**level
    upper = 2 ** (level + 1)
    if lower <= index <= middle:
        return (index - lower) / max(1, middle - lower)
    if middle < index <= upper:
        return (upper - index) / max(1, upper - middle)
    return 0.0


def hankel_coefficients(
    data: dict[str, np.ndarray], detector: np.ndarray, maximum_index: int
) -> list[np.ndarray]:
    killed = data["K"]
    delta = data["Delta"]
    defect_output = killed @ positive_function(
        delta, lambda value: np.sqrt(1.0 + value)
    )
    coefficients: list[np.ndarray] = []
    power = np.eye(delta.shape[0], dtype=complex)
    for _ in range(maximum_index + 1):
        block = defect_output @ power @ defect_output.conj().T
        coefficients.append(detector @ block - block @ detector)
        power = power @ delta
    return coefficients


def block_hankel(coefficients: list[np.ndarray], horizon: int) -> np.ndarray:
    block_size = coefficients[0].shape[0]
    result = np.zeros(
        (horizon * block_size, horizon * block_size), dtype=complex
    )
    for row in range(horizon):
        for column in range(horizon):
            block = coefficients[row + column]
            result[
                row * block_size : (row + 1) * block_size,
                column * block_size : (column + 1) * block_size,
            ] = block
    return result


def besov_surrogate(
    coefficients: list[np.ndarray], angle_count: int
) -> tuple[float, list[tuple[int, float]]]:
    maximum_index = len(coefficients) - 1
    maximum_level = int(np.floor(np.log2(maximum_index)))
    angles = 2.0 * np.pi * np.arange(angle_count) / angle_count
    rows: list[tuple[int, float]] = []
    total = 0.0
    for level in range(maximum_level + 1):
        indices = [
            index
            for index in range(maximum_index + 1)
            if dyadic_weight(level, index) != 0.0
        ]
        if not indices:
            continue
        average = 0.0
        for angle in angles:
            value = np.zeros_like(coefficients[0])
            for index in indices:
                value += (
                    dyadic_weight(level, index)
                    * np.exp(1j * index * angle)
                    * coefficients[index]
                )
            average += trace_norm(value)
        average /= angle_count
        contribution = (2**level) * average
        total += contribution
        rows.append((level, contribution))
    return total, rows


def certificate(
    multiplicity: int,
    seed: int,
    diagonals: tuple[float, ...],
    maximum_index: int,
    horizon: int,
    angle_count: int,
) -> list[dict[str, float]]:
    model = PROOF_270.PROOF_266.build_model(multiplicity, seed)
    detector = model["W"]
    rows: list[dict[str, float]] = []
    for diagonal in diagonals:
        inverse = PROOF_270.causal_inverse(multiplicity, diagonal)
        data = PROOF_270.owner_data(model, inverse)
        coefficients = hankel_coefficients(data, detector, maximum_index)
        hankel = block_hankel(coefficients, horizon)
        besov, _ = besov_surrogate(coefficients, angle_count)
        delta_norm = float(np.linalg.norm(data["Delta"], ord=2))
        rows.append(
            {
                "diagonal": diagonal,
                "delta_norm": delta_norm,
                "hankel_trace_norm": trace_norm(hankel),
                "besov_surrogate": besov,
                "ratio": trace_norm(hankel) / max(besov, 1e-15),
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=6)
    parser.add_argument("--seed", type=int, default=339)
    parser.add_argument("--maximum-index", type=int, default=127)
    parser.add_argument("--horizon", type=int, default=24)
    parser.add_argument("--angle-count", type=int, default=128)
    args = parser.parse_args()
    rows = certificate(
        args.multiplicity,
        args.seed,
        (0.55, 0.35, 0.20, 0.10, 0.05),
        args.maximum_index,
        args.horizon,
        args.angle_count,
    )
    print("identity=operator-valued Hankel emission corner")
    print("hankel_besov_table=BEGIN")
    for row in rows:
        print(
            f"diagonal={row['diagonal']:.2f} "
            f"delta_norm={row['delta_norm']:.9f} "
            f"hankel_S1={row['hankel_trace_norm']:.6e} "
            f"Besov_B11={row['besov_surrogate']:.6e} "
            f"ratio={row['ratio']:.6e}"
        )
    print("hankel_besov_table=END")
    print("source_S1_valued_Besov_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
