#!/usr/bin/env python3
"""Finite certificate for the renewal/de Branges--Rovnyak coordinate.

The certificate checks exact finite-dimensional identities only.  It does not
prove the source Hardy/Hankel boundary estimate or Gate 3U.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def load_proof_290():
    path = Path(__file__).with_name(
        "290_biorthogonal_finite_horizon_renewal_probe.py"
    )
    specification = importlib.util.spec_from_file_location("proof_290_for_337", path)
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


PROOF_290 = load_proof_290()


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    return float(
        np.linalg.norm(actual - expected)
        / max(1.0, float(np.linalg.norm(expected)))
    )


def positive_function(operator: np.ndarray, function) -> np.ndarray:
    values, vectors = np.linalg.eigh(0.5 * (operator + operator.conj().T))
    return vectors @ np.diag(function(values)) @ vectors.conj().T


def path_projection(killed: np.ndarray, delta: np.ndarray, horizon: int) -> np.ndarray:
    identity = np.eye(delta.shape[0], dtype=complex)
    blocks = [
        killed @ np.linalg.matrix_power(delta, power)
        for power in range(horizon + 1)
    ]
    blocks.append(np.linalg.matrix_power(delta, horizon + 1))
    right = np.vstack(blocks)
    gram = right.conj().T @ right
    return right @ np.linalg.inv(gram) @ right.conj().T


def observability_projection(
    defect_output: np.ndarray, delta: np.ndarray, horizon: int
) -> tuple[np.ndarray, np.ndarray]:
    blocks = [
        defect_output @ np.linalg.matrix_power(delta, power)
        for power in range(horizon + 1)
    ]
    blocks.append(np.linalg.matrix_power(delta, horizon + 1))
    observability = np.vstack(blocks)
    return observability @ observability.conj().T, observability


def certificate(
    multiplicity: int, root_radius: int, seed: int, maximum_horizon: int
) -> tuple[dict[str, float], list[dict[str, float]]]:
    _, state = PROOF_290.build_path_model(
        multiplicity, root_radius, seed, max(1, maximum_horizon)
    )
    killed = state["killed"]
    gamma = state["gamma"]
    delta = state["delta"]
    identity = np.eye(delta.shape[0], dtype=complex)
    sqrt_one_plus_delta = positive_function(delta, lambda value: np.sqrt(1.0 + value))
    defect_output = killed @ sqrt_one_plus_delta
    renewal_transition = positive_function(delta, np.sqrt)

    contraction_defect = identity - delta @ delta
    base = {
        "defect identity error": relative_error(
            defect_output.conj().T @ defect_output, contraction_defect
        ),
        "gamma identity error": relative_error(gamma, identity - delta),
    }

    survivor_blocks = [
        killed @ np.linalg.matrix_power(renewal_transition, power)
        for power in range(maximum_horizon + 1)
    ]
    survivor_blocks.append(
        np.linalg.matrix_power(renewal_transition, maximum_horizon + 1)
    )
    survivor_observability = np.vstack(survivor_blocks)
    base["survivor observability isometry error"] = relative_error(
        survivor_observability.conj().T @ survivor_observability, identity
    )

    rows: list[dict[str, float]] = []
    for horizon in sorted(set([1, 2, 4, 8, 16, maximum_horizon])):
        if horizon > maximum_horizon:
            continue
        model_projection, observability = observability_projection(
            defect_output, delta, horizon
        )
        renewal_projection = path_projection(killed, delta, horizon)
        rows.append(
            {
                "horizon": float(horizon),
                "observability isometry error": relative_error(
                    observability.conj().T @ observability, identity
                ),
                "model projection idempotence": relative_error(
                    model_projection @ model_projection, model_projection
                ),
                "renewal/model projection gap": relative_error(
                    renewal_projection, model_projection
                ),
            }
        )

    maximum_kernel_violation = 0.0
    for radius in (0.0, 0.25, 0.5, 0.75, 0.9, 0.97):
        transfer = defect_output @ np.linalg.inv(identity - radius * delta)
        kernel_diagonal = (1.0 - radius * radius) * transfer @ transfer.conj().T
        maximum_kernel_violation = max(
            maximum_kernel_violation,
            float(max(0.0, np.linalg.eigvalsh(kernel_diagonal)[-1] - 1.0)),
        )
        survivor_transfer = killed @ np.linalg.inv(
            identity - radius * renewal_transition
        )
        survivor_kernel = (
            (1.0 - radius * radius)
            * survivor_transfer
            @ survivor_transfer.conj().T
        )
        maximum_kernel_violation = max(
            maximum_kernel_violation,
            float(max(0.0, np.linalg.eigvalsh(survivor_kernel)[-1] - 1.0)),
        )
    base["Hardy kernel bound violation"] = maximum_kernel_violation
    return base, rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--multiplicity", type=int, default=10)
    parser.add_argument("--root-radius", type=int, default=2)
    parser.add_argument("--seed", type=int, default=337)
    parser.add_argument("--maximum-horizon", type=int, default=32)
    parser.add_argument("--tolerance", type=float, default=3e-9)
    args = parser.parse_args()

    base, rows = certificate(
        args.multiplicity,
        args.root_radius,
        args.seed,
        args.maximum_horizon,
    )
    print("identity=renewal de-Branges-Rovnyak observability coordinate")
    print("status=exact contraction model; source boundary estimate open")
    for label, value in base.items():
        print(f"{label.replace(' ', '_')}={value:.12e}")
    print("horizon_table=BEGIN")
    for row in rows:
        print(
            f"horizon={int(row['horizon']):3d} "
            f"isometry={row['observability isometry error']:.3e} "
            f"projection={row['model projection idempotence']:.3e} "
            f"renewal_model_gap={row['renewal/model projection gap']:.3e}"
        )
    print("horizon_table=END")

    exact_error = max(
        base["defect identity error"],
        base["gamma identity error"],
        base["survivor observability isometry error"],
        base["Hardy kernel bound violation"],
        max(row["observability isometry error"] for row in rows),
        max(row["model projection idempotence"] for row in rows),
    )
    if exact_error > args.tolerance:
        raise RuntimeError(f"observability certificate failed: {exact_error:.3e}")
    print(f"maximum_exact_error={exact_error:.12e}")
    print("finite_horizon_zero_count_used=FALSE")
    print("uniform_source_Hardy_boundary_bound=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
