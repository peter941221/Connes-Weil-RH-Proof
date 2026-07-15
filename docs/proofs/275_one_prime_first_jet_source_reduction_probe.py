#!/usr/bin/env python3
"""Certificate for Proof 275's one-prime first-jet reduction.

The exact layer checks the derivative of the orthogonal projection onto
``(I-aU) Ran(J)`` and its nested ``E-R`` difference.  The source-shaped layer
reuses Proof 251's finite Sonin section to verify compact-window deletion of
the outer half-line tangent and to report, without promoting it to a theorem,
the decay of the complete nested tangent.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path

import numpy as np


def load_probe(filename: str, module_name: str):
    path = Path(__file__).with_name(filename)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def orthogonal_projection(columns: np.ndarray) -> np.ndarray:
    basis, _ = np.linalg.qr(columns, mode="reduced")
    return basis @ basis.conj().T


def transported_projection(
    basis: np.ndarray, translation: np.ndarray, parameter: float
) -> np.ndarray:
    identity = np.eye(translation.shape[0], dtype=complex)
    return orthogonal_projection((identity - parameter * translation) @ basis)


def projection_first_jet(
    projection: np.ndarray, translation: np.ndarray
) -> np.ndarray:
    identity = np.eye(projection.shape[0], dtype=complex)
    complement = identity - projection
    crossing = complement @ translation @ projection
    return -(crossing + crossing.conj().T)


def random_unitary(size: int, rng: np.random.Generator) -> np.ndarray:
    matrix = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    unitary, diagonal = np.linalg.qr(matrix)
    phases = np.diag(diagonal)
    phases = np.where(np.abs(phases) > 0.0, phases / np.abs(phases), 1.0)
    return unitary @ np.diag(np.conj(phases))


def abstract_first_jet_certificate(
    size: int, seed: int, derivative_step: float
) -> dict[str, float]:
    rng = np.random.default_rng(seed)
    ambient_basis = random_unitary(size, rng)
    translation = random_unitary(size, rng)
    outer_basis = ambient_basis[:, : size // 2]
    inner_basis = ambient_basis[:, : size // 4]
    outer = outer_basis @ outer_basis.conj().T
    inner = inner_basis @ inner_basis.conj().T

    analytic_outer = projection_first_jet(outer, translation)
    analytic_inner = projection_first_jet(inner, translation)
    analytic_band = analytic_outer - analytic_inner

    plus_band = transported_projection(
        outer_basis, translation, derivative_step
    ) - transported_projection(inner_basis, translation, derivative_step)
    minus_band = transported_projection(
        outer_basis, translation, -derivative_step
    ) - transported_projection(inner_basis, translation, -derivative_step)
    finite_difference = (plus_band - minus_band) / (2.0 * derivative_step)

    nested_error = float(
        np.linalg.norm(finite_difference - analytic_band, ord=2)
    )
    self_adjoint_error = float(
        np.linalg.norm(analytic_band - analytic_band.conj().T, ord=2)
    )
    nesting_error = float(np.linalg.norm(inner @ outer - inner, ord=2))
    return {
        "nested first-jet finite-difference error": nested_error,
        "nested first-jet self-adjoint error": self_adjoint_error,
        "source projection nesting error": nesting_error,
    }


def source_first_jet_rows(
    size: int,
    step: float,
    root_width: float,
    lengths: tuple[float, ...],
    intersection_tolerance: float,
) -> tuple[list[dict[str, float]], dict[str, float]]:
    proof_251 = load_probe(
        "251_complete_nested_central_scaling_probe.py",
        "proof_251_first_jet",
    )
    coordinates = (np.arange(size) - size // 2) * step
    basis, angle_eigenvalues = proof_251.sonin_basis(
        size, step, intersection_tolerance
    )
    if basis.shape[1] == 0:
        raise RuntimeError("finite section found no near-Sonin directions")

    root_size = int(round(root_width / step))
    differential = proof_251.root_differential(root_size, step)
    rows: list[dict[str, float]] = []
    maximum_outer_norm = 0.0
    maximum_coefficient_error = 0.0

    for requested_length in lengths:
        row = proof_251.scaling_row(
            basis,
            coordinates,
            step,
            root_size,
            requested_length,
        )
        length = row["realized_length"]
        displacement = int(row["displacement"])
        outer_derivative = proof_251.halfline_first_variation(
            coordinates, displacement
        )
        outer_toeplitz = proof_251.trace_diagonal_toeplitz(
            outer_derivative, root_size
        )
        outer_root = step**2 * (
            differential.conj().T @ outer_toeplitz @ differential
        )
        outer_norm = proof_251.operator_norm(outer_root)

        euler_coefficient = math.exp(-length / 2.0)
        dressed_from_ledger = euler_coefficient * row["derivative_norm"]
        coefficient_error = abs(
            dressed_from_ledger - row["integrated_norm"]
        )
        maximum_outer_norm = max(maximum_outer_norm, outer_norm)
        maximum_coefficient_error = max(
            maximum_coefficient_error, coefficient_error
        )
        rows.append(
            {
                "length": length,
                "outer_root_norm": outer_norm,
                "nested_tangent_norm": row["derivative_norm"],
                "euler_coefficient": euler_coefficient,
                "dressed_response": row["integrated_norm"],
                "full_power_ratio": (
                    row["integrated_norm"] * math.exp(length)
                ),
            }
        )

    length_values = np.array([row["length"] for row in rows])
    tangent_values = np.array(
        [row["nested_tangent_norm"] for row in rows]
    )
    dressed_values = np.array([row["dressed_response"] for row in rows])
    tangent_slope = float(
        np.polyfit(length_values, np.log(tangent_values), 1)[0]
    )
    dressed_slope = float(
        np.polyfit(length_values, np.log(dressed_values), 1)[0]
    )
    checks = {
        "maximum outer compact-window root norm": maximum_outer_norm,
        "Euler coefficient ledger error": maximum_coefficient_error,
        "finite tangent log slope": tangent_slope,
        "finite dressed log slope": dressed_slope,
        "near-Sonin rank": float(basis.shape[1]),
        "top angle eigenvalue": float(angle_eigenvalues[-1]),
    }
    return rows, checks


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+----------------------------------------------+----------------+")
    print("| check                                        | value          |")
    print("+----------------------------------------------+----------------+")
    for label, value in checks.items():
        print(f"| {label:<44} | {value:>14.6e} |")
    print("+----------------------------------------------+----------------+")


def print_rows(rows: list[dict[str, float]]) -> None:
    print("Source-shaped one-prime first-jet diagnostic")
    print(
        "+--------+-------------+-------------+-------------+-------------+"
    )
    print(
        "| z      | outer root  | tangent     | dressed     | e^z dressed |"
    )
    print(
        "+--------+-------------+-------------+-------------+-------------+"
    )
    for row in rows:
        print(
            f"| {row['length']:>6.2f} "
            f"| {row['outer_root_norm']:>11.3e} "
            f"| {row['nested_tangent_norm']:>11.3e} "
            f"| {row['dressed_response']:>11.3e} "
            f"| {row['full_power_ratio']:>11.3e} |"
        )
    print(
        "+--------+-------------+-------------+-------------+-------------+"
    )


def parse_lengths(value: str) -> tuple[float, ...]:
    return tuple(float(item) for item in value.split(",") if item.strip())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--abstract-size", type=int, default=20)
    parser.add_argument("--seed", type=int, default=1275)
    parser.add_argument("--derivative-step", type=float, default=2e-5)
    parser.add_argument("--size", type=int, default=512)
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--root-width", type=float, default=1.0)
    parser.add_argument("--lengths", default="3,3.5,4,4.5,5")
    parser.add_argument("--intersection-tolerance", type=float, default=1e-8)
    parser.add_argument("--tolerance", type=float, default=2e-7)
    parser.add_argument("--outer-tolerance", type=float, default=1e-12)
    args = parser.parse_args()

    lengths = parse_lengths(args.lengths)
    if len(lengths) < 4:
        raise ValueError("lengths must contain at least four entries")
    if min(lengths) <= 2.0 * args.root_width:
        raise ValueError("every diagnostic shift must clear compact support")
    half_domain = args.size * args.step / 2.0
    if max(lengths) + args.root_width >= half_domain / 2.0:
        raise ValueError("finite diagnostic domain is too small")

    abstract = abstract_first_jet_certificate(
        args.abstract_size, args.seed, args.derivative_step
    )
    rows, source = source_first_jet_rows(
        args.size,
        args.step,
        args.root_width,
        lengths,
        args.intersection_tolerance,
    )

    print("identity=one-prime nested first-jet extra-half-power reduction")
    print("status=exact reduction; continuous Sonin/prolate decay open")
    print_checks("Abstract projection first-jet checks", abstract)
    print()
    print_rows(rows)
    print()
    print_checks("Source-shaped diagnostic checks", source)

    maximum_exact_error = max(
        abstract["nested first-jet finite-difference error"],
        abstract["nested first-jet self-adjoint error"],
        abstract["source projection nesting error"],
        source["Euler coefficient ledger error"],
    )
    print(f"maximum exact-certificate error={maximum_exact_error:.12e}")
    if maximum_exact_error > args.tolerance:
        raise SystemExit(
            f"first-jet certificate failed: {maximum_exact_error:.6e}"
        )
    if source["maximum outer compact-window root norm"] > args.outer_tolerance:
        raise SystemExit("outer half-line compact-window clip failed")

    print("orthogonal_projection_first_jet=EXACT")
    print("nested_band_first_jet=EXACT")
    print("outer_compact_support_scalar_clip=SOURCE_EXACT_AND_PROBE_PASS")
    print("extra_half_power_reduction=EXACT")
    if source["finite dressed log slope"] < -0.75:
        print("finite_section_decay_diagnostic=EXTRA_HALF_POWER_SURVIVES")
    else:
        print("finite_section_decay_diagnostic=RAW_HALF_POWER_SURVIVES")
    print("continuous_sonin_prolate_off_diagonal_decay=OPEN")
    print("mixed_prime_determinant_resummation=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
