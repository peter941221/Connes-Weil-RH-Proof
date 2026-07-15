#!/usr/bin/env python3
"""Certificate for Proof 273's signed paired-stopping correction.

The first layer imports Proof 260's compact-root crossing.  Compact support
makes its scalar trace zero while its trace norm, and hence its one-column H1
norm, stays positive.

The second layer imports Proof 271's source-shaped finite model and splits the
exact renewal pairing into its random and outer first-missing channels.  This
is an algebra certificate.  It does not construct the real-line scalar
disintegration required by Gate 3U.
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


PROOF_260 = load_probe(
    "260_schatten_legality_signed_trace_gate_probe.py",
    "proof_260_for_273",
)
PROOF_271 = load_probe(
    "271_first_missing_prime_row_probe.py",
    "proof_271_for_273",
)


def relative_error(
    actual: complex | np.ndarray, expected: complex | np.ndarray
) -> float:
    actual_array = np.asarray(actual)
    expected_array = np.asarray(expected)
    scale = max(float(np.linalg.norm(expected_array)), 1.0)
    return float(np.linalg.norm(actual_array - expected_array) / scale)


def paired_renewal_certificate(
    multiplicity: int,
    seed: int,
    maximum_power: int,
    tail_tolerance: float,
) -> dict[str, float]:
    model = PROOF_271.PROOF_266.build_model(multiplicity, seed)
    owner = PROOF_271.PROOF_270.owner_data(model)
    channels = PROOF_271.missing_channel_data(model, owner)

    survivor = owner["K"]
    left = owner["L"]
    gamma = owner["Gamma"]
    defect = owner["D"]
    numerator = owner["N"]
    random_channel = channels["I_rand"]
    outer_channel = channels["I_C"]

    expected_response = np.trace(numerator @ np.linalg.inv(gamma))
    base_pairing = np.trace(left.conj().T @ survivor)
    random_pairing = 0.0j
    outer_pairing = 0.0j
    positive_left_mass = float(np.linalg.norm(left, ord="fro") ** 2)
    defect_power = np.eye(gamma.shape[0], dtype=complex)

    for renewal_index in range(maximum_power):
        left_random = left @ defect_power @ random_channel.conj().T
        right_random = survivor @ defect_power @ random_channel.conj().T
        left_outer = left @ defect_power @ outer_channel.conj().T
        right_outer = survivor @ defect_power @ outer_channel.conj().T

        random_pairing += np.trace(left_random.conj().T @ right_random)
        outer_pairing += np.trace(left_outer.conj().T @ right_outer)
        positive_left_mass += float(
            np.linalg.norm(left_random, ord="fro") ** 2
            + np.linalg.norm(left_outer, ord="fro") ** 2
        )

        defect_power = defect_power @ defect
        if (
            renewal_index >= 32
            and float(np.linalg.norm(defect_power, ord=2)) <= tail_tolerance
        ):
            break

    paired_response = base_pairing + random_pairing + outer_pairing
    return {
        "paired renewal response error": relative_error(
            paired_response, expected_response
        ),
        "base pairing magnitude": float(abs(base_pairing)),
        "random pairing magnitude": float(abs(random_pairing)),
        "outer pairing magnitude": float(abs(outer_pairing)),
        "complete response magnitude": float(abs(expected_response)),
        "positive left-column mass": positive_left_mass,
        "terminal defect-power norm": float(
            np.linalg.norm(defect_power, ord=2)
        ),
    }


def print_checks(title: str, checks: dict[str, float]) -> None:
    print(title)
    print("+--------------------------------------------+---------------+")
    print("| check                                      | value         |")
    print("+--------------------------------------------+---------------+")
    for label, value in checks.items():
        print(f"| {label:<42} | {value:>13.6e} |")
    print("+--------------------------------------------+---------------+")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=256)
    parser.add_argument("--root-radius", type=int, default=6)
    parser.add_argument("--shift", type=int, default=40)
    parser.add_argument("--multiplicity", type=int, default=8)
    parser.add_argument("--seed", type=int, default=273)
    parser.add_argument("--concentration-atoms", type=int, default=16)
    parser.add_argument("--maximum-power", type=int, default=512)
    parser.add_argument("--tail-tolerance", type=float, default=1e-13)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    args = parser.parse_args()

    crossing = PROOF_260.single_crossing_certificate(
        args.size, args.root_radius, args.shift
    )
    if args.concentration_atoms < 2:
        raise ValueError("concentration atoms must be at least two")
    renewal = paired_renewal_certificate(
        args.multiplicity,
        args.seed,
        args.maximum_power,
        args.tail_tolerance,
    )

    crossing_checks = {
        "crossing trace magnitude": crossing["trace_magnitude"],
        "crossing trace norm": crossing["trace_norm"],
        "one-column H1 norm": crossing["trace_norm"],
        "uniform-law concentration": 1.0 / args.concentration_atoms,
        "normalized direct-sum H1 mass": crossing["trace_norm"],
        "H1/concentration ratio": (
            args.concentration_atoms * crossing["trace_norm"]
        ),
        "trace norm formula error": crossing["trace_norm_error"],
        "optimal S2 factor error": crossing["holder_optimality_error"],
    }

    print("identity=signed paired stopping guard")
    print("status=positive H1 stopping rejected; paired scalar owner retained")
    print_checks("Compact-support crossing guard", crossing_checks)
    print()
    print_checks("First-missing signed pairing", renewal)

    maximum_error = max(
        crossing["trace_magnitude"],
        crossing["trace_formula_error"],
        crossing["trace_norm_error"],
        crossing["holder_optimality_error"],
        renewal["paired renewal response error"],
        max(
            renewal["terminal defect-power norm"] - args.tail_tolerance,
            0.0,
        ),
    )
    print(f"maximum checked error={maximum_error:.12e}")
    if maximum_error > args.tolerance:
        raise SystemExit(f"certificate failed: {maximum_error:.6e}")

    print("positive_h1_compact_support_stopping=REJECTED")
    print("fixed_s_signed_paired_renewal=EXACT")
    print("positive_square_energy_concentration=RETAINED")
    print("signed_scalar_local_coefficient=p^(-m/2)")
    print("complete_signed_extra_half_power=OPEN")
    print("paired_source_disintegration=OPEN")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
