#!/usr/bin/env python3
"""Certificate for covariant transport of the prolate leakage.

The endpoint identity

    Q U = (Q-R_T) [T Q B + [Q,T] B] Sigma^(-1/2)

must not be estimated term by term.  A two-dimensional Q-preserving model can
make the displayed branches +kappa and -kappa while their sum is zero.

For a differentiable orthogonal band projection P_t, Kato's generator

    A_t = [P_t', P_t]

is skew-adjoint and satisfies P_t' = [A_t,P_t].  Its unitary flow transports
P_0 to P_t.  Therefore the leakage is carried without the unstable endpoint
split by

    C_t = Q U_t P_0,
    C_t' = Q A_t U_t P_0,
    C_t C_t* = Q P_t Q.

The script verifies the exact algebra, the branch-cancellation model, and an
independent Runge--Kutta integration of a nonzero Q-preserving nested flow.
It does not prove a uniform trace bound or RH.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
from pathlib import Path
from types import ModuleType

import numpy as np


def load_proof_257() -> ModuleType:
    path = Path(__file__).with_name(
        "257_two_boundary_graph_flow_probe.py"
    )
    spec = importlib.util.spec_from_file_location("proof_257", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROOF_257 = load_proof_257()
PROOF_252 = PROOF_257.PROOF_252


def projection(columns: np.ndarray) -> np.ndarray:
    return columns @ columns.conj().T


def relative_error(actual: np.ndarray, expected: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(expected, ord="fro")), 1e-15)
    return float(np.linalg.norm(actual - expected, ord="fro") / denominator)


def relative_norm(matrix: np.ndarray, scale: np.ndarray) -> float:
    denominator = max(float(np.linalg.norm(scale, ord="fro")), 1e-15)
    return float(np.linalg.norm(matrix, ord="fro") / denominator)


def selector_basis(size: int, start: int, stop: int) -> np.ndarray:
    basis = np.zeros((size, stop - start), dtype=complex)
    basis[np.arange(start, stop), np.arange(stop - start)] = 1.0
    return basis


def branch_cancellation_row(kappa: float) -> dict[str, float]:
    if kappa <= 0.0:
        raise ValueError("kappa must be positive")
    q_projection = np.diag([1.0, 0.0]).astype(complex)
    identity = np.eye(2, dtype=complex)
    normalization = math.sqrt(1.0 + kappa * kappa)
    band = np.array([[kappa], [1.0]], dtype=complex) / normalization
    transport = np.array(
        [[1.0, -kappa], [0.0, 1.0]], dtype=complex
    )
    minimum_singular = float(
        np.linalg.svd(transport, compute_uv=False).min()
    )
    normalized_transport = transport / minimum_singular
    transported = normalized_transport @ band
    sigma = float(np.vdot(transported, transported).real)
    isometry = transported / math.sqrt(sigma)

    base_branch = (
        normalized_transport @ q_projection @ band / math.sqrt(sigma)
    )
    commutator = (
        q_projection @ normalized_transport
        - normalized_transport @ q_projection
    )
    boundary_branch = commutator @ band / math.sqrt(sigma)
    complete = q_projection @ isometry
    metric = normalized_transport.conj().T @ normalized_transport
    return {
        "kappa": kappa,
        "minimum_metric_eigenvalue": float(
            np.linalg.eigvalsh((metric + metric.conj().T) / 2.0).min()
        ),
        "q_invariance_error": float(
            np.linalg.norm(
                (identity - q_projection)
                @ normalized_transport
                @ q_projection,
                ord="fro",
            )
        ),
        "base_branch_norm": float(np.linalg.norm(base_branch)),
        "boundary_branch_norm": float(np.linalg.norm(boundary_branch)),
        "complete_norm": float(np.linalg.norm(complete)),
        "branch_sum_error": float(
            np.linalg.norm(base_branch + boundary_branch - complete)
            / max(
                float(np.linalg.norm(base_branch)),
                float(np.linalg.norm(boundary_branch)),
                1.0,
            )
        ),
        "isometry_error": relative_error(
            isometry.conj().T @ isometry, np.eye(1, dtype=complex)
        ),
    }


def make_q_preserving_geometry(
    size: int, seed: int
) -> dict[str, np.ndarray]:
    if size < 12 or size % 4:
        raise ValueError("size must be a multiple of four")
    rng = np.random.default_rng(seed)
    block = size // 4
    r_basis = selector_basis(size, 0, block)
    b_basis = selector_basis(size, block, 2 * block)
    c_basis = selector_basis(size, 2 * block, 3 * block)
    extra_basis = selector_basis(size, 3 * block, size)
    e_basis = np.concatenate([r_basis, b_basis], axis=1)
    angles = np.linspace(0.23, 1.13, block)
    q_generic = (
        b_basis @ np.diag(np.cos(angles))
        + c_basis @ np.diag(np.sin(angles))
    )
    q_basis = np.concatenate([r_basis, q_generic, extra_basis], axis=1)
    q_projection = projection(q_basis)
    identity = np.eye(size, dtype=complex)

    random = rng.normal(size=(size, size)) + 1j * rng.normal(
        size=(size, size)
    )
    random /= max(float(np.linalg.norm(random, ord=2)), 1e-15)
    generator = 0.17 * (
        random
        - (identity - q_projection) @ random @ q_projection
    )
    return {
        "identity": identity,
        "r_basis": r_basis,
        "b_basis": b_basis,
        "e_basis": e_basis,
        "q_projection": q_projection,
        "generator": generator,
    }


def orthonormalize(columns: np.ndarray) -> np.ndarray:
    basis, _ = np.linalg.qr(columns, mode="reduced")
    return basis


def nested_path_data(
    geometry: dict[str, np.ndarray], parameter: float
) -> dict[str, np.ndarray]:
    identity = geometry["identity"]
    generator = geometry["generator"]
    transport = identity + parameter * generator
    right_generator = generator @ np.linalg.inv(transport)
    e_columns = orthonormalize(transport @ geometry["e_basis"])
    r_columns = orthonormalize(transport @ geometry["r_basis"])
    e_projection = projection(e_columns)
    r_projection = projection(r_columns)
    band_projection = e_projection - r_projection
    derivative = PROOF_252.projection_derivative(
        e_projection, e_columns, right_generator
    ) - PROOF_252.projection_derivative(
        r_projection, r_columns, right_generator
    )
    kato_generator = derivative @ band_projection - band_projection @ derivative
    return {
        "transport": transport,
        "right_generator": right_generator,
        "e_projection": e_projection,
        "r_projection": r_projection,
        "band_projection": band_projection,
        "derivative": derivative,
        "kato_generator": kato_generator,
    }


def rk4_step(
    geometry: dict[str, np.ndarray],
    parameter: float,
    step: float,
    unitary: np.ndarray,
) -> np.ndarray:
    def vector_field(value: float, matrix: np.ndarray) -> np.ndarray:
        kato = nested_path_data(geometry, value)["kato_generator"]
        return kato @ matrix

    first = vector_field(parameter, unitary)
    second = vector_field(
        parameter + step / 2.0, unitary + step * first / 2.0
    )
    third = vector_field(
        parameter + step / 2.0, unitary + step * second / 2.0
    )
    fourth = vector_field(parameter + step, unitary + step * third)
    return unitary + step * (
        first + 2.0 * second + 2.0 * third + fourth
    ) / 6.0


def kato_flow_certificate(
    size: int, seed: int, steps: int, finite_difference: float
) -> dict[str, float]:
    geometry = make_q_preserving_geometry(size, seed)
    identity = geometry["identity"]
    q_projection = geometry["q_projection"]
    base = nested_path_data(geometry, 0.0)
    endpoint = nested_path_data(geometry, 1.0)
    base_band = base["band_projection"]
    endpoint_band = endpoint["band_projection"]

    sample = nested_path_data(geometry, 0.61)
    derivative = sample["derivative"]
    band = sample["band_projection"]
    kato = sample["kato_generator"]
    plus = nested_path_data(geometry, 0.61 + finite_difference)[
        "band_projection"
    ]
    minus = nested_path_data(geometry, 0.61 - finite_difference)[
        "band_projection"
    ]
    finite_difference_derivative = (plus - minus) / (
        2.0 * finite_difference
    )

    unitary = identity.copy()
    step = 1.0 / steps
    for index in range(steps):
        unitary = rk4_step(geometry, index * step, step, unitary)

    leakage = q_projection @ unitary @ base_band
    leakage_square = leakage @ leakage.conj().T
    fixed_compression = (
        base_band @ unitary.conj().T @ q_projection @ unitary @ base_band
    )
    return {
        "projection_tangent_error": relative_norm(
            band @ derivative @ band, derivative
        ),
        "kato_skew_error": relative_error(
            kato.conj().T, -kato
        ),
        "kato_commutator_error": relative_error(
            kato @ band - band @ kato, derivative
        ),
        "projection_finite_difference_error": relative_error(
            finite_difference_derivative, derivative
        ),
        "unitarity_error": relative_error(
            unitary.conj().T @ unitary, identity
        ),
        "transported_projection_error": relative_error(
            unitary @ base_band @ unitary.conj().T, endpoint_band
        ),
        "leakage_square_error": relative_error(
            leakage_square,
            q_projection @ endpoint_band @ q_projection,
        ),
        "fixed_compression_error": relative_error(
            fixed_compression, leakage.conj().T @ leakage
        ),
        "base_leakage_trace_norm": float(
            np.linalg.svd(q_projection @ base_band, compute_uv=False).sum()
        ),
        "endpoint_leakage_trace_norm": float(
            np.linalg.svd(q_projection @ endpoint_band, compute_uv=False).sum()
        ),
    }


def parse_kappas(raw: str) -> list[float]:
    values = [float(item) for item in raw.split(",") if item.strip()]
    if not values or min(values) <= 0.0:
        raise ValueError("kappas must be positive")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kappas", default="2,10,100,10000")
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=258)
    parser.add_argument("--steps", type=int, default=256)
    parser.add_argument("--finite-difference", type=float, default=1e-6)
    parser.add_argument("--max-algebra-error", type=float, default=2e-8)
    args = parser.parse_args()
    if args.steps < 32:
        raise ValueError("steps must be at least 32")

    rows = [branch_cancellation_row(value) for value in parse_kappas(args.kappas)]
    flow = kato_flow_certificate(
        args.size, args.seed, args.steps, args.finite_difference
    )
    maximum_branch_error = max(
        max(row["branch_sum_error"], row["isometry_error"])
        for row in rows
    )
    maximum_flow_error = max(
        value for key, value in flow.items() if key.endswith("_error")
    )

    print("identity=covariant transported-prolate flow")
    print("status=exact cancellation guard plus Kato-flow certificate")
    print(f"maximum_branch_error={maximum_branch_error:.12e}")
    print(f"maximum_kato_flow_error={maximum_flow_error:.12e}")
    print("branch_cancellation_table=BEGIN")
    for row in rows:
        print(
            f"kappa={row['kappa']:.12e} "
            f"minimum_metric={row['minimum_metric_eigenvalue']:.12e} "
            f"q_invariance={row['q_invariance_error']:.3e} "
            f"base={row['base_branch_norm']:.12e} "
            f"boundary={row['boundary_branch_norm']:.12e} "
            f"complete={row['complete_norm']:.12e} "
            f"sum_error={row['branch_sum_error']:.3e}"
        )
    print("branch_cancellation_table=END")
    print("kato_flow_table=BEGIN")
    for key, value in flow.items():
        print(f"{key}={value:.12e}")
    print("kato_flow_table=END")

    if maximum_branch_error > args.max_algebra_error:
        raise RuntimeError("transported-prolate cancellation guard failed")
    if maximum_flow_error > args.max_algebra_error:
        raise RuntimeError("Kato-flow certificate failed")

    print("certificate=PASS")
    print("separate_endpoint_branch_estimates=REJECTED")
    print("covariant_leakage_transport=EXACT")
    print("uniform_compact_root_bound=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
