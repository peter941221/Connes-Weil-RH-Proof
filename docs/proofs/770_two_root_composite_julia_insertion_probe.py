#!/usr/bin/env python3
"""Finite checks for Proof 770's two-root composite placement."""

from __future__ import annotations

import numpy as np


def random_complex(rng: np.random.Generator, rows: int, cols: int) -> np.ndarray:
    return rng.standard_normal((rows, cols)) + 1j * rng.standard_normal((rows, cols))


def hs_inner(left: np.ndarray, right: np.ndarray) -> complex:
    return np.trace(left.conj().T @ right)


def check_two_root_composite_placement() -> dict[str, float]:
    rng = np.random.default_rng(770)
    p_dim = 3
    q_dim = 4

    c00 = random_complex(rng, p_dim, p_dim)
    c01 = random_complex(rng, p_dim, q_dim)
    c10 = random_complex(rng, q_dim, p_dim)
    c11 = random_complex(rng, q_dim, q_dim)
    c = np.block([[c00, c01], [c10, c11]])

    r = random_complex(rng, q_dim, p_dim)
    zero_pp = np.zeros((p_dim, p_dim), dtype=np.complex128)
    zero_qq = np.zeros((q_dim, q_dim), dtype=np.complex128)
    delta = np.block([[zero_pp, r.conj().T], [r, zero_qq]])
    w = c.conj().T @ c

    lhs = np.trace(w @ delta)
    old_pairing = 2.0 * np.real(
        hs_inner(c10, c11 @ r)
        + hs_inner(c01.conj().T, r @ c00.conj().T)
    )
    l_plus = c10.conj().T @ c11
    l_minus = c00.conj().T @ c01
    recombined = l_plus + l_minus
    detector_corner = w[:p_dim, p_dim:]
    u, singular_values, vh = np.linalg.svd(recombined, full_matrices=False)
    active = singular_values > 1e-12
    root = np.sqrt(singular_values[active])
    polar_left = u[:, active] * root
    b_root = vh[active, :].conj().T * root
    prefix = np.diag(np.array([0.91, 0.67, 0.43], dtype=np.complex128))
    a_root = np.linalg.solve(prefix, polar_left)
    composite_pairing = 2.0 * np.real(hs_inner(b_root, r @ prefix @ a_root))

    return {
        "old_pairing_error": abs(lhs - old_pairing),
        "composite_pairing_error": abs(lhs - composite_pairing),
        "recombined_corner_error": np.linalg.norm(recombined - detector_corner),
        "prefix_factor_error": np.linalg.norm(
            recombined - prefix @ a_root @ b_root.conj().T
        ),
        "trace_imaginary_part": abs(np.imag(lhs)),
    }


def check_extension_ambiguity() -> dict[str, float]:
    projection = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    identity = np.eye(2, dtype=np.complex128)
    root = np.array([[0.0, 0.0], [1.0, 0.0]], dtype=np.complex128)
    off_model = (identity - projection) @ root @ projection

    extension_zero = projection
    extension_identity = identity
    source_vector = np.array([1.0, 0.0], dtype=np.complex128)

    agreement_error = max(
        np.linalg.norm(extension_zero @ source_vector - source_vector),
        np.linalg.norm(extension_identity @ source_vector - source_vector),
    )
    zero_extension_norm = np.linalg.norm(extension_zero @ off_model)
    identity_extension_difference = np.linalg.norm(
        extension_identity @ off_model - off_model
    )
    ambiguity_norm = np.linalg.norm(
        extension_identity @ off_model - extension_zero @ off_model
    )

    return {
        "agreement_error": agreement_error,
        "zero_extension_norm": zero_extension_norm,
        "identity_extension_difference": identity_extension_difference,
        "off_model_ambiguity": ambiguity_norm,
    }


def check_prefix_visibility_obstruction() -> dict[str, float]:
    prefix = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    invisible_output = np.array([0.0, 1.0], dtype=np.complex128)
    bad_corner = np.array([[0.0, 0.0], [1.0, 0.0]], dtype=np.complex128)

    source_kernel_norm = np.linalg.norm(prefix.conj().T @ invisible_output)
    corner_adjoint_norm = np.linalg.norm(bad_corner.conj().T @ invisible_output)

    return {
        "prefix_kernel_norm": source_kernel_norm,
        "corner_adjoint_norm": corner_adjoint_norm,
        "visibility_violation": corner_adjoint_norm - source_kernel_norm,
    }


def main() -> None:
    placement = check_two_root_composite_placement()
    extension = check_extension_ambiguity()
    visibility = check_prefix_visibility_obstruction()
    tolerance = 2e-11

    for name, value in placement.items():
        print(f"{name:28s} {value:.12e}")
    for name, value in extension.items():
        print(f"{name:28s} {value:.12e}")
    for name, value in visibility.items():
        print(f"{name:28s} {value:.12e}")

    if max(placement.values()) > tolerance:
        raise SystemExit("two-root composite placement check failed")
    if extension["agreement_error"] > tolerance:
        raise SystemExit("extensions do not agree on the source subspace")
    if extension["zero_extension_norm"] > tolerance:
        raise SystemExit("zero extension unexpectedly acts off the source")
    if extension["identity_extension_difference"] > tolerance:
        raise SystemExit("identity extension does not preserve the off-model vector")
    if extension["off_model_ambiguity"] <= 0.5:
        raise SystemExit("extension ambiguity was not detected")
    if visibility["prefix_kernel_norm"] > tolerance:
        raise SystemExit("chosen vector is not invisible to the prefix")
    if visibility["corner_adjoint_norm"] <= 0.5:
        raise SystemExit("corner does not violate prefix visibility")


if __name__ == "__main__":
    main()
