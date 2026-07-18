"""Non-periodic Burnol-window probe for the complete Toeplitz covariance.

This is a finite-element diagnostic, not a proof of Gate 3U.  It discretizes
the actual even cosine transform on the source window [0, 1] and evaluates
Burnol's complementary-Gram Schur difference

    M(z + u) - M(z) G^{-1} M(u),

where M(t) = A* U_t A and G = M(0).  The compact test is Q phi with
Q = -d^2/du^2 + 1/4, so both half-density characters are annihilated before
the first absolute value.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def shifted_legendre_values(size: int, points: np.ndarray) -> np.ndarray:
    """Orthonormal shifted Legendre basis values on [0, 1]."""
    values = np.polynomial.legendre.legvander(2.0 * points - 1.0, size - 1)
    return values * np.sqrt(2.0 * np.arange(size, dtype=float) + 1.0)


def interval_overlap_matrix(
    size: int, rho: float, integration_order: int
) -> np.ndarray:
    """Legendre-Galerkin matrix of f(x) -> sqrt(rho) f(rho x) on [0, 1]."""
    upper = min(1.0, 1.0 / rho)
    nodes, weights = np.polynomial.legendre.leggauss(integration_order)
    points = 0.5 * upper * (nodes + 1.0)
    weights = 0.5 * upper * weights
    output_values = shifted_legendre_values(size, points)
    input_values = shifted_legendre_values(size, rho * points)
    return math.sqrt(rho) * output_values.T @ (weights[:, None] * input_values)


def cosine_rectangle_matrix(
    size: int, rho: float, orientation: int, integration_order: int
) -> np.ndarray:
    """Legendre-Galerkin matrix of the two windowed cosine-transform blocks."""
    nodes, weights = np.polynomial.legendre.leggauss(integration_order)
    points = 0.5 * (nodes + 1.0)
    weights = 0.5 * weights
    basis = shifted_legendre_values(size, points)
    if orientation == 1:
        frequency = 2.0 * math.pi * rho
        amplitude = 2.0 * math.sqrt(rho)
    elif orientation == -1:
        frequency = 2.0 * math.pi / rho
        amplitude = 2.0 / math.sqrt(rho)
    else:
        raise ValueError("orientation must be +1 or -1")

    kernel = amplitude * np.cos(frequency * np.outer(points, points))
    weighted_basis = weights[:, None] * basis
    return weighted_basis.T @ kernel @ weighted_basis


def boundary_gram_moment(
    size: int, displacement: float, integration_order: int
) -> np.ndarray:
    """The 2-by-2 Burnol boundary moment M(t)=A*U_t A."""
    rho = math.exp(displacement)
    direct = interval_overlap_matrix(size, rho, integration_order)
    reverse = interval_overlap_matrix(size, 1.0 / rho, integration_order)
    forward_fourier = cosine_rectangle_matrix(size, rho, 1, integration_order)
    reverse_fourier = cosine_rectangle_matrix(size, rho, -1, integration_order)
    return np.block(
        [[direct, forward_fourier], [reverse_fourier, reverse]]
    ).astype(complex)


def compact_phi_and_qphi(points: np.ndarray, radius: float) -> tuple[np.ndarray, np.ndarray]:
    """C^3 compact bump phi=(1-(u/B)^2)^4 and Q phi."""
    scaled = points / radius
    inside = np.abs(scaled) < 1.0
    phi = np.zeros_like(points)
    second = np.zeros_like(points)
    x = scaled[inside]
    phi[inside] = (1.0 - x * x) ** 4
    second[inside] = (
        -8.0 + 72.0 * x * x - 120.0 * x**4 + 56.0 * x**6
    ) / (radius * radius)
    return phi, -second + 0.25 * phi


def response(
    size: int,
    radius: float,
    quadrature_order: int,
    displacement: float,
    integration_order: int,
) -> dict[str, float]:
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    shifts = radius * nodes
    weights = radius * weights
    phi, qphi = compact_phi_and_qphi(shifts, radius)

    gram = boundary_gram_moment(size, 0.0, integration_order)
    gram_condition = float(np.linalg.cond(gram))
    gram_inverse = np.linalg.inv(gram)
    moment_z = boundary_gram_moment(size, displacement, integration_order)
    static_phi = 0.0j
    compressed_phi = 0.0j
    static_q = 0.0j
    compressed_q = 0.0j
    phi_covariance_direct = 0.0j
    q_covariance_direct = 0.0j
    moment_q_zero = np.zeros_like(gram)
    for shift, weight, phi_value, q_value in zip(shifts, weights, phi, qphi):
        moment_shift = boundary_gram_moment(size, float(shift), integration_order)
        moment_far = boundary_gram_moment(
            size, displacement + float(shift), integration_order
        )
        static_scalar = np.trace(gram_inverse @ moment_far)
        compressed_matrix = moment_z @ gram_inverse @ moment_shift
        compressed_scalar = np.trace(gram_inverse @ compressed_matrix)
        covariance_scalar = np.trace(
            gram_inverse @ (moment_far - compressed_matrix)
        )
        static_phi += weight * phi_value * static_scalar
        compressed_phi += weight * phi_value * compressed_scalar
        static_q += weight * q_value * static_scalar
        compressed_q += weight * q_value * compressed_scalar

        # Accumulating the Schur difference directly is the only continuum-
        # meaningful ordering; the two displayed terms need not converge
        # separately under a finite-rank cutoff.
        phi_covariance_direct += weight * phi_value * covariance_scalar
        q_covariance_direct += weight * q_value * covariance_scalar
        moment_q_zero += weight * q_value * moment_shift

    one = np.zeros(size)
    one[0] = 1.0
    evaluation_zero = np.sqrt(2.0 * np.arange(size) + 1.0) * (
        (-1.0) ** np.arange(size)
    )
    residue_column = np.concatenate((evaluation_zero, 2.0 * one)).astype(complex)
    residue_row = np.concatenate((one, 0.5 * evaluation_zero)).astype(complex)
    expected_column_preimage = np.concatenate((evaluation_zero, np.zeros(size)))
    expected_row_preimage = np.concatenate((np.zeros(size), 0.5 * evaluation_zero))
    actual_column_preimage = gram_inverse @ residue_column
    actual_row_preimage = gram_inverse @ residue_row
    residue_scalar = np.vdot(
        residue_row, gram_inverse @ moment_q_zero @ actual_column_preimage
    )

    return {
        "gram_condition": gram_condition,
        "boundary_column_error": float(
            np.linalg.norm(actual_column_preimage - expected_column_preimage)
            / max(1.0, np.linalg.norm(expected_column_preimage))
        ),
        "boundary_row_error": float(
            np.linalg.norm(actual_row_preimage - expected_row_preimage)
            / max(1.0, np.linalg.norm(expected_row_preimage))
        ),
        "residue_scalar": float(residue_scalar.real),
        "phi_static": float(static_phi.real),
        "phi_compressed": float(compressed_phi.real),
        "phi_covariance": float(phi_covariance_direct.real),
        "q_static": float(static_q.real),
        "q_compressed": float(compressed_q.real),
        "q_covariance": float(q_covariance_direct.real),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sizes", default="20,28")
    parser.add_argument("--radius", type=float, default=0.8)
    parser.add_argument("--quadrature-order", type=int, default=48)
    parser.add_argument("--integration-order", type=int, default=160)
    parser.add_argument("--displacements", default="3,4,5,6")
    args = parser.parse_args()

    sizes = [int(value) for value in args.sizes.split(",")]
    displacements = [float(value) for value in args.displacements.split(",")]
    print("identity=Burnol complementary-Gram Schur tail")
    print("status=non-periodic finite-element diagnostic only")
    print("table=BEGIN")
    for size in sizes:
        for displacement in displacements:
            row = response(
                size,
                args.radius,
                args.quadrature_order,
                displacement,
                args.integration_order,
            )
            print(
                f"size={size:3d} z={displacement:4.1f} "
                f"gram_cond={row['gram_condition']:.4e} "
                f"phi_cov={row['phi_covariance']:+.6e} "
                f"q_static={row['q_static']:+.6e} "
                f"q_product={row['q_compressed']:+.6e} "
                f"q_cov={row['q_covariance']:+.6e} "
                f"half_scaled={math.exp(displacement / 2) * row['q_covariance']:+.6e} "
                f"three_half_scaled={math.exp(1.5 * displacement) * row['q_covariance']:+.6e}"
            )
        print(
            f"boundary size={size:3d} "
            f"column_error={row['boundary_column_error']:.3e} "
            f"row_error={row['boundary_row_error']:.3e} "
            f"q_residue={row['residue_scalar']:+.6e}"
        )
    print("table=END")
    print("complete_covariance_owner=SCHUR_DIFFERENCE")
    print("half_density_compressed_residue=Q_ANNIHILATED")
    print("finite_section_is_proof=FALSE")
    print("gate_3u=OPEN")
    print("RH=UNPROVED")


if __name__ == "__main__":
    main()
