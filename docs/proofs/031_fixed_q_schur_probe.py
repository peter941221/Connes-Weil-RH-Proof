"""Direct fixed-q Schur-complement probe for the source Lambert q-matrix.

This bypasses moment quadrature.  It builds the finite parity blocks from
Consani--Moscovici, Proposition 5.3, using the exact Meixner Poisson kernel.
Every section is rejected unless the normalized Gram matrix is symmetric
positive definite and obeys the source density-equivalence eigenvalue bounds.
"""

import argparse

import numpy as np
from scipy.special import gammaln, hyp2f1


def meixner_poisson(t: float, m: int, n: int) -> float:
    prefactor = (1 - t) ** (m + n) / (1 + t) ** (m + n + 0.5)
    argument = -4 * t / (1 - t) ** 2
    return float(prefactor * hyp2f1(-m, -n, 0.5, argument))


def eta_normalization(index: int) -> float:
    log_central_binomial = (
        gammaln(2 * index + 1) - 2 * gammaln(index + 1)
    )
    return float(np.exp(0.5 * log_central_binomial - index * np.log(2)))


def parity_gram(max_degree: int, q: float, parity: int, layers: int):
    indices = np.arange(parity, max_degree + 1, 2, dtype=int)
    size = indices.size
    perturbation = np.zeros((size, size))
    normalizations = np.array([eta_normalization(int(m)) for m in indices])

    for row, m in enumerate(indices):
        for column in range(row + 1):
            n = int(indices[column])
            lambert_entry = 0.0
            for r in range(1, layers + 1):
                lambert_entry += q**r * meixner_poisson(q ** (2 * r), int(m), n)
            value = (
                (1 if parity == 0 else -1)
                * 2
                * np.sqrt(2)
                * normalizations[row]
                * normalizations[column]
                * lambert_entry
            )
            perturbation[row, column] = value
            perturbation[column, row] = value

    return indices, np.eye(size) + perturbation


def schur_last(matrix: np.ndarray) -> float:
    if matrix.shape == (1, 1):
        return float(matrix[0, 0])
    boundary = matrix[-1, :-1]
    return float(matrix[-1, -1] - boundary @ np.linalg.solve(
        matrix[:-1, :-1], boundary
    ))


def run_probe(q: float = 0.5, layers: int = 32):
    a = np.sqrt(q)
    lower_bound = (1 - a) / (1 + a)
    upper_bound = (1 + a) / (1 - a)
    print(f"q={q} layers={layers} admissible=[{lower_bound:.6g}, {upper_bound:.6g}]")
    print("n min_eig max_eig s_n s_n+1 ratio a_p-a_inf scaled")
    for degree in (16, 24, 32, 48, 64, 96, 128):
        schurs = []
        extrema = []
        rejected = False
        for active_degree in (degree, degree + 1):
            parity = active_degree % 2
            _, gram = parity_gram(active_degree, q, parity, layers)
            eigenvalues = np.linalg.eigvalsh(gram)
            if (
                not np.all(np.isfinite(gram))
                or eigenvalues[0] <= 0
                or eigenvalues[0] < lower_bound * (1 - 1e-8)
                or eigenvalues[-1] > upper_bound * (1 + 1e-8)
            ):
                print(
                    f"{degree:3d} rejected at degree={active_degree}: "
                    f"min={eigenvalues[0]:.6g} max={eigenvalues[-1]:.6g}"
                )
                rejected = True
                break
            schurs.append(schur_last(gram))
            extrema.append((eigenvalues[0], eigenvalues[-1]))
        if rejected:
            continue

        ratio = schurs[1] / schurs[0]
        archimedean = np.sqrt((degree + 0.5) * (degree + 1))
        difference = archimedean * (np.sqrt(ratio) - 1)
        print(
            f"{degree:3d} {min(x[0] for x in extrema):.8f} "
            f"{max(x[1] for x in extrema):.8f} {schurs[0]:.10f} "
            f"{schurs[1]:.10f} {ratio:.10f} {difference: .8f} "
            f"{difference / np.sqrt(degree): .8f}"
        )


def run_frequency_probe(q: float = 0.5, layers: int = 40, max_degree: int = 512):
    _, even_gram = parity_gram(max_degree, q, 0, layers)
    _, odd_gram = parity_gram(max_degree + 1, q, 1, layers)
    even_schurs = np.square(np.diag(np.linalg.cholesky(even_gram)))
    odd_schurs = np.square(np.diag(np.linalg.cholesky(odd_gram)))
    schurs = np.empty(max_degree + 2)
    schurs[0::2] = even_schurs
    schurs[1::2] = odd_schurs

    cayley_frequency = np.pi - 4 * np.arctan(q)
    print(
        "fit_start cayley_frequency amplitude second_harmonic rms max_error"
    )
    for fit_start in (32, 64, 128, 256):
        degrees = np.arange(fit_start, max_degree + 1)
        ratios = schurs[degrees + 1] / schurs[degrees]
        archimedean = np.sqrt((degrees + 0.5) * (degrees + 1))
        scaled = archimedean * (np.sqrt(ratios) - 1) / np.sqrt(degrees)
        design = np.column_stack(
            [
                np.ones(degrees.size),
                np.cos(cayley_frequency * degrees),
                np.sin(cayley_frequency * degrees),
                np.cos(2 * cayley_frequency * degrees),
                np.sin(2 * cayley_frequency * degrees),
                1 / np.sqrt(degrees),
            ]
        )
        coefficients = np.linalg.lstsq(design, scaled, rcond=None)[0]
        residual = scaled - design @ coefficients
        amplitude = np.hypot(coefficients[1], coefficients[2])
        second_harmonic = np.hypot(coefficients[3], coefficients[4])
        print(
            f"{fit_start:9d} {cayley_frequency:.10f} {amplitude:.10f} "
            f"{second_harmonic:.10f} {np.sqrt(np.mean(residual**2)):.3e} "
            f"{np.max(np.abs(residual)):.3e}"
        )


def run_cross_prime_probe(max_degree: int = 512):
    print(
        "p q lower_bound min_eig omega amplitude phase residual_rms "
        "sigma B_real B_imag B_rms"
    )
    for prime in (2, 3, 5, 7, 11):
        q = 1 / prime
        layers = 40 if prime == 2 else 24
        _, even_gram = parity_gram(max_degree, q, 0, layers)
        _, odd_gram = parity_gram(max_degree + 1, q, 1, layers)
        a = np.sqrt(q)
        lower_bound = (1 - a) / (1 + a)
        minimum_eigenvalue = min(
            np.linalg.eigvalsh(even_gram)[0],
            np.linalg.eigvalsh(odd_gram)[0],
        )
        if (
            not np.all(np.isfinite(even_gram))
            or not np.all(np.isfinite(odd_gram))
            or minimum_eigenvalue < lower_bound * (1 - 1e-8)
        ):
            print(
                f"{prime} rejected: lower_bound={lower_bound:.10f} "
                f"min_eig={minimum_eigenvalue:.10f}"
            )
            continue

        even_schurs = np.square(np.diag(np.linalg.cholesky(even_gram)))
        odd_schurs = np.square(np.diag(np.linalg.cholesky(odd_gram)))
        schurs = np.empty(max_degree + 2)
        schurs[0::2] = even_schurs
        schurs[1::2] = odd_schurs
        degrees = np.arange(128, max_degree + 1)
        ratios = schurs[degrees + 1] / schurs[degrees]
        archimedean = np.sqrt((degrees + 0.5) * (degrees + 1))
        scaled = archimedean * (np.sqrt(ratios) - 1) / np.sqrt(degrees)
        frequency = np.pi - 4 * np.arctan(q)
        design = np.column_stack(
            [
                np.ones(degrees.size),
                np.cos(frequency * degrees),
                np.sin(frequency * degrees),
                np.cos(2 * frequency * degrees),
                np.sin(2 * frequency * degrees),
                1 / np.sqrt(degrees),
            ]
        )
        coefficients = np.linalg.lstsq(design, scaled, rcond=None)[0]
        residual = scaled - design @ coefficients
        amplitude = np.hypot(coefficients[1], coefficients[2])
        phase = np.arctan2(-coefficients[2], coefficients[1])
        boundary_design = np.column_stack(
            [
                np.ones(degrees.size),
                np.cos(frequency * degrees) / np.sqrt(degrees),
                np.sin(frequency * degrees) / np.sqrt(degrees),
                1 / degrees,
                np.cos(2 * frequency * degrees) / degrees,
                np.sin(2 * frequency * degrees) / degrees,
            ]
        )
        boundary_coefficients = np.linalg.lstsq(
            boundary_design, np.log(schurs[degrees]), rcond=None
        )[0]
        boundary_residual = (
            np.log(schurs[degrees])
            - boundary_design @ boundary_coefficients
        )
        print(
            f"{prime:2d} {q:.9f} {lower_bound:.9f} "
            f"{minimum_eigenvalue:.9f} {frequency:.9f} {amplitude:.9f} "
            f"{phase:.9f} {np.sqrt(np.mean(residual**2)):.3e} "
            f"{np.exp(boundary_coefficients[0]):.9f} "
            f"{boundary_coefficients[1]:.9f} "
            f"{-boundary_coefficients[2]:.9f} "
            f"{np.sqrt(np.mean(boundary_residual**2)):.3e}"
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--cross-primes", action="store_true")
    arguments = parser.parse_args()
    if arguments.cross_primes:
        run_cross_prime_probe()
    else:
        run_probe()
        run_frequency_probe()
