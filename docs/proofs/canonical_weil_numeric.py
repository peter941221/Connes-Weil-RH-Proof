"""Numerical readout of the canonical compact-log Weil functional.

This module mirrors the definitions in C1SameOwnerWeil.lean for real-valued
compact log tests. It provides evidence only; floating-point quadrature is not
a Lean proof.
"""

import math

import numpy as np


CRITICAL_POINTS = (0.0, 0.5, 1.0)
DEFAULT_INVARIANT_TOLERANCE = 1e-8


def integrate(values, grid):
    """Use the NumPy spelling available in the installed version."""
    trapezoid = getattr(np, "trapezoid", None)
    if trapezoid is None:
        trapezoid = np.trapz
    return float(trapezoid(values, grid))


def smooth_transition(value):
    value = np.asarray(value, dtype=float)
    result = np.zeros_like(value)
    result[value >= 1.0] = 1.0
    core = (value > 0.0) & (value < 1.0)
    core_value = value[core]
    left = np.exp(-1.0 / core_value)
    right = np.exp(-1.0 / (1.0 - core_value))
    result[core] = left / (left + right)
    return result


def centered_bump(grid):
    """The support-[-1,1], plateau-[-1/2,1/2] bump used by probe 987."""
    return smooth_transition(2.0 - 2.0 * np.abs(np.asarray(grid, dtype=float)))


def interval_bump(grid, lo, hi):
    """A C-infinity bump supported on [lo, hi]."""
    if not lo < hi:
        raise ValueError("expected lo < hi")
    grid = np.asarray(grid, dtype=float)
    half_width = (hi - lo) / 2.0
    return (
        smooth_transition((grid - lo) / half_width)
        * smooth_transition((hi - grid) / half_width)
    )


def mellin_moment(test, grid, point):
    return integrate(np.exp(point * grid) * test, grid)


def smooth_finite_vanishing_test(grid, lo, hi):
    """Build a smooth compact test vanishing at 0, 1/2, and 1.

    The test has the form

        bump_[lo,hi](t) * (c0 + c1*t + c2*t^2 + c3*t^3).

    A right-null vector of the 3-by-4 Mellin moment matrix supplies the
    coefficients. L2 normalization makes comparisons across widths stable.
    """
    grid = np.asarray(grid, dtype=float)
    bump = interval_bump(grid, lo, hi)
    basis = np.column_stack([bump * grid**degree for degree in range(4)])
    moment_matrix = np.array(
        [
            [mellin_moment(basis[:, degree], grid, point) for degree in range(4)]
            for point in CRITICAL_POINTS
        ]
    )
    _left, singular_values, right = np.linalg.svd(moment_matrix, full_matrices=True)
    coefficients = right[-1]
    test = basis @ coefficients
    l2_sq = integrate(test * test, grid)
    if not l2_sq > 0.0:
        raise RuntimeError("finite-vanishing null vector has zero L2 mass")
    test = test / math.sqrt(l2_sq)
    coefficients = coefficients / math.sqrt(l2_sq)
    moments = {
        point: mellin_moment(test, grid, point) for point in CRITICAL_POINTS
    }
    return {
        "test": test,
        "bump": bump,
        "coefficients": coefficients,
        "moments": moments,
        "singular_values": singular_values,
        "l2": integrate(test * test, grid),
    }


def convolution_square(test, dx):
    """Return positive lags of g-star convolution g for a real test g."""
    sample_count = len(test)
    fft_count = 1 << int(math.ceil(math.log2(2 * sample_count)))
    spectrum = np.fft.rfft(test, fft_count)
    square = np.fft.irfft(spectrum * np.conj(spectrum), fft_count) * dx
    lags = np.arange(fft_count, dtype=float) * dx
    return lags, square


def _support_grid(square, dx, support_radius):
    if not support_radius > 0.0:
        raise ValueError("support_radius must be positive")
    final_index = int(math.floor(support_radius / dx))
    grid = np.arange(final_index + 1, dtype=float) * dx
    values = square[: final_index + 1].copy()
    if grid[-1] < support_radius - 8.0 * np.finfo(float).eps:
        grid = np.append(grid, support_radius)
        values = np.append(
            values,
            np.interp(support_radius, np.arange(len(square)) * dx, square),
        )
    return grid, values


def von_mangoldt(n):
    """Return log(p) when n is a positive power of one prime p."""
    if n < 2:
        return 0.0
    divisor = 2
    while divisor * divisor <= n and n % divisor != 0:
        divisor += 1
    prime = n if divisor * divisor > n else divisor
    remainder = n
    while remainder % prime == 0:
        remainder //= prime
    return math.log(prime) if remainder == 1 else 0.0


def canonical_weil_value(test, grid, support_radius):
    """Evaluate pole - archimedean - all visible prime-power terms.

    The input must be real-valued, sampled on a uniform grid, and supported in
    an interval of length at most support_radius. Its convolution square then
    has support in [-support_radius, support_radius].
    """
    grid = np.asarray(grid, dtype=float)
    test = np.asarray(test, dtype=float)
    if len(grid) != len(test) or len(grid) < 2:
        raise ValueError("test and grid must have the same nontrivial length")
    dx = float(grid[1] - grid[0])
    if not np.allclose(np.diff(grid), dx, rtol=0.0, atol=abs(dx) * 1e-8):
        raise ValueError("grid must be uniform")

    lags, square = convolution_square(test, dx)
    positive_grid, positive_square = _support_grid(square, dx, support_radius)
    leading = float(square[0])
    l2 = integrate(test * test, grid)

    # SelectedWeilSquareOwner.poleTerm uses the two real Laplace points +/-1/2.
    laplace_half = integrate(
        2.0 * np.cosh(positive_grid / 2.0) * positive_square,
        positive_grid,
    )
    pole = 2.0 * laplace_half
    mellin_plus = mellin_moment(test, grid, 0.5)
    mellin_minus = mellin_moment(test, grid, -0.5)
    pole_from_product = 2.0 * mellin_plus * mellin_minus

    # SelectedWeilSquareOwner.archimedeanTerm. The exact tail is
    # A * log(tanh(R/2)), since the denominator is 2*sinh(y).
    denominator = np.empty_like(positive_grid)
    denominator[0] = 1.0
    denominator[1:] = (
        np.exp(positive_grid[1:]) * (-np.expm1(-2.0 * positive_grid[1:]))
    )
    numerator = (
        2.0 * np.exp(positive_grid / 2.0) * positive_square - 2.0 * leading
    )
    arch_density = numerator / denominator
    arch_density[0] = leading / 2.0
    arch_integral_body = integrate(arch_density, positive_grid)
    arch_integral_tail = leading * math.log(math.tanh(support_radius / 2.0))
    arch_coefficient = math.log(4.0 * math.pi) + np.euler_gamma
    archimedean = (
        arch_coefficient * leading + arch_integral_body + arch_integral_tail
    )

    # SelectedWeilSquareOwner.finitePrimeTerm samples +/-log(n), not n and 1/n.
    prime_terms = []
    prime_sum = 0.0
    max_index = int(math.floor(math.exp(support_radius) + 1e-12))
    for n in range(2, max_index + 1):
        weight = von_mangoldt(n)
        if weight == 0.0:
            continue
        log_n = math.log(n)
        square_at_log_n = float(np.interp(log_n, positive_grid, positive_square))
        term = weight * (2.0 * square_at_log_n) / math.sqrt(n)
        prime_terms.append((n, term, square_at_log_n))
        prime_sum += term

    return {
        "A": leading,
        "l2": l2,
        "arch": archimedean,
        "arch_body": arch_integral_body,
        "arch_tail": arch_integral_tail,
        "pole": pole,
        "pole_from_product": pole_from_product,
        "pole_identity_error": pole - pole_from_product,
        "prime_sum": prime_sum,
        "prime_terms": prime_terms,
        "psi": pole - archimedean - prime_sum,
        "lags": lags,
        "square": square,
    }


def assert_canonical_invariants(
    result,
    moments=None,
    tolerance=DEFAULT_INVARIANT_TOLERANCE,
):
    """Fail when a probe no longer mirrors the defining Lean identities."""
    if tolerance <= 0.0:
        raise ValueError("tolerance must be positive")

    leading_error = abs(result["A"] - result["l2"])
    if leading_error >= tolerance:
        raise AssertionError(
            "convolution-square invariant failed: "
            f"abs(A - L2)={leading_error:.3e} >= {tolerance:.3e}"
        )

    pole_error = abs(result["pole"] - result["pole_from_product"])
    if pole_error >= tolerance:
        raise AssertionError(
            "pole product invariant failed: "
            f"abs(pole - 2*M(1/2)*M(-1/2))={pole_error:.3e} "
            f">= {tolerance:.3e}"
        )

    moment_error = None
    if moments is not None:
        missing = set(CRITICAL_POINTS).difference(moments)
        if missing:
            raise AssertionError(f"missing critical moments: {sorted(missing)}")
        moment_error = max(abs(moments[point]) for point in CRITICAL_POINTS)
        if moment_error >= tolerance:
            raise AssertionError(
                "finite-vanishing invariant failed: "
                f"max(abs(M0), abs(Mhalf), abs(M1))={moment_error:.3e} "
                f">= {tolerance:.3e}"
            )

    return {
        "leading_error": leading_error,
        "pole_error": pole_error,
        "moment_error": moment_error,
        "tolerance": tolerance,
    }
