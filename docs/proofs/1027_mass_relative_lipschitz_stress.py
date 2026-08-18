"""Stress-test the mass-relative Gamma_R head constant on D3 roots.

The formal Gamma_R majorant uses a Lipschitz constant for the compact-log
test.  This probe normalizes the convolution-square mass to one and measures
a lower bound for the derivative size of its autocorrelation on the interior
of the support.  The D3 construction still has the exact three formal
vanishing nodes; the residuals below are only floating-point diagnostics.

This is a route-selection probe, not a Lean theorem and not a proof that no
special finite-dimensional owner can have a uniform constant.
"""

from __future__ import annotations

import numpy as np


def integrate(values: np.ndarray, grid: np.ndarray) -> float:
    """Use the available trapezoid API across supported NumPy versions."""
    if hasattr(np, "trapezoid"):
        return float(np.trapezoid(values, grid))
    return float(np.trapz(values, grid))


def bell(t: np.ndarray, radius: float) -> np.ndarray:
    result = np.zeros_like(t)
    inside = np.abs(t) < radius
    result[inside] = np.exp(
        -(radius * radius) / (radius * radius - t[inside] * t[inside])
    )
    return result


def d3_fft(t: np.ndarray, h: np.ndarray) -> tuple[np.ndarray, float]:
    """Apply d/dt (d/dt+1/2) (d/dt+1) with zero padding."""
    count = len(t)
    step = t[1] - t[0]
    padded_count = 1 << (int(np.ceil(np.log2(2 * count))) + 3)
    padded = np.zeros(padded_count)
    padded[:count] = h
    frequency = np.fft.fftfreq(padded_count, d=step) * 2.0 * np.pi
    derivative = 1.0j * frequency
    operator = derivative**3 + 1.5 * derivative**2 + 0.5 * derivative
    output = np.real(np.fft.ifft(operator * np.fft.fft(padded)))
    return output[:count], step


def laplace_residual(t: np.ndarray, g: np.ndarray, node: float) -> float:
    return abs(integrate(g * np.exp(node * t), t))


def run_case(frequency: float, t: np.ndarray) -> dict[str, float]:
    h = bell(t, 1.0 / 3.0) * np.cos(frequency * t)
    root, step = d3_fft(t, h)
    mass_before = integrate(root * root, t)
    root = root / np.sqrt(mass_before)
    mass = integrate(root * root, t)

    correlation = np.convolve(root[::-1], root, mode="full") * step
    correlation_grid = (t[0] - t[-1]) + step * np.arange(len(correlation))
    correlation_derivative = np.gradient(correlation, step)

    # This is a lower bound for the true Lipschitz constant: stay away from
    # the compact-support boundary where an FFT edge artifact can dominate.
    interior = np.abs(correlation_grid) <= 0.60
    lipschitz_lower = float(np.max(np.abs(correlation_derivative[interior])))
    laplace_max = max(
        laplace_residual(t, root, node) for node in (0.0, 0.5, 1.0)
    )
    return {
        "frequency": frequency,
        "mass": mass,
        "lipschitz_lower": lipschitz_lower,
        # For mass one, the source majorant coefficient 2*Lip + ||F(0)||
        # is at least this value for the measured derivative lower bound.
        "head_constant_lower": 2.0 * lipschitz_lower + 1.0,
        "laplace_residual": laplace_max,
    }


def main() -> None:
    t = np.linspace(-0.42, 0.42, 16385)
    frequencies = (0.0, 8.0, 16.0, 32.0, 64.0, 96.0, 128.0, 192.0, 256.0)
    print("D3 mass-relative Lipschitz stress screen (2026-08-18)")
    print("frequency mass lipschitz_lower head_constant_lower laplace_residual")
    for frequency in frequencies:
        result = run_case(frequency, t)
        print(
            f"{result['frequency']:9.1f} {result['mass']:.8f} "
            f"{result['lipschitz_lower']:.6e} "
            f"{result['head_constant_lower']:.6e} "
            f"{result['laplace_residual']:.6e}"
        )
    print(
        "Interpretation: growth of the normalized lower bound challenges a "
        "small frequency-uniform mass coefficient for this sampled D3 family; "
        "it does not reject a finite-band or owner-specific certificate."
    )


if __name__ == "__main__":
    main()
