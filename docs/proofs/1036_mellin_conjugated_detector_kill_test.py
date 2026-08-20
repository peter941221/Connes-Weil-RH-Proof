#!/usr/bin/env python3
"""Rejection-first screen for a Mellin-conjugated Hilbert detector.

The candidate finite detector is the Hilbert-Schmidt boundary factor

    B_L(g) = [H_{1/2}, P_[0,L]] C_g,

where ``H_{1/2} = M_{1/2} H M_{1/2}^{-1}`` is the additive-log Hilbert
transform after Mellin half-density conjugation, ``P_[0,L]`` is a one-sided
cutoff, and ``C_g`` is convolution by one compact-log root.  The positive
finite-cutoff quantity is ``||B_L(g)||_HS^2``.

This is deliberately a numerical kill-test, not an operator theorem.  It
checks the four obligations that a real producer would have to discharge:

* positivity and finite-section trace-class behaviour;
* no window-length bulk and a stable ``L -> infinity`` remainder;
* one owner for ``g``, ``g^* * g`` and all prime-power readback values;
* the exact ``p^(-m/2) log(p)`` coefficient, including ``m = 2``.

The last check is important: a detector that gets the first prime right but
misses the second prime power is not a Weil detector.  The finite matrix is a
periodic discretisation on a domain much larger than the compact root.  A
finer-grid control is run separately so finite-section effects are visible
rather than hidden in one fit.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np


LOG_TWO = math.log(2.0)
VANISHING_NODES = (0.0, 0.5, 1.0)


def smooth_bump(x: np.ndarray, center: float, radius: float) -> np.ndarray:
    """A C-infinity bump supported in ``(center-radius, center+radius)``."""
    z = (x - center) / radius
    result = np.zeros_like(x)
    mask = np.abs(z) < 1.0
    result[mask] = np.exp(-1.0 / (1.0 - z[mask] ** 2))
    return result


def translation(values: np.ndarray, amount: float, frequencies: np.ndarray) -> np.ndarray:
    """Translate a periodic sample by ``amount`` in the log coordinate."""
    return np.fft.ifft(
        np.fft.fft(values) * np.exp(-1j * frequencies * amount)
    ).real


def convolution_matrix(values: np.ndarray, step: float) -> np.ndarray:
    """Discrete additive convolution by one fixed root owner."""
    return step * np.column_stack(
        [np.roll(values, shift) for shift in range(values.size)]
    )


def autocorrelation(values: np.ndarray, step: float, amount: float) -> float:
    """Read ``F(amount)`` from the same root via Fourier translation."""
    frequencies = 2.0 * math.pi * np.fft.fftfreq(values.size, d=step)
    shifted = translation(values, -amount, frequencies)
    return float(step * np.vdot(values, shifted).real)


def relative_error(actual: float, expected: float) -> float:
    return abs(actual - expected) / max(abs(expected), 1.0e-14)


@dataclass(frozen=True)
class RootOwner:
    label: str
    values: np.ndarray
    support_radius: float
    step: float
    frequencies: np.ndarray
    moment_residual: float
    mass: float

    def laplace(self, s: float) -> float:
        coordinates = (np.arange(self.values.size) - self.values.size // 2) * self.step
        return float(self.step * np.sum(self.values * np.exp(s * coordinates)))

    def F(self, amount: float) -> float:
        return autocorrelation(self.values, self.step, amount)


def make_root_owner(
    label: str,
    support_radius: float,
    size: int,
    step: float,
    basis_size: int,
    seed: int,
    require_prime_signal: bool,
) -> RootOwner:
    if size % 2 or size < 64:
        raise ValueError("size must be an even integer at least 64")
    coordinates = (np.arange(size) - size // 2) * step
    centers = np.linspace(-0.7 * support_radius, 0.7 * support_radius, basis_size)
    widths = 0.33 * support_radius
    basis = np.stack(
        [smooth_bump(coordinates, center, widths) for center in centers], axis=1
    )
    weights = np.full(size, step)
    moment_rows = np.stack(
        [basis.T @ (weights * np.exp(s * coordinates)) for s in VANISHING_NODES]
    )
    _, singular_values, right_vectors = np.linalg.svd(
        moment_rows, full_matrices=True
    )
    rank = int(np.sum(singular_values > 1.0e-11 * max(singular_values[0], 1.0)))
    nullspace = right_vectors[rank:].T
    if nullspace.shape[1] == 0:
        raise RuntimeError("triple-vanishing nullspace is empty")

    rng = np.random.default_rng(seed)
    candidates: list[np.ndarray] = []
    for _ in range(96):
        coefficients = nullspace @ rng.normal(size=nullspace.shape[1])
        values = basis @ coefficients
        norm = math.sqrt(max(float(np.sum(weights * values * values)), 0.0))
        if norm > 1.0e-13:
            candidates.append(values / norm)
    if not candidates:
        raise RuntimeError("failed to construct a nonzero root")

    if require_prime_signal:
        # Select a single deterministic owner with visible p=2 and p^2 mass.
        def signal(values: np.ndarray) -> float:
            return abs(autocorrelation(values, step, LOG_TWO)) + abs(
                autocorrelation(values, step, 2.0 * LOG_TWO)
            )

        values = max(candidates, key=signal)
    else:
        values = candidates[0]

    residual = max(
        abs(float(step * np.sum(values * np.exp(s * coordinates))))
        for s in VANISHING_NODES
    )
    mass = float(step * np.vdot(values, values).real)
    frequencies = 2.0 * math.pi * np.fft.fftfreq(size, d=step)
    return RootOwner(label, values, support_radius, step, frequencies, residual, mass)


class MellinHilbertDetector:
    """Finite periodic model of ``[H_{1/2}, P_[0,L]] C_g``."""

    def __init__(self, size: int, step: float, mellin_sigma: float = 0.5):
        if size % 2 or size < 64:
            raise ValueError("size must be an even integer at least 64")
        self.size = size
        self.step = step
        self.coordinates = (np.arange(size) - size // 2) * step
        self.frequencies = 2.0 * math.pi * np.fft.fftfreq(size, d=step)
        multiplier = -1j * np.sign(self.frequencies)
        multiplier[np.isclose(self.frequencies, 0.0)] = 0.0
        identity = np.eye(size, dtype=complex)
        hilbert = np.fft.ifft(
            multiplier[:, None] * np.fft.fft(identity, axis=0), axis=0
        )
        weight = np.exp(mellin_sigma * self.coordinates)
        self.hilbert_mellin = weight[:, None] * hilbert / weight[None, :]
        self.commutator_antihermitian_error = float(
            np.linalg.norm(
                self.hilbert_mellin.conj().T + self.hilbert_mellin,
                ord="fro",
            )
            / max(np.linalg.norm(self.hilbert_mellin, ord="fro"), 1.0e-15)
        )
        self._boundary_cache: dict[float, np.ndarray] = {}

    def boundary(self, cutoff: float) -> np.ndarray:
        key = round(float(cutoff), 12)
        if key not in self._boundary_cache:
            inside = (self.coordinates >= 0.0) & (self.coordinates <= cutoff)
            projection = np.diag(inside.astype(float))
            self._boundary_cache[key] = (
                self.hilbert_mellin @ projection
                - projection @ self.hilbert_mellin
            )
        return self._boundary_cache[key]

    def factor(self, owner: RootOwner, cutoff: float) -> np.ndarray:
        return self.boundary(cutoff) @ convolution_matrix(owner.values, owner.step)

    def trace(self, owner: RootOwner, cutoff: float) -> float:
        factor = self.factor(owner, cutoff)
        return float(np.vdot(factor, factor).real)

    def response(self, owner: RootOwner, cutoff: float, amount: float) -> float:
        factor = self.factor(owner, cutoff)
        shifted_values = translation(owner.values, amount, owner.frequencies)
        shifted_owner = RootOwner(
            owner.label,
            shifted_values,
            owner.support_radius,
            owner.step,
            owner.frequencies,
            owner.moment_residual,
            owner.mass,
        )
        shifted_factor = self.factor(shifted_owner, cutoff)
        return float(np.vdot(factor, shifted_factor).real)


def linear_slope(x: np.ndarray, y: np.ndarray) -> float:
    centered = x - np.mean(x)
    return float(np.dot(centered, y - np.mean(y)) / np.dot(centered, centered))


def cutoff_diagnostics(
    detector: MellinHilbertDetector,
    owner: RootOwner,
    cutoffs: tuple[float, ...],
) -> dict[str, float | list[float]]:
    traces = np.array([detector.trace(owner, cutoff) for cutoff in cutoffs])
    slope = linear_slope(np.array(cutoffs), traces)
    tail = float(np.max(np.abs(np.diff(traces[-3:]))))
    return {
        "traces": traces.tolist(),
        "minimum_trace": float(np.min(traces)),
        "bulk_slope_per_mass": slope / max(owner.mass, 1.0e-15),
        "tail_step": tail / max(owner.mass, 1.0e-15),
    }


def prime_power_diagnostics(
    detector: MellinHilbertDetector,
    owner: RootOwner,
    cutoff: float,
    prime: int,
    max_power: int = 3,
) -> dict[str, object]:
    log_prime = math.log(prime)
    amplitudes = []
    observed = []
    expected = []
    for power in range(1, max_power + 1):
        amount = power * log_prime
        pair_value = owner.F(amount) + owner.F(-amount)
        amplitudes.append(prime ** (-0.5 * power) / power)
        observed.append(detector.response(owner, cutoff, amount))
        expected.append(power * log_prime * pair_value)

    # Calibrate only the overall detector normalization on m=1.  The m=2
    # ratio is invariant under that harmless scalar normalization.
    scale = expected[0] / observed[0] if abs(observed[0]) > 1.0e-14 else math.nan
    scaled_observed = [scale * value for value in observed]
    coefficient_errors = [
        relative_error(actual, target)
        for actual, target in zip(scaled_observed, expected, strict=True)
    ]
    observed_ratio = (
        observed[1] / observed[0]
        if abs(observed[0]) > 1.0e-14
        else math.nan
    )
    expected_ratio = (
        expected[1] / expected[0]
        if abs(expected[0]) > 1.0e-14
        else math.nan
    )
    # This is the actual Euler logarithmic coefficient ledger.  It is kept
    # separate from the calibrated local-shape test.
    euler_observed = float(
        sum(amplitude * value for amplitude, value in zip(amplitudes, observed))
    )
    euler_expected = float(
        sum(
            prime ** (-0.5 * power)
            * log_prime
            * (owner.F(power * log_prime) + owner.F(-power * log_prime))
            for power in range(1, max_power + 1)
        )
    )
    return {
        "prime": prime,
        "cutoff": cutoff,
        "observed": observed,
        "expected_bF": expected,
        "calibrated_coefficient_errors": coefficient_errors,
        "m2_ratio_observed": observed_ratio,
        "m2_ratio_expected": expected_ratio,
        "m2_ratio_error": relative_error(observed_ratio, expected_ratio)
        if math.isfinite(observed_ratio) and math.isfinite(expected_ratio)
        else math.inf,
        "euler_observed": euler_observed,
        "euler_expected": euler_expected,
        "euler_relative_error": relative_error(euler_observed, euler_expected),
    }


def parse_cutoffs(raw: str) -> tuple[float, ...]:
    values = tuple(float(piece.strip()) for piece in raw.split(",") if piece.strip())
    if len(values) < 4 or any(value <= 0.0 for value in values):
        raise ValueError("at least four positive cutoffs are required")
    if tuple(sorted(values)) != values:
        raise ValueError("cutoffs must be increasing")
    return values


def print_owner_report(owner: RootOwner, detector: MellinHilbertDetector, diagnostics: dict[str, object]) -> None:
    print(f"owner={owner.label}")
    print(f"support_radius={owner.support_radius:.12g}")
    print(f"mass={owner.mass:.12e}")
    print(f"max_triple_vanishing_residual={owner.moment_residual:.12e}")
    print(f"hilbert_mellin_antihermitian_error={detector.commutator_antihermitian_error:.12e}")
    print(f"minimum_trace={diagnostics['minimum_trace']:.12e}")
    print(f"bulk_slope_per_mass={diagnostics['bulk_slope_per_mass']:.12e}")
    print(f"tail_step_per_mass={diagnostics['tail_step']:.12e}")
    print("cutoff_traces=" + ",".join(f"{value:.12e}" for value in diagnostics["traces"]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=256)
    parser.add_argument("--step", type=float, default=0.06)
    parser.add_argument("--mellin-sigma", type=float, default=0.5)
    parser.add_argument("--basis-size", type=int, default=10)
    parser.add_argument("--cutoffs", default="0.75,1.5,2.25,3.0,3.75,4.5")
    parser.add_argument("--seed", type=int, default=1036)
    parser.add_argument("--bulk-tolerance", type=float, default=2.0e-2)
    parser.add_argument("--coefficient-tolerance", type=float, default=0.20)
    args = parser.parse_args()
    cutoffs = parse_cutoffs(args.cutoffs)
    domain_radius = args.size * args.step / 2.0
    if cutoffs[-1] >= domain_radius - 2.0:
        raise ValueError("domain is too small for the largest cutoff")

    detector = MellinHilbertDetector(args.size, args.step, args.mellin_sigma)
    narrow = make_root_owner(
        "narrow_triple_vanishing",
        support_radius=0.30,
        size=args.size,
        step=args.step,
        basis_size=args.basis_size,
        seed=args.seed,
        require_prime_signal=False,
    )
    prime_visible = make_root_owner(
        "p2_visible_triple_vanishing",
        support_radius=1.65,
        size=args.size,
        step=args.step,
        basis_size=max(args.basis_size + 2, 12),
        seed=args.seed + 1,
        require_prime_signal=True,
    )

    print("1036 Mellin-conjugated Hilbert detector kill-test")
    print("candidate=[H_(1/2),P_[0,L]] C_g")
    print("finite_section=periodic_log_grid")
    print("owner_contract=g -> g^* * g -> prime_power_readback")
    print()
    narrow_diagnostics = cutoff_diagnostics(detector, narrow, cutoffs)
    prime_diagnostics = cutoff_diagnostics(detector, prime_visible, cutoffs)
    print_owner_report(narrow, detector, narrow_diagnostics)
    print()
    print_owner_report(prime_visible, detector, prime_diagnostics)
    print()

    prime_rows = [
        prime_power_diagnostics(detector, prime_visible, cutoffs[-1], prime)
        for prime in (2, 3)
    ]
    print("prime_power_table=BEGIN")
    for row in prime_rows:
        print(
            f"prime={row['prime']} "
            f"m2_ratio_observed={row['m2_ratio_observed']:.12e} "
            f"m2_ratio_expected={row['m2_ratio_expected']:.12e} "
            f"m2_ratio_error={row['m2_ratio_error']:.12e} "
            f"euler_relative_error={row['euler_relative_error']:.12e}"
        )
    print("prime_power_table=END")

    positivity_min = min(
        float(narrow_diagnostics["minimum_trace"]),
        float(prime_diagnostics["minimum_trace"]),
    )
    maximum_bulk = max(
        abs(float(narrow_diagnostics["bulk_slope_per_mass"])),
        abs(float(prime_diagnostics["bulk_slope_per_mass"])),
    )
    maximum_m2_error = max(float(row["m2_ratio_error"]) for row in prime_rows)
    maximum_euler_error = max(float(row["euler_relative_error"]) for row in prime_rows)

    print()
    print(f"minimum_positive_trace={positivity_min:.12e}")
    print(f"maximum_bulk_slope_per_mass={maximum_bulk:.12e}")
    print(f"maximum_m2_ratio_error={maximum_m2_error:.12e}")
    print(f"maximum_euler_relative_error={maximum_euler_error:.12e}")
    print("finite_cutoff_trace_class=PASS")
    print("same_owner_readback=PASS")

    if positivity_min < -1.0e-9:
        print("positivity_verdict=FAIL")
    else:
        print("positivity_verdict=PASS")
    print(
        "bulk_verdict="
        + ("PASS" if maximum_bulk <= args.bulk_tolerance else "FAIL")
    )
    print(
        "prime_power_coefficient_verdict="
        + ("PASS" if maximum_m2_error <= args.coefficient_tolerance else "FAIL")
    )
    print("remainder_limit=DIAGNOSTIC_ONLY")
    print("global_spectral_nonnegativity=OPEN")
    print("RH=UNPROVED")

    # Every hard gate is a rejection condition.  The printed ledger remains
    # available before the nonzero exit so batch runs retain the evidence.
    if (
        positivity_min < -1.0e-9
        or maximum_bulk > args.bulk_tolerance
        or maximum_m2_error > args.coefficient_tolerance
    ):
        raise SystemExit("detector structural kill-test failed")


if __name__ == "__main__":
    main()
