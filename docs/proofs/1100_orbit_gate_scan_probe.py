"""Orbit-window semi-local gate scan (record 1100).

Prices the record-1099 exit gate `orbitWindowSemiLocalGate` numerically: the
quadratic form Q(g) = arch(g.convSq) + sum over visible prime powers of
(Lambda(q)/sqrt(q)) * (F(log q) + F(-log q)), with F the plain
autocorrelation of the profile, compressed to the orthonormal null space of
the three moment rows laplaceAt(g, s) = 0 at s in {0, 1/2, 1}.

The arch path is the CERTIFIED record-1020 machinery, imported from the
committed probe file (zero duplication).  The prime rows are new: F(log q)
is evaluated by analytic basis evaluation at shifted points (no
interpolation).

Pre-registration: docs/proofs/1100_orbit_gate_scan_preregistration.md
(committed before this run).  All gates are asserted; ABORT-class failures
exit before any scan row is consumed.  Numerical evidence only.
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import legvander
from scipy.linalg import eigh

_HERE = os.path.dirname(os.path.abspath(__file__))
_SPEC = importlib.util.spec_from_file_location(
    "rig1020", os.path.join(_HERE, "1020_lane_r_prime_free_spectrum.py")
)
assert _SPEC is not None and _SPEC.loader is not None
rig1020 = importlib.util.module_from_spec(_SPEC)
sys.modules["rig1020"] = rig1020  # register BEFORE exec_module (dataclasses)
_SPEC.loader.exec_module(rig1020)

VANISH_S = rig1020.VANISH_S
POS_THRESHOLD = 1.0e-3  # one order above the certified 5.6e-05 arch scale


def prime_powers_with_weight(bound: int) -> list[tuple[int, float]]:
    """(q, Lambda(q)/sqrt(q)) for every prime power q <= bound."""
    sieve = np.ones(bound + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(math.isqrt(bound)) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    lam = np.zeros(bound + 1)
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= bound:
            lam[q] = math.log(int(p))
            q *= int(p)
    return [
        (int(q), float(lam[q]) / math.sqrt(q))
        for q in np.nonzero(lam > 0.0)[0]
    ]


def sine_pair_integral(i: int, j: int, t: float, a: float) -> float:
    """Closed-form overlap int phi_i(u) phi_j(u+t) du for the sine family.

    phi_k(u) = sin(k pi (u/a + 1) / 2) on (-a, a); substitution v = u + a.
    """
    length = 2.0 * a
    ai = i * math.pi / length
    aj = j * math.pi / length
    lo = max(0.0, -t)
    hi = min(length, length - t)
    if hi <= lo:
        return 0.0

    def anti(c: float, d: float) -> float:
        if abs(c) < 1e-14:
            return (hi - lo) * math.cos(d)
        return (math.sin(c * hi + d) - math.sin(c * lo + d)) / c

    return 0.5 * (anti(ai - aj, -aj * t) - anti(ai + aj, aj * t))


@dataclass
class GateRow:
    radius: float
    family: str
    basis_size: int
    nullity: int
    n_terms: int
    top_total: float
    top_arch: float
    top_prime: float
    resid: float
    orth: float
    cond_g: float


class OrbitGateProbe:
    """The record-1020 rig adapted to orbit radii, plus prime rows."""

    def __init__(
        self,
        radius: float,
        basis_size: int,
        grid_size: int = 8001,
        envelope_power: int = 1,
        basis_family: str = "legendre",
        include_primes: bool = True,
    ):
        if radius <= 0.0:
            raise ValueError("radius must be positive")
        if basis_size < 4:
            raise ValueError("at least four basis functions are needed")
        if basis_family not in ("legendre", "sine"):
            raise ValueError("basis_family must be 'legendre' or 'sine'")
        self.radius = radius
        self.basis_size = basis_size
        self.envelope_power = envelope_power
        self.basis_family = basis_family
        self.include_primes = include_primes
        self.n = grid_size if grid_size % 2 == 1 else grid_size + 1
        self.t, self.step = np.linspace(
            -radius, radius, self.n, retstep=True
        )
        self.quad = rig1020.simpson_weights(self.n, self.step)
        self.mass = np.full(self.n, self.step)

        scaled = self.t / radius
        if basis_family == "legendre":
            vandermonde = legvander(scaled, basis_size - 1)
            envelope = rig1020.smooth_bump(scaled) ** envelope_power
            self.basis = (vandermonde.T * envelope).astype(float)
        else:
            phase = math.pi * (scaled + 1.0) / 2.0
            frequencies = np.arange(1, basis_size + 1)[:, None]
            self.basis = np.sin(frequencies * phase[None, :])

        # G-basis (pre-registered, part of G-arch-2): the analytic evaluator
        # must reproduce the sampled basis on the grid exactly.
        analytic = self.analytic_basis(self.t)
        basis_gap = float(np.max(np.abs(analytic - self.basis)))
        if basis_gap > 1e-12:
            raise FloatingPointError(
                f"analytic evaluator off by {basis_gap}"
            )

        two_r = 2.0 * self.radius
        self.prime_terms = []
        if include_primes:
            bound = int(math.floor(math.exp(two_r)))
            self.prime_terms = [
                (q, w)
                for (q, w) in prime_powers_with_weight(bound)
                if math.log(q) < two_r - 1e-9
            ]

    def analytic_basis(self, x: np.ndarray) -> np.ndarray:
        """(basis_size, len(x)) values of the basis functions at x; 0 outside."""
        size = self.basis_size
        out = np.zeros((size, x.size))
        scaled = x / self.radius
        inside = np.abs(scaled) < 1.0
        xs = scaled[inside]
        if self.basis_family == "legendre":
            vals = (
                legvander(xs, size - 1)
                * (rig1020.smooth_bump(xs) ** self.envelope_power)[:, None]
            ).T
        else:
            phase = math.pi * (xs + 1.0) / 2.0
            frequencies = np.arange(1, size + 1)[:, None]
            vals = np.sin(frequencies * phase[None, :])
        out[:, inside] = vals
        return out

    def laplace_matrix(self) -> np.ndarray:
        return np.stack(
            [
                np.sum(
                    self.quad[None, :] * self.basis
                    * np.exp(s * self.t)[None, :],
                    axis=1,
                )
                for s in VANISH_S
            ]
        )

    def nullspace(self) -> tuple[np.ndarray, np.ndarray]:
        moments = self.laplace_matrix()
        _, singular_values, vh = np.linalg.svd(moments, full_matrices=True)
        threshold = 1e-11 * max(float(singular_values[0]), 1.0)
        rank = int(np.sum(singular_values > threshold))
        return vh[rank:].T.copy(), singular_values

    def _orthonormal_null_functions(self):
        null_coefficients, singular_values = self.nullspace()
        weighted_basis = self.basis.T * np.sqrt(self.mass)[:, None]
        weighted_null = weighted_basis @ null_coefficients
        orthonormal_weighted, triangular = np.linalg.qr(
            weighted_null, mode="reduced"
        )
        if np.min(np.abs(np.diag(triangular))) <= 1e-14:
            raise FloatingPointError("weighted null basis is rank deficient")
        inverse_triangular = np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )
        coefficients = null_coefficients @ inverse_triangular
        functions = coefficients.T @ self.basis
        gram_condition = float(np.linalg.cond(triangular) ** 2)
        orth_error = float(
            np.max(np.abs(
                (functions * self.mass[None, :]) @ functions.T
                - np.eye(functions.shape[0])
            ))
        )
        return (
            functions,
            singular_values,
            coefficients,
            gram_condition,
            orth_error,
        )

    def prime_matrix(self, functions: np.ndarray) -> np.ndarray:
        """2 * sum_q (Lambda(q)/sqrt(q)) * F(log q) as a symmetric matrix."""
        dimension = functions.shape[0]
        matrix = np.zeros((dimension, dimension))
        for q, weight in self.prime_terms:
            shifted = self._shifted_functions(math.log(q))
            corr = self.step * (functions @ shifted.T)
            matrix += (2.0 * weight) * corr
        return (matrix + matrix.T) / 2.0

    def _shifted_functions(self, shift: float) -> np.ndarray:
        """Orthonormal null functions evaluated at t + shift (0 outside)."""
        return self.coefficients.T @ self.analytic_basis(self.t + shift)

    def arch_matrix(self, functions: np.ndarray) -> np.ndarray:
        dimension = functions.shape[0]
        arch = rig1020.PrimeFreeProbe._arch_of_function
        diagonal = np.empty(dimension)
        for i in range(dimension):
            diagonal[i] = arch(functions[i], self.step)[0]
        matrix = np.zeros((dimension, dimension))
        np.fill_diagonal(matrix, diagonal)
        for i in range(dimension):
            for j in range(i):
                combined = functions[i] + functions[j]
                combined_value = arch(combined, self.step)[0]
                value = 0.5 * (combined_value - diagonal[i] - diagonal[j])
                matrix[i, j] = value
                matrix[j, i] = value
        return (matrix + matrix.T) / 2.0

    def solve(self) -> GateRow:
        functions, _sv, self.coefficients, cond_g, orth = (
            self._orthonormal_null_functions()
        )
        arch_m = self.arch_matrix(functions)
        total_m = arch_m.copy()
        prime_m = np.zeros_like(arch_m)
        if self.include_primes:
            prime_m = self.prime_matrix(functions)
            total_m = arch_m + prime_m
        eig = lambda m: eigh(  # noqa: E731
            (m + m.T) / 2.0,
            np.eye(m.shape[0]),
            check_finite=True,
            eigvals_only=True,
        )
        moment_residual = float(
            np.max(np.abs(self.laplace_matrix() @ self.coefficients))
        )
        return GateRow(
            radius=self.radius,
            family=self.basis_family,
            basis_size=self.basis_size,
            nullity=functions.shape[0],
            n_terms=len(self.prime_terms),
            top_total=float(eig(total_m)[-1]),
            top_arch=float(eig(arch_m)[-1]),
            top_prime=float(eig(prime_m)[-1]),
            resid=moment_residual,
            orth=orth,
            cond_g=cond_g,
        )


ANCHOR: dict[tuple[float, int], float] = {
    (0.300, 8): -1.09132868,
    (0.300, 12): -1.07153088,
    (0.300, 16): -1.05884874,
    (0.330, 8): -0.99581113,
    (0.330, 12): -0.97600231,
    (0.330, 16): -0.96331391,
    (0.345, 8): -0.95124819,
    (0.345, 12): -0.93143347,
    (0.345, 16): -0.91874172,
}


def run_anchor_gates() -> None:
    print("G-arch-1 environment-drift measurement (record <= 1e-4 abs)")
    worst = 0.0
    for (radius, k), expected in ANCHOR.items():
        res = rig1020.PrimeFreeProbe(
            radius=radius,
            basis_size=k,
            grid_size=6001,
            envelope_power=1,
            basis_family="legendre",
        ).solve()
        top = float(res.eigenvalues[-1])
        gap = abs(top - expected)
        worst = max(worst, gap)
        print(
            f"  r={radius:.3f} K={k:2d} top={top:+.8f} "
            f"committed={expected:+.8f} gap={gap:.2e}"
        )
        if gap > 1e-4:
            sys.exit(f"ABORT: G-arch-1 drift too large at r={radius} K={k}")
    print(f"  worst drift {worst:.3e} (recorded; era venv is deleted)")
    print("G-arch-2 same-environment adapted-class equivalence (<= 1e-12)")
    for (radius, k), expected in ANCHOR.items():
        rig_top = float(
            rig1020.PrimeFreeProbe(
                radius=radius,
                basis_size=k,
                grid_size=6001,
                envelope_power=1,
                basis_family="legendre",
            ).solve().eigenvalues[-1]
        )
        res = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=6001,
            envelope_power=1,
            basis_family="legendre",
            include_primes=False,
        ).solve()
        gap = abs(res.top_total - rig_top)
        print(
            f"  r={radius:.3f} K={k:2d} adapted={res.top_total:+.12f} "
            f"rig={rig_top:+.12f} gap={gap:.2e}"
        )
        if gap > 1e-12:
            sys.exit(f"ABORT: G-arch-2 failed at r={radius} K={k}")


def run_sieve_gates() -> None:
    print("G-count hard sieve anchors")
    for a, expected in ((1.0, 5), (2.0, 24)):
        bound = int(math.floor(math.exp(2.0 * a)))
        terms = [
            (q, w)
            for (q, w) in prime_powers_with_weight(bound)
            if math.log(q) < 2.0 * a - 1e-9
        ]
        qs = [q for q, _ in terms]
        print(f"  a={a}: {len(terms)} terms -> {qs}")
        if len(terms) != expected:
            sys.exit(f"ABORT: G-count failed at a={a}")


def run_shift_gates() -> None:
    print("G-sym-t plus/minus shift consistency (5e-6 abs)")
    probe = OrbitGateProbe(radius=2.0, basis_size=12, grid_size=8001)
    functions, _sv, coefficients, _cond, _orth = (
        probe._orthonormal_null_functions()
    )
    probe.coefficients = coefficients
    dimension = functions.shape[0]
    plus = np.zeros((dimension, dimension))
    minus = np.zeros((dimension, dimension))
    for q, weight in probe.prime_terms:
        t = math.log(q)
        plus += (2.0 * weight) * (
            probe.step * (functions @ probe._shifted_functions(t).T)
        )
        minus += (2.0 * weight) * (
            probe.step * (functions @ probe._shifted_functions(-t).T)
        )
    gap = float(np.max(np.abs(plus - minus.T)))
    scale = float(np.max(np.abs(plus)))
    print(f"  |M+ - (M-)^T|max = {gap:.3e} (scale {scale:.3e})")
    if gap > 5e-6:
        sys.exit("ABORT: G-sym-t failed")
    print("G-closed sine closed-form vs analytic-shift (5e-6 abs + order)")
    a_here, k_here = 2.0, 8
    for q in (2, 3):
        t = math.log(q)
        closed = np.array(
            [
                [
                    sine_pair_integral(i + 1, j + 1, t, a_here)
                    for j in range(k_here)
                ]
                for i in range(k_here)
            ]
        )

        def route_for(grid: int) -> np.ndarray:
            probe_g = OrbitGateProbe(
                radius=a_here, basis_size=k_here, grid_size=grid,
                basis_family="sine",
            )
            shifted = probe_g.analytic_basis(probe_g.t + t)
            return probe_g.step * (probe_g.basis @ shifted.T)

        route_fine = route_for(32001)
        route_coarse = route_for(16001)
        gap_fine = float(np.max(np.abs(route_fine - closed)))
        gap_coarse = float(np.max(np.abs(route_coarse - closed)))
        shrink = gap_coarse / max(gap_fine, 1e-300)
        print(
            f"  q={q} basis level: fine diff {gap_fine:.3e}, coarse diff "
            f"{gap_coarse:.3e}, shrink {shrink:.2f}x"
        )
        if gap_fine > 5e-6 or not (3.0 <= shrink <= 6.0):
            sys.exit(f"ABORT: G-closed failed at q={q}")
        fine = OrbitGateProbe(
            radius=a_here, basis_size=k_here, grid_size=32001,
            basis_family="sine",
        )
        functions_f, _svf, coefficients_f, _condf, _orthf = (
            fine._orthonormal_null_functions()
        )
        fine.coefficients = coefficients_f
        route_null = fine.step * (
            functions_f @ fine._shifted_functions(t).T
        )
        closed_null = coefficients_f.T @ closed @ coefficients_f
        gap_null = float(np.max(np.abs(route_null - closed_null)))
        print(f"  q={q} null level: diff {gap_null:.3e}")
        if gap_null > 5e-6:
            sys.exit(f"ABORT: G-closed null level failed at q={q}")


def print_row(row: GateRow) -> None:
    valid = row.resid <= 1e-10 and row.orth <= 1e-10
    status = "ok" if valid else "DISCARDED (row gates)"
    print(
        f"a={row.radius:.2f} {row.family[:3]} K={row.basis_size:2d} "
        f"null={row.nullity:2d} terms={row.n_terms:4d} "
        f"top_total={row.top_total:+.6f} top_arch={row.top_arch:+.6f} "
        f"top_prime={row.top_prime:+.6f} condG={row.cond_g:.2e} "
        f"resid={row.resid:.1e} orth={row.orth:.1e} {status}"
    )


def extrapolate(tops: list[float]) -> float:
    """Geometric-increment extrapolation of a K-rising top sequence."""
    if len(tops) < 3:
        return tops[-1]
    inc1 = tops[-1] - tops[-2]
    inc0 = tops[-2] - tops[-3]
    if inc0 <= 0.0:
        return tops[-1]
    ratio = inc1 / inc0
    if not (0.0 < ratio < 1.0):
        return tops[-1]
    return tops[-1] + inc1 * ratio / (1.0 - ratio)


def main() -> None:
    print("Orbit-window semi-local gate scan (record 1100)")
    print(f"C = log(4*pi) + gamma = {rig1020.C_ARCH:.12f}")
    print(f"positive-direction threshold: {POS_THRESHOLD:.1e}")
    print()
    run_anchor_gates()
    run_sieve_gates()
    run_shift_gates()
    print()
    print("ALL ABORT-CLASS GATES PASSED - scan follows")
    print("-" * 118)

    rows: list[GateRow] = []
    for family, ks in (("legendre", (8, 12, 16, 20, 24, 32)),
                       ("sine", (8, 12, 16, 20))):
        for radius in (1.0, 2.0, 3.0, 4.0):
            if family == "sine" and radius > 2.0:
                continue
            for k in ks:
                row = OrbitGateProbe(
                    radius=radius,
                    basis_size=k,
                    grid_size=8001,
                    envelope_power=1,
                    basis_family=family,
                    include_primes=True,
                ).solve()
                print_row(row)
                if row.resid <= 1e-10 and row.orth <= 1e-10:
                    rows.append(row)
    print("-" * 118)

    verdict_fired = False
    for family in ("legendre", "sine"):
        for radius in (1.0, 2.0, 3.0, 4.0):
            seq = [
                r.top_total
                for r in sorted(
                    (r for r in rows
                     if r.family == family and r.radius == radius),
                    key=lambda r: r.basis_size,
                )
            ]
            if not seq:
                print(
                    f"{family} a={radius}: NO VALID ROWS (unresolved)"
                )
                continue
            limit = extrapolate(seq)
            print(
                f"{family} a={radius}: K-sequence tops "
                f"{['%+.6f' % s for s in seq]} extrapolated {limit:+.6f}"
            )
            if seq[-1] >= POS_THRESHOLD:
                verdict_fired = True

    print()
    any_negative_plateau = True
    for family in ("legendre", "sine"):
        for radius in (1.0, 2.0, 3.0, 4.0):
            seq = [
                r.top_total
                for r in sorted(
                    (r for r in rows
                     if r.family == family and r.radius == radius),
                    key=lambda r: r.basis_size,
                )
            ]
            if len(seq) < 3 or seq[-1] >= 0.0:
                any_negative_plateau = False
    if verdict_fired:
        print(
            "VERDICT: GATE-FAILS-ON-V (matrix observation): a valid row "
            "reaches the positive-direction threshold; the all-of-V sign "
            "theorem is false at that radius (NUMERICAL, law 34)."
        )
    elif any_negative_plateau:
        print(
            "VERDICT: GATE-ALIVE-EVIDENCE: every valid row is negative "
            "with geometric K-increments and negative extrapolation at "
            "every scanned radius (NUMERICAL pricing only; formal closure "
            "needs a certified upper bound, law 34)."
        )
    else:
        print(
            "VERDICT: SPLIT: report the per-radius price table; no route "
            "change."
        )
    print("RH unclaimed; GATE 1 untouched.")


if __name__ == "__main__":
    main()
